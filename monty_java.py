# Python program to generate reasonably efficient Java modular arithmetic code for any prime, on a 32-bit "processor"
# IMPORTANT:- Uses Montgomery representation
# uses unsaturated radix
#
# Java backend derived from monty_rust.py. Same algorithms, same radix logic, same code shape; only the
# code-emission syntax changes. Java has no unsigned types, so the 32-bit word mode is used:
#
#   SPINT  = u32 -> Java int      DPINT  = u64 -> Java long
#   SSPINT = i32 -> Java int      SDPINT = i64 -> Java long
#
# Bit widths match exactly, so wrapping +, -, * and &, |, ^, << are identical. Translation rules used below:
#   (x as DPINT), x an SPINT           -> Integer.toUnsignedLong(x)     (zero extension)
#   (x as SPINT), x a DPINT            -> (int) x                       (truncation)
#   (x as SSPINT), (x as SPINT) i32<->u32 -> no-op (same bits)
#   >> on SPINT/DPINT (unsigned)       -> >>>
#   >> on SSPINT/SDPINT (signed)       -> >>
#   (c[i] as DPINT) in modmul/modsqr   -> long locals c0..,b0.. loaded once at entry (zero-extended),
#                                         which also makes modmul(b,c) alias-safe for b==c
#   (p_i as DPINT), p_i a positive SPINT constant -> long constant p_i
#   u8 <-> SPINT                       -> (byte) x / (b[i] & 0xff)
#   Option<&[SPINT]>                   -> int[] or null
# No unsigned division or comparison is emitted.
#
# In particular this script generates code for the NIST primes
#
# NIST256 = 2^256-2^224+2^192+2^96-1
# NIST384 = 2^384-2^128-2^96+2^32-1
#
# and the "Goldilocks" prime
#
# X448=2^448-2^224-1
#
# uses addchain utility if in the path - see https://github.com/mmcloughlin/addchain
# if not found, a pure-Python sliding-window addition chain is used instead (same ac.txt format)
#
# How to use.
# (1) First execute this program: python3 monty_java.py 32 NIST256. Output code is written to file FieldNIST256.java
# (2) All constants and inputs must be converted to Montgomery nresidue form by calling nres()
# (3) All final outputs must be converted back to integer form by calling redc()
#
# The modulus can either be entered directly, or derived from the hard-wired name of an elliptic curve
# Normally this will be the field prime modulus
# However if the modulus is entered in decimal with two leading 0s, it is instead assumed to be a group
# order (a large prime factor of the number of points on a curve)
#
# Note that even though a modulus is represented to the base 2^29 rather than 2^32, it still retains some shape
# For example on a 32-bit processor using a radix of 2^29 the NIST384 prime is
# {0x1FFFFFFF,0x7,0x0,0x1FFFFE00,0x1FFFEFFF,0x1FFFFFFF,0x1FFFFFFF,0x1FFFFFFF,0x1FFFFFFF,0x1FFFFFFF,0x1FFFFFFF,0x1FFFFFFF,0x1FFFFFFF,0x7F}
# which can also be represented as
# {0x1FFFFFFF,0x7,0x0,0x1FFFFE00,0x1FFFEFFF,      -0x1,       0x0,       0x0,       0x0,       0x0,       0x0,       0x0,       0x0,0x80}
#
# and now the majority of the multiplications in the Montgomery reduction are by 0, and can be eliminated.
#
# Mike Scott 22nd April 2024
# TII
#

# Some default settings

karatsuba=False # default setting (Karatsuba variant not supported by the Java backend)
makepublic=False # True: modarith API public static; False: package-private static (prop/flatten stay private)
PSCR=False # Power Side Channel Resistant conditional moves and swaps. Not emitted for Java: no volatile local
           # writes, and the Rust version keeps a static mutable seed, which would break statelessness
MAXSMALL=65535 # largest multiplier accepted by mulSmall()/modmli() in the ModArithField wrapper

import sys
import subprocess
import os
import shutil

PACKAGE="de.rub.nds.protocol.crypto.ec.modarith"
LICENSE="""/*
 * Protocol-Attacker - A Framework to create Protocol Analysis Tools
 *
 * Copyright 2023-2023 Ruhr University Bochum, Paderborn University, Technology Innovation Institute, and Hackmanit GmbH
 *
 * Licensed under Apache License, Version 2.0
 * http://www.apache.org/licenses/LICENSE-2.0.txt
 */"""

# (x as DPINT) for an SPINT x
def U(x) :
    return "Integer.toUnsignedLong({})".format(x)

# workaround for addchain bug
def remove_unused() :
    # get all tokens
    fin = open("inv.acc")
    words = fin.read().split()
    fin.close()
    #print(words)
    found=False

    #strip out some stuff
    for i in range(0,len(words)) :
        words[i]=words[i].replace('2*','')
        for char in words[i] :
            if char in "()":
                words[i]=words[i].replace(char,'')
    #print(words)

    #remove operators
    while ("=" in words) :
        words.remove("=")
    while ("+" in words) :
        words.remove("+")
    while ("<<" in words) :
        words.remove("<<")
    while ("return" in words) :
        words.remove("return")
    #print(words)

    #remove numbers
    i=0
    while (True) :
        if words[i].isdigit() :
            words.remove(words[i])
        else :
            i+=1
        if i>=len(words) :
            break

    #print(words)

    #only variables left?
    #find those that occur only once
    unused=[]
    for i in range(0,len(words)) :
        var=words[i]
        times=words.count(var)
        if words.count(var) == 1 :
            found=True
            unused.append(var)

    #print(unused)

    #remove them
    fin = open("inv.acc","rt")
    fout = open("myinv.acc","wt")
    for line in fin :
        index=line.index(' ')
        subs=line[0:index]
        dont=False
        for i in range(0,len(unused)) :
            if subs==unused[i] :
                dont=True;
        if dont :
            continue
        fout.write(line)
    fin.close()
    fout.close()

    os.remove("inv.acc")
    os.rename("myinv.acc","inv.acc")

    return found

# Pure-Python fallback when addchain is not installed: sliding-window addition chain for x^e,
# written in the format of "addchain gen" (first line "tmp t0 t1 ...", then double/add/shift lines,
# input x, output z). Inversion runs once per scalar multiplication, so optimality is not critical.
def fallback_chain(e, fname) :
    w=5
    if e.bit_length()<64 :
        w=3
    lines=[]
    # odd powers x^1 (named x), x^3, x^5, ... x^(2^w-1) in t1,t2,...; t0 = x^2
    names={1:"x"}
    tmps=["t0"]
    lines.append("double t0 x")
    prev="x"
    for d in range(3,2**w,2) :
        nm="t{}".format(len(tmps))
        tmps.append(nm)
        lines.append("add {} {} t0".format(nm,prev))
        names[d]=nm
        prev=nm
    # scan exponent left to right
    bitsl=[int(c) for c in bin(e)[2:]]
    i=0
    acc=None      # name holding the running value (None until first window)
    pend=0        # pending squarings
    L=len(bitsl)
    while i<L :
        if bitsl[i]==0 :
            pend+=1
            i+=1
            continue
        # window: longest run bits[i..j] with j-i+1<=w ending in a 1
        j=min(i+w-1,L-1)
        while bitsl[j]==0 :
            j-=1
        d=0
        for k in range(i,j+1) :
            d=2*d+bitsl[k]
        wl=j-i+1
        if acc is None :
            acc=names[d]
            pend=0
        else :
            pend+=wl
            lines.append("shift z {} {}".format(acc,pend))
            lines.append("add z z {}".format(names[d]))
            acc="z"
            pend=0
        i=j+1
    if acc!="z" :
        lines.append("shift z {} {}".format(acc,pend))
    elif pend>0 :
        lines.append("shift z z {}".format(pend))
    f=open(fname,"wt")
    f.write("tmp\t"+"\t".join(tmps)+"\n")
    for l in lines :
        f.write("\t".join(l.split())+"\n")
    f.close()

# check an ac.txt chain computes x^e (exponent arithmetic only)
def check_chain(e, fname) :
    f=open(fname)
    lines=f.readlines()
    f.close()
    v={"x":1,"z":0}
    for t in lines[0].split()[1:] :
        v[t]=0
    for i in range(1,len(lines)) :
        info=lines[i].split()
        if info[0]=="double" :
            v[info[1]]=2*v[info[2]]
        if info[0]=="add" :
            v[info[1]]=v[info[2]]+v[info[3]]
        if info[0]=="shift" :
            v[info[1]]=v[info[2]]<<int(info[3])
    return v["z"]==e

def ispowerof2(n) :
    if (n & (n-1) == 0) and n>0 :
        e=0
        while n>0 :
            if (n&1)!=0 :
                return e
            e=e+1
            n>>=1
    return -1

# Determine default optimal radix
def getbase(n) :
    limbs=int(n/WL)
    min_excess=4  # for fast modadd/modsub inputs to modmul could be 4px4p < pR, so 16p<R, so 4 extra bits needed
    while (True) :
        limbs=limbs+1
        if limbs==1 :   # must be at least 2 limbs
            limbs=2
        base=int(WL/2)
        while limbs*base<n or base-(n%base)<min_excess :  # insist on excess of 4 or more
            base=base+1
        if n%base==0 :
            _,E,_=process_prime(p,base,limbs)      # if excess=0, and if no extra limb required, bump base
            if not E :
                base=base+1
        while limbs*base<n or base-(n%base)<min_excess :  # insist on excess of 4 or more
            base=base+1
        if base>WL-3 :    # OK, base too large, another limb required
            continue
        if limbs*(2**base-1)**2 < 2**limit :   # worst case scenario for non-shaped primes
            break
        _,_,npp=process_prime(p,base,limbs) # npp=max number of extra partial products in longest diagonal
        npp+=limbs+1
        if npp*(2**base-1)**2 < 2**limit :   # Sufficient condition to avoid overflow in multiplication
            break
    return base

# get number of limbs
def getN(n,base) :
    N=int(n/base)
    if n%base!=0 :
        N=N+1
    return N

def bits(n) :
    b=0
    m=n
    while m!=0 :
        b+=1
        m>>=1
    return b

# gcd
def gcd(x, y):
    a = x
    b = y
    while b != 0:
        a, b = b, a % b
    return a

# inverse mod prime p
def inverse(a, p) :
    n = p
    x = a % n
    if x == 0:
        return x
    kn = n
    if x < 0:
        x += n
    if gcd(x, n) != 1:
        return 0
    a = 1
    la = 0
    while x > 1:
        q, r = divmod(n, x)
        t = la - a * q
        la = a
        a = t
        n = x
        x = r
    if a < 0:
        a += kn
    return a

# get Montgomery R
def getR(n,base) :
    m=int(n/base)
    if n%base!=0 :
        m+=1
    R=2**(m*base)
    return R

# is it a lucky trinomial?
def trinomial(p,base) :
    n=p.bit_length()
    m=2**n - p
    m = m-1
    k=20
    while k < n :
        if 2**k > m :
            return 0
        if 2**k == m: break
        k=k+1
    if k%base == 0 :
        return k//base
    return 0

# convert to radix array
def makebig(p,base,N) :
    pw=[]
    i=0
    b=2**base
    tp=p
    while i<N :
        pw.append(tp%b)
        tp=tp>>base
        i=i+1
    return pw

# process the modulus given radix and number of limbs
def process_prime(p,base,N) :
    b=2**base
    pw=makebig(p,base,N)

# Here pw is further processed to convert 2^base-1 values to -1, and carry +1 to the next digit
# generated code must be modified to process a -1 multiplier in the reduction function
# observe that for NIST primes this will increase the number of 0 entries

# ppw contains processed modulus
    ppw=[]
    for i in range(0,N) :
        ppw.append(0)

    carry=0
    i=0
    while i<N :
        if carry==1 :
            ppw[i]=pw[i]+carry
            if ppw[i] == b-1 :
                ppw[i]=-1
            else :
                carry=0
                if ppw[i]==b :
                    ppw[i]=0
                    carry=1
        else :
            ppw[i]=pw[i]
            if PM and i==0 :
                if pw[i] == b-m :
                    ppw[i]=-m
                    carry=1
            else :
                if pw[i] == b-1 :
                    ppw[i]=-1
                    carry=1
        i=i+1
    E=False
    if carry==1 :
        E=True
        ppw.append(carry)

# count number of extra large partial products required
    npp=0
    for i in range(0,len(ppw)) :
        if ppw[i]==1 or ppw[i]==-1 or ppw[i]==0 :
            continue
        npp+=1

    return ppw,E,npp

# Java integer literal for an SPINT constant 0<=x<2^32
def H(x) :
    assert 0<=x<2**32
    return "0x{:x}".format(x)

#conditional add of p
def caddp(x) :
    str=""
    for i in range(0,N) :
        if ppw[i]==0 :
            continue
        if ppw[i]==-1:
            str+="\t\tn[{}]-={}&carry;\n".format(i,x)
            continue
        if ppw[i]<0:
            str+="\t\tn[{}]-={}&carry;\n".format(i,H(-ppw[i]*x))
            continue
        str+="\t\tn[{}]+={}&carry;\n".format(i,H(ppw[i]*x))
    if E:
        str+="\t\tn[{}]+=({}*q)&carry;\n".format(N-1,x)
    return str

#add p
def addp(x) :
    str=""
    for i in range(0,N) :
        if ppw[i]==0 :
            continue
        if ppw[i]==-1:
            str+="\t\tn[{}]-={};\n".format(i,x)
            continue
        if ppw[i]<0:
            str+="\t\tn[{}]-={};\n".format(i,H(-ppw[i]*x))
            continue
        str+="\t\tn[{}]+={};\n".format(i,H(ppw[i]*x))
    if E:
        str+="\t\tn[{}]+={}*q;\n".format(N-1,x)
    return str


#subtract p
def subp(x) :
    str=""
    for i in range(0,N) :
        if ppw[i]==0 :
            continue
        if ppw[i]==-1:
            str+="\t\tn[{}]+={};\n".format(i,x)
            continue
        if ppw[i]<0:
            str+="\t\tn[{}]+={};\n".format(i,H(-ppw[i]*x))
            continue
        str+="\t\tn[{}]-={};\n".format(i,H(ppw[i]*x))
    if E:
        str+="\t\tn[{}]-={}*q;\n".format(N-1,x)
    return str

def pub() :
    if makepublic :
        return "public static "
    return "static "

#propagate carries
def prop(n,base) :
    str="\t// propagate carries\n"
    str+="\tprivate static int prop(int[] n) {\n"
    str+="\t\tint mask=(1<<{})-1;\n".format(base)
    str+="\t\tint carry=n[0]>>{};\n".format(base)
    str+="\t\tn[0]&=mask;\n"
    str+="\t\tfor (int i=1;i<{};i++) {{\n".format(N-1)
    str+="\t\t\tcarry+=n[i];\n"
    str+="\t\t\tn[i]=carry&mask;\n"
    str+="\t\t\tcarry>>={};\n".format(base)
    str+="\t\t}\n"
    str+="\t\tn[{}]+=carry;\n".format(N-1)
    str+="\t\treturn n[{}]>>{};\n\t}}\n".format(N-1,WL-1)
    return str

#propagate carries and add p if negative, propagate carries again
def flat(n,base) :
    mask=(1<<base)-1
    str="\t// propagate carries and add p if negative, propagate carries again\n"
    str+="\tprivate static int flatten(int[] n) {\n"
    str+="\t\tint q=1<<{};\n".format(base)
    str+="\t\tint carry=prop(n);\n"
    str+=caddp(1)
    str+="\t\tprop(n);\n"
    str+="\t\treturn carry&1;\n\t}\n"
    return str

#final subtract
def modfsb(n,base) :
    str="\t// Montgomery final subtract\n"
    str+="\t"+pub()+"int modfsb(int[] n) {\n"
    str+="\t\tint q=1<<{};\n".format(base)
    str+=subp(1)
    str+="\t\treturn flatten(n);\n\t}\n"
    return str

#modular addition
def modadd(n,base) :
    str="\t// Modular addition - can be used in all cases - reduce less than 2p\n"
    str+="\t"+pub()+"void modadd(int[] b,int[] n) {\n"

    if E:
        str+="\t\tint q=1<<{};\n".format(base)
    for i in range(0,N) :
        str+="\t\tn[{}]=n[{}]+b[{}];\n".format(i,i,i)

    str+=subp(2)
    str+="\t\tint carry=prop(n);\n"
    str+=caddp(2)
    str+="\t\tprop(n);\n"
    str+="\t}\n"
    return str

#fast modular addition
def modaddf(n,base) :
    str="\t// Fast modular addition - can be used if output is consumed ONLY by multiplication or squaring\n"
    str+="\t"+pub()+"void modaddf(int[] b,int[] n) {\n"

    if E:
        str+="\t\tint q=1<<{};\n".format(base)
    for i in range(0,N) :
        str+="\t\tn[{}]=n[{}]+b[{}];\n".format(i,i,i)

    if not veryfastadd :
        str+="\t\tprop(n);\n"
    str+="\t}\n"
    return str

#modular subtraction
def modsub(n,base) :
    str="\t// Modular subtraction - can be used in all cases - reduce less than 2p\n"
    str+="\t"+pub()+"void modsub(int[] b,int[] n) {\n"

    if E:
        str+="\t\tint q=1<<{};\n".format(base)

    for i in range(0,N) :
        str+="\t\tn[{}]=n[{}]-b[{}];\n".format(i,i,i)

    str+="\t\tint carry=prop(n);\n"
    str+=caddp(2)

    str+="\t\tprop(n);\n"
    str+="\t}\n"
    return str

#fast modular subtraction
def modsubf(n,base) :
    str="\t// Fast modular subtraction - can be used if output is ONLY consumed by multiplication or squaring\n"
    str+="\t"+pub()+"void modsubf(int[] b,int[] n) {\n"

    if E:
        str+="\t\tint q=1<<{};\n".format(base)

    for i in range(0,N) :
        str+="\t\tn[{}]=n[{}]-b[{}];\n".format(i,i,i)

    str+=addp(2)

    str+="\t\tprop(n);\n"
    str+="\t}\n"
    return str

#modular negation
def modneg(n,base) :
    str="\t// Modular negation\n"
    str+="\t"+pub()+"void modneg(int[] n) {\n"

    if E:
        str+="\t\tint q=1<<{};\n".format(base)

    for i in range(0,N) :
        str+="\t\tn[{}]=0-n[{}];\n".format(i,i)

    str+="\t\tint carry=prop(n);\n"
    str+=caddp(2)

    str+="\t\tprop(n);\n"
    str+="\t}\n"
    return str

# add column of partial products from multiplication on way up
# c[k] and b[k] (as DPINT) are the long locals c{k} and b{k}
def getZMU(str,i) :
    first=True
    global maxnum

    k=0
    while (k<=i) :
        if first :
            str+="\t\tt+=c{}*b{};".format(k,i-k)
            first=False
        else :
            str+=" t+=c{}*b{};".format(k,i-k)
        k+=1
        maxnum+=maxdigit*maxdigit
    return str

# add column of partial products from multiplication on way down
def getZMD(str,i) :

    first=True
    k=i-(N-1)
    while (k<=N-1) :
        if first :
            first=False
            str+="\t\tt+=c{}*b{};".format(k,i-k)
        else :
            str+=" t+=c{}*b{};".format(k,i-k)
        k+=1
    return str

# add column of partial products from squaring on way up
def getZSU(str,i) :
    first=True
    k=0
    j=i
    hap=False
    while k<j :
        hap=True
        if first :
            str+="\t\ttot=c{}*c{};".format(k,i-k)
            first=False
        else :
            str+=" tot+=c{}*c{};".format(k,i-k)
        k+=1
        j-=1
    if hap:
        str+=" tot*=2;"
    if i%2==0:
        if first :
            str+="\t\ttot=c{}*c{};".format(int(i/2),int(i/2))
        else :
            str+=" tot+=c{}*c{};".format(int(i/2),int(i/2))
    if i==0 :
        str+=" t=tot;"
    else :
        str+=" t+=tot;"
    return str

# add column of partial products from squaring on way down
def getZSD(str,i) :
    first=True
    k=i-(N-1)
    j=N
    hap=False
    while k<i-k :
        hap=True
        if first :
            str+="\t\ttot=c{}*c{};".format(k,i-k)
            first=False
        else :
            str+=" tot+=c{}*c{};".format(k,i-k)
        k+=1
        j-=1
    if hap :
        str+=" tot*=2;"
    if i%2==0:
        if first :
            str+="\t\ttot=c{}*c{};".format(int(i/2),int(i/2))
        else :
            str+=" tot+=c{}*c{};".format(int(i/2),int(i/2))
    str+=" t+=tot;"
    return str

# process ppw[i] element, where i is index of the prime p, j is index of v
# do a double-shift instead of a multiply if possible
# Add in q for appearance of negative v (maybe need to add in q again for such every appearance?)
# try to accumulate contributions in single-precision if possible

def mul_process(i,j,str,gone_neg,mask_set) :
    global maxnum
    n=ppw[i]   # do nothing if n=0
    if abs(n)>1 :
        e=ispowerof2(n)
        if e > 0  :
            str+=" t+={}<<{};".format(U("v{}".format(j)),e)
            maxnum+=maxdigit*2**e
        else :
            str+=" t+={}*p{};".format(U("v{}".format(j)),i)
            maxnum+=maxdigit*ppw[i]
    if n == 1 :
        if mask_set :
            str+=" s+=v{};".format(j)
        else :
            str+=" t+={};".format(U("v{}".format(j)))
            maxnum+=maxdigit
    if n == -1 :
        if mask_set :
            if not gone_neg :
                str+=" s+=q-v{};".format(j)
            else :
                str+=" s-=v{};".format(j)
        else:
            if not gone_neg :
                str+=" t+={};".format(U("q-v{}".format(j)))
                maxnum+=maxdigit
            else :
                str+=" t-={};".format(U("v{}".format(j)))
        gone_neg=True
    return str,gone_neg

def sqr_process(i,j,str,gone_neg,mask_set) :
    global maxnum
    n=ppw[i]   # do nothing if n=0
    if abs(n)>1 :
        e=ispowerof2(n)
        if e > 0  :
            str+=" t+={}<<{};".format(U("v{}".format(j)),e)
            maxnum+=maxdigit*2**e
        else :
            str+=" t+={}*p{};".format(U("v{}".format(j)),i)
            maxnum+=maxdigit*ppw[i]
    if n == 1 :
        if mask_set :
            str+=" s+=v{};".format(j)
        else :
            str+=" t+={};".format(U("v{}".format(j)))
            maxnum+=maxdigit
    if n == -1 :
        if mask_set :
            if not gone_neg :
                str+=" s+=q-v{};".format(j)
            else :
                str+=" s-=v{};".format(j)
        else:
            if not gone_neg :
                str+=" t+={};".format(U("q-v{}".format(j)))
                maxnum+=maxdigit
            else :
                str+=" t-={};".format(U("v{}".format(j)))
        gone_neg=True
    return str,gone_neg


def modmli(n,base) :
    N=getN(n,base)
    mask=(1<<base)-1
    xcess=N*base-n
    str="\t// Modular multiplication by an integer, c=c*b mod 2p\n"
    str+="\t"+pub()+"void modmli(int b,int[] c) {\n"
    if trin>0 :
        str+="\t\tlong t=0;\n"
        str+="\t\tint mask=(1<<{})-1;\n".format(base)

        for i in range(0,N) :
            str+="\t\tt+={}*{}; ".format(U("c[{}]".format(i)),U("b"))
            str+="c[{}]=(int)t&mask; t=t>>>{};\n".format(i,base)

        str+="\t\t// reduction pass\n\n"
        str+="\t\tint s=(int)t;\n"

        if xcess>0 :
            smask=(1<<(base-xcess))-1
            str+= "\t\ts=(s<<{})+(c[{}]>>>{}); c[{}]&={};\n".format(xcess,N-1,base-xcess,N-1,H(smask))

        str+="\t\tc[0]+=s;\n"
        str+="\t\tc[{}]+=s;\n".format(trin)
    else :

# Barrett/Dhem method
        # h=t>>((n-WL)%base) must be the top n+base-WL bits of the product, as assumed by r below
        assert base*(N-1)+(n-WL)%base==n+base-WL
        for i in range(0,N) :
            d=ppw[i]
            if abs(d)>1 :
                if d>1 :
                    if i==0 or ispowerof2(d)<0 :
                        str+="\t\tint p{}={};\n".format(i,H(d))
                if d<1 :
                    if i==0 :
                        str+="\t\tint p{}={};\n".format(i,H(-d))

        str+="\t\tint mask=(1<<{})-1;\n".format(base)
        str+="\t\tlong t=0;\n"
        str+="\t\tint r={};\n".format(H((2**(n+base))//p))
        for i in range(0,N-1) :
            str+="\t\tt+={}*{}; ".format(U("c[{}]".format(i)),U("b"))
            str+="c[{}]=(int)t&mask; t=t>>>{};\n".format(i,base)
        str+="\t\tt+={}*{}; ".format(U("c[{}]".format(N-1)),U("b"))
        str+="c[{}]=(int)t;\n".format(N-1)
        str+="\n\t\t// Barrett-Dhem reduction\n"
        str+="\t\tint h=(int)(t>>>{});\n".format((n-WL)%base)
        str+="\t\tint q=(int)(({}*{})>>>{});\n".format(U("h"),U("r"),WL)

        for i in range(0,N) :
            d=ppw[i]
            if d==0 :
                continue
            if d==-1 :
                str+="\t\tc[{}]+=q;\n".format(i)
                continue
            if d==1 :
                str+="\t\tc[{}]-=q;\n".format(i)
                continue
            e=ispowerof2(d)
            if e>0 :
                if i<N-1 :
                    str+="\t\tt={}<<{}; c[{}]-=(int)t&mask; c[{}]-=(int)(t>>>{});\n".format(U("q"),e,i,i+1,base)
                else :
                    str+="\t\tc[{}]-=q<<{};\n".format(i,e)
            else :
                if d<0 :
                    str+="\t\tt={}*{}; c[{}]+=(int)t&mask; c[{}]+=(int)(t>>>{});\n".format(U("q"),U("p{}".format(i)),i,i+1,base)
                else :
                    if i<N-1 :
                        str+="\t\tt={}*{}; c[{}]-=(int)t&mask; c[{}]-=(int)(t>>>{});\n".format(U("q"),U("p{}".format(i)),i,i+1,base)
                    else :
                        str+="\t\tc[{}]-=q*p{};\n".format(i,i)
        if E:
            str+="\t\tc[{}]-=q<<{};\n".format(N-1,base)
        str+="\t\tprop(c);\n"
    str+="\t}\n"
    return str

# modular multiplication, modulo p. Exploits 0 digits in p.
def modmul(n,base) :
    global maxnum
    mask=(1<<base)-1

    str="\t// Modular multiplication, c=c*b mod 2p\n"
    str+="\t"+pub()+"void modmul(int[] b,int[] c) {\n"

    str+="\t\tlong t=0;\n"
    str+="\t\tint s;\n"
    for i in range(0,N) :
        str+="\t\tlong c{}={}, b{}={};\n".format(i,U("c[{}]".format(i)),i,U("b[{}]".format(i)))

    for i in range(0,N) :
        if i==0 and PM :
            continue
        n=ppw[i]
        if abs(n)>1 :
            if i==0 or ispowerof2(n)<0 :
                assert n>0
                str+="\t\tlong p{}={}L;\n".format(i,H(ppw[i]))
    str+="\t\tint q=1<<{}; // q is unsaturated radix\n".format(base)
    str+="\t\tint mask=q-1;\n"
    if fullmonty :
        str+="\t\tint ndash={};\n".format(H(ndash))
    maxnum=0
    str=getZMU(str,0)
    gone_neg=False

    if fullmonty :
        str+=" int v0=((int)t*ndash)&mask;"
        if PM :
            gone_neg=True
            str+=" t+={};".format(U("{}*(q-v0)".format(M)))
            maxnum+=M*maxdigit
        else :
            if ppw[0]==1 :
                str+=" t+={};".format(U("v0"))
            else :
                str+=" t+={}*p0;".format(U("v0"))
            maxnum+=ppw[0]*maxdigit
    else :
        str+=" int v0=(int)t&mask;"
    str+=" t>>>={};\n".format(base)
    maxnum=2**(2*WL-base)
    str=getZMU(str,1)
    mask_set=False

    for i in range(1,N) :
        if gone_neg :
            if PM :
                str+=" t+={};".format(U("{}*mask".format(M)))
                maxnum+=M*maxdigit
            else :
                str+=" s=mask;"
                mask_set=True
                #str+=" t+=mask;"
        k=1
        str,gone_neg=mul_process(i,0,str,gone_neg,mask_set)
        while k<i :
            str,gone_neg=mul_process(i-k,k,str,gone_neg,mask_set)
            k+=1
        if mask_set :
            str+=" t+={};".format(U("s"))
            maxnum+=maxdigit
            mask_set=False

        if fullmonty :
            str+=" int v{}=((int)t*ndash)&mask;".format(i)
            if PM :
                str+=" t-={};".format(U("{}*v{}".format(M,i)))
            else :
                if ppw[0]==1 :
                    str+=" t+={};".format(U("v{}".format(i)))
                else :
                    str+=" t+={}*p0;".format(U("v{}".format(i)))
                maxnum+=ppw[0]*maxdigit
        else :
            str+=" int v{}=(int)t&mask;".format(i)
        if i==N-1 :
            print("// Overflow limit   =",2**(2*WL))
            print("// maximum possible =",maxnum)
            if maxnum >= 2**(2*WL) :
                print("//Warning: Overflow possibility detected - change radix ")
                overflow_warnings.append("modmul")
        str+=" t>>>={};\n".format(base)
        maxnum=2**(2*WL-base)
        if i<N-1 :
            str= getZMU(str,i+1)

    str=getZMD(str,N)
    if gone_neg :
        if PM :
            str+=" t+={};".format(U("{}*mask".format(M)))
        else :
            str+=" s=mask;"
            mask_set=True
            #str+=" t+=mask;"

    if E :
        k=0
        while k<N :
            str,gone_neg=mul_process(N-k,k,str,gone_neg,mask_set)
            k+=1
        if mask_set :
            str+=" t+={};".format(U("s"))
            mask_set=False

        if fullmonty :
            str+=" int v{}=((int)t*ndash)&mask;".format(N)
            if PM :
                str+=" t-={};".format(U("{}*v{}".format(M,N)))
            else :
                if ppw[0]==1 :
                    str+=" t+={};".format(U("v{}".format(N)))
                else :
                    str+=" t+={}*p0;".format(U("v{}".format(N)))
        else :
            str+=" int v{}=(int)t&mask;".format(N)
        str+=" t>>>={};\n".format(base)

        str=getZMD(str,N+1)

        for i in range(N+1,2*N) :
            if gone_neg :
                if PM :
                    str+=" t+={};".format(U("{}*mask".format(M)))
                else :
                    str+=" s=mask;"
                    mask_set=True
            k=i-N
            while k<=N :
                str,gone_neg=mul_process(i-k,k,str,gone_neg,mask_set)
                k+=1
            if mask_set :
                str+=" t+={};".format(U("s"))
                mask_set=False

            str+=" c[{}]=(int)t&mask;".format(i-N-1)
            str+=" t>>>={};\n".format(base)

            #if i<=2*N-1 :
            if i<2*N-2 :
                str=getZMD(str,i+1)
            else :
                str+="\t\t"

        if gone_neg :
            if PM :
                str+=" t+={};".format(U("v{}-{}".format(N,M)))
            else :
                str+=" t+={};".format(U("v{}-1".format(N)))
        else :
            str+=" t+={};".format(U("v{}".format(N)))

        str+=" c[{}]=(int)t;\n".format(N-1)
    else :
        for i in range(N,2*N-1) :
            k=i-(N-1)
            while k<=N-1 :
                str,gone_neg=mul_process(i-k,k,str,gone_neg,mask_set)
                k+=1
            if mask_set :
                str+=" t+={};".format(U("s"))
                mask_set=False

            if i==2*N-1 :
                break
            str+=" c[{}]=(int)t&mask;".format(i-N)
            str+=" t>>>={};\n".format(base)
            if i<=2*N-3 :
                str=getZMD(str,i+1)
                if gone_neg :
                    if PM :
                        str+=" t+={};".format(U("{}*mask".format(M)))
                    else :
                        str+=" s=mask;"
                        mask_set=True
        if gone_neg :
            if PM :
                str+="\t\tt-={};".format(M)
            else :
                str+="\t\tt-=1;"
        str+="\t\tc[{}]=(int)t;\n".format(N-1)
    str+="\t}\n"
    return str

# modular squaring
def modsqr(n,base) :
    mask=(1<<base)-1

    str="\t// Modular squaring, c=a*a  mod 2p\n"
    str+="\t"+pub()+"void modsqr(int[] c) {\n"

    str+="\t\tlong t;\n"
    str+="\t\tlong tot;\n"
    str+="\t\tint s;\n"
    for i in range(0,N) :
        str+="\t\tlong c{}={};\n".format(i,U("c[{}]".format(i)))
    for i in range(0,N) :
        if i==0 and PM :
            continue
        n=ppw[i]
        if abs(n)>1 :
            if i==0 or ispowerof2(n)<0 :
                assert n>0
                str+="\t\tlong p{}={}L;\n".format(i,H(ppw[i]))
    str+="\t\tint q=1<<{}; // q is unsaturated radix\n".format(base)
    str+="\t\tint mask=q-1;\n"
    if fullmonty :
        str+="\t\tint ndash={};\n".format(H(ndash))
    str=getZSU(str,0)
    gone_neg=False

    if fullmonty :
        str+=" int v0=((int)t*ndash)&mask;"
        if PM :
            gone_neg=True
            str+=" t+={};".format(U("{}*(q-v0)".format(M)))
        else :
            if ppw[0]==1 :
                str+=" t+={};".format(U("v0"))
            else :
                str+=" t+={}*p0;".format(U("v0"))

    else :
        str+=" int v0=(int)t&mask;"
    str+=" t>>>={};\n".format(base)

    str=getZSU(str,1)
    mask_set=False

    for i in range(1,N) :
        if gone_neg :
            if PM :
                str+=" t+={};".format(U("{}*mask".format(M)))
            else :
                str+=" s=mask;"
                mask_set=True

        k=1
        str,gone_neg=sqr_process(i,0,str,gone_neg,mask_set)
        while k<i :
            str,gone_neg=sqr_process(i-k,k,str,gone_neg,mask_set)
            k+=1
        if mask_set :
            str+=" t+={};".format(U("s"))
            mask_set=False

        if fullmonty :
            str+=" int v{}=((int)t*ndash)&mask;".format(i)
            if PM :
                str+=" t-={};".format(U("{}*v{}".format(M,i)))
            else :
                if ppw[0]==1 :
                    str+=" t+={};".format(U("v{}".format(i)))
                else :
                    str+=" t+={}*p0;".format(U("v{}".format(i)))
        else :
            str+=" int v{}=(int)t&mask;".format(i)
        str+=" t>>>={};\n".format(base)
        if i<N-1 :
            str= getZSU(str,i+1)

    str=getZSD(str,N)
    if gone_neg :
        if PM :
            str+=" t+={};".format(U("{}*mask".format(M)))
        else :
            str+=" s=mask;"
            mask_set=True

    if E :
        k=0
        while k<N :
            str,gone_neg=sqr_process(N-k,k,str,gone_neg,mask_set)
            k+=1
        if mask_set :
            str+=" t+={};".format(U("s"))
            mask_set=False
        if fullmonty :
            str+=" int v{}=((int)t*ndash)&mask;".format(N)
            if PM :
                str+=" t-={};".format(U("{}*v{}".format(M,N)))
            else :
                if ppw[0]==1 :
                    str+=" t+={};".format(U("v{}".format(N)))
                else :
                    str+=" t+={}*p0;".format(U("v{}".format(N)))
        else :
            str+=" int v{}=(int)t&mask;".format(N)
        str+=" t>>>={};\n".format(base)

        str=getZSD(str,N+1)
        for i in range(N+1,2*N) :
            if gone_neg :
                if PM :
                    str+=" t+={};".format(U("{}*mask".format(M)))
                else :
                    str+= " s=mask;"
                    mask_set=True
                    #str+=" t+=mask;"
            k=i-N
            while k<=N :
                str,gone_neg=sqr_process(i-k,k,str,gone_neg,mask_set)
                k+=1
            if mask_set :
                str+=" t+={};".format(U("s"))
                mask_set=False
            str+=" c[{}]=(int)t&mask;".format(i-N-1)
            str+=" t>>>={};\n".format(base)

            #if i<=2*N-1 :
            if i<2*N-2 :
                str=getZSD(str,i+1)
            else :
                str+="\t\t"

        if gone_neg :
            if PM :
                str+=" t+={};".format(U("v{}-{}".format(N,M)))
            else :
                str+=" t+={};".format(U("v{}-1".format(N)))
        else :
            str+=" t+={};".format(U("v{}".format(N)))
        str+=" c[{}]=(int)t;\n".format(N-1)
    else :
        for i in range(N,2*N-1) :
            k=i-(N-1)
            while k<=N-1 :
                str,gone_neg=sqr_process(i-k,k,str,gone_neg,mask_set)
                k+=1
            if mask_set :
                str+=" t+={};".format(U("s"))
                mask_set=False
            if i==2*N-1 :
                break
            str+=" c[{}]=(int)t&mask;".format(i-N)
            str+=" t>>>={};\n".format(base)
            if i<=2*N-3 :
                str=getZSD(str,i+1)
                if gone_neg :
                    if PM :
                        str+=" t+={};".format(U("{}*mask".format(M)))
                    else :
                        str+= " s=mask;"
                        mask_set=True
        if gone_neg :
            if PM :
                str+="\t\tt-={};".format(M)
            else :
                str+="\t\tt-=1;"
        str+="\t\tc[{}]=(int)t;\n".format(N-1)
    str+="\t}\n"
    return str

def modcpy() :
    str="\t// copy\n"
    str+="\t"+pub()+"void modcpy(int[] a,int[] c) {\n"
    str+="\t\tfor (int i=0;i<{};i++) {{\n".format(N)
    str+="\t\t\tc[i]=a[i];\n"
    str+="\t\t}\n"
    str+="\t}\n"
    return str

def modnsqr() :
    str="\t// square n times\n"
    str+="\t"+pub()+"void modnsqr(int[] a,int n) {\n"
    str+="\t\tfor (int i=0;i<n;i++) {\n"
    str+="\t\t\tmodsqr(a);\n"
    str+="\t\t}\n"
    str+="\t}\n"
    return str

# uses https://github.com/mmcloughlin/addchain to create addition chain
def modpro() :
    f=open('ac.txt')
    lines=f.readlines()
    info=lines[0].split()
    ntmps=len(info)-1
    str="\t// Calculate progenitor\n"
    str+="\t"+pub()+"void modpro(int[] w,int[] r) {\n"
    str+="\t\tint[] x=new int[{}];\n".format(N)
    str+="\t\tint[] z=new int[{}];\n".format(N)
    for i in range(0,ntmps) :
        str+="\t\tint[] {}=new int[{}];\n".format(info[i+1],N)
    str+="\t\tmodcpy(w,x);\n"
    for i in range(1,len(lines)) :
        info=lines[i].split()
        if info[0]=="double" :
            if info[1]!=info[2] :
                str+="\t\tmodcpy({},{});\n".format(info[2],info[1])
            str+="\t\tmodsqr({});\n".format(info[1])
        if info[0]=="add" :
            if info[2]==info[1] :
                str+="\t\tmodmul({},{});\n".format(info[3],info[1])
            elif info[3]==info[1] :
                str+="\t\tmodmul({},{});\n".format(info[2],info[1])
            if info[2]!=info[1] and info[3]!=info[1] :
                str+="\t\tmodcpy({},{});\n".format(info[2],info[1])
                str+="\t\tmodmul({},{});\n".format(info[3],info[1])
        if info[0]=="shift" :
            if info[2]!=info[1] :
                str+="\t\tmodcpy({},{});\n".format(info[2],info[1])
            str+="\t\tmodnsqr({},{});\n".format(info[1],int(info[3]))
    str+="\t\tmodcpy(z,r);\n"
    str+="\t}\n"
    f.close()
    return str

def modinv() :
    str="\t// calculate inverse, provide progenitor h if available, null if not\n"
    str+="\t"+pub()+"void modinv(int[] h,int[] z) {\n"
    str+="\t\tint[] s=new int[{}];\n".format(N)
    str+="\t\tint[] t=new int[{}];\n".format(N)
    str+="\t\tif (h!=null) {\n"
    str+="\t\t\tmodcpy(h,t);\n"
    str+="\t\t} else {\n"
    str+="\t\t\tmodpro(z,t);\n"
    str+="\t\t}\n"
    str+="\t\tmodcpy(z,s);\n"
    if PM1D2>1 :
        str+="\t\tfor (int i=0;i<{}-1;i++) {{\n".format(PM1D2)
        str+="\t\t\tmodsqr(s);\n"
        str+="\t\t\tmodmul(z,s);\n"
        str+="\t\t}\n"
    str+="\t\tmodnsqr(t,{});\n".format(PM1D2+1)
    str+="\t\tmodcpy(t,z);\n"
    str+="\t\tmodmul(s,z);\n"
    str+="\t}\n"
    return str

def modqr() :
    str="\t// Test for quadratic residue, provide progenitor h if available, null if not\n"
    str+="\t"+pub()+"boolean modqr(int[] h,int[] x) {\n"
    str+="\t\tint[] r=new int[{}];\n".format(N)
    str+="\t\tif (h!=null) {\n"
    str+="\t\t\tmodcpy(h,r);\n"
    str+="\t\t} else {\n"
    str+="\t\t\tmodpro(x,r);\n"
    str+="\t\t}\n"
    str+="\t\tmodsqr(r);\n"
    str+="\t\tmodmul(x,r);\n"
    if PM1D2>1 :
        str+="\t\tmodnsqr(r,{});\n".format(PM1D2-1)
    str+="\t\treturn modis1(r) || modis0(x);\n\t}\n"
    return str

def modsqrt() :
    str="\t// Modular square root, provide progenitor h if available, null if not\n"
    str+="\t"+pub()+"void modsqrt(int[] h,int[] x) {\n"
    if PM1D2>1 :
        str+="\t\tint[] t=new int[{}];\n".format(N)
        str+="\t\tint[] b=new int[{}];\n".format(N)
        str+="\t\tint[] v=new int[{}];\n".format(N)
        str+="\t\tint[] z={"
        for i in range(0,N-1) :
            str+=H(ROI[i])
            str+=","
        str+=H(ROI[N-1])
        str+="};\n"
    str+="\t\tint[] y=new int[{}];\n".format(N)
    str+="\t\tint[] s=new int[{}];\n".format(N)
    str+="\t\tif (h!=null) {\n"
    str+="\t\t\tmodcpy(h,y);\n"
    str+="\t\t} else {\n"
    str+="\t\t\tmodpro(x,y);\n"
    str+="\t\t}\n"
    str+="\t\tmodcpy(x,s);\n"
    str+="\t\tmodmul(y,s);\n"
    if PM1D2>1 :
        str+="\t\tmodcpy(s,t);\n"
        str+="\t\tmodmul(y,t);\n"
        str+="\t\tnres(z);\n"
        str+="\t\tfor (int k={};k>=2;k--) {{\n".format(PM1D2)
        str+="\t\t\tmodcpy(t,b);\n"

        str+="\t\t\tmodnsqr(b,k-2);\n"
        str+="\t\t\tint d=1-(modis1(b)?1:0);\n"
        str+="\t\t\tmodcpy(z,v);\n"
        str+="\t\t\tmodmul(s,v);\n"
        str+="\t\t\tmodcmv(d,v,s);\n"
        str+="\t\t\tmodsqr(z);\n"
        str+="\t\t\tmodcpy(z,v);\n"
        str+="\t\t\tmodmul(t,v);\n"
        str+="\t\t\tmodcmv(d,v,t);\n"
        str+="\t\t}\n"
    str+="\t\tmodcpy(s,x);\n"
    str+="\t}\n"
    return str

def modis1(n,base) :
    str="\t// is unity?\n"
    str+="\t"+pub()+"boolean modis1(int[] a) {\n"
    str+="\t\tint[] c=new int[{}];\n".format(N)
    str+="\t\tint d=0;\n"
    str+="\t\tmodcpy(a,c);\n"
    str+="\t\tredc(c);\n"
    str+="\t\tfor (int i=1;i<{};i++) {{\n".format(N)
    str+="\t\t\td|=c[i];\n\t\t}\n"
    str+="\t\tint c0=c[0];\n"
    str+="\t\treturn (1&((d-1)>>{})&(((c0^1)-1)>>{}))!=0;\n\t}}\n".format(base,base)
    return str

def modis0(n,base) :
    str="\t// is zero?\n"
    str+="\t"+pub()+"boolean modis0(int[] a) {\n"
    str+="\t\tint[] c=new int[{}];\n".format(N)
    str+="\t\tint d=0;\n"
    str+="\t\tmodcpy(a,c);\n"
    str+="\t\tredc(c);\n"
    str+="\t\tfor (int i=0;i<{};i++) {{\n".format(N)
    str+="\t\t\td|=c[i];\n\t\t}\n"
    str+="\t\treturn (1&((d-1)>>{}))!=0;\n\t}}\n".format(base)
    return str

def modltn() :
    str="\t// is lexically less than?\n"
    str+="\t"+pub()+"boolean modltn(int[] a,int[] b) {\n"
    str+="\t\tint[] c=new int[{}];\n".format(N)
    str+="\t\tint[] d=new int[{}];\n".format(N)
    str+="\t\tmodcpy(a,c);\n"
    str+="\t\tredc(c);\n"
    str+="\t\tmodcpy(b,d);\n"
    str+="\t\tredc(d);\n"
    str+="\t\tfor (int i=0;i<{};i++) {{\n".format(N)
    str+="\t\t\tc[i]-=d[i];\n\t\t}\n"
    str+="\t\treturn (prop(c)&1)!=0;\n"
    str+="\t}\n"
    return str

def modzer() :
    str="\t// set to zero\n"
    str+="\t"+pub()+"void modzer(int[] a) {\n"
    str+="\t\tfor (int i=0;i<{};i++) {{\n".format(N)
    str+="\t\t\ta[i]=0;\n\t\t}\n"
    str+="\t}\n"
    return str

def modone() :
    str="\t// set to one\n"
    str+="\t"+pub()+"void modone(int[] a) {\n"
    str+="\t\ta[0]=1;\n"
    str+="\t\tfor (int i=1;i<{};i++) {{\n".format(N)
    str+="\t\t\ta[i]=0;\n\t\t}\n"
    str+="\t\tnres(a);\n"
    str+="\t}\n"
    return str

def modint() :
    str="\t// set to integer\n"
    str+="\t"+pub()+"void modint(int x,int[] a) {\n"
    str+="\t\ta[0]=x;\n"
    str+="\t\tfor (int i=1;i<{};i++) {{\n".format(N)
    str+="\t\t\ta[i]=0;\n\t\t}\n"
    str+="\t\tnres(a);\n"
    str+="\t}\n"
    return str

# convert to Montgomery nresidue form
def nres(n,base) :
    str="\t// Convert n to n-residue form, n=nres(m)\n"
    str+="\t"+pub()+"void nres(int[] n) {\n"
    str+="\t\tint[] c={"
    for i in range(0,N-1) :
        str+=H(cw[i])
        str+=","
    str+=H(cw[N-1])
    str+="};\n"
    str+="\t\tmodmul(c,n);\n"
    str+="\t}\n"
    return str

#convert back from Montgomery to integer form
def redc(n,base) :
    str="\t// Convert m back to normal form, m=redc(n)\n"
    str+="\t"+pub()+"void redc(int[] m) {\n"
    str+="\t\tint[] c=new int[{}];\n".format(N)
    str+="\t\tc[0]=1;\n"
    str+="\t\tmodmul(c,m);\n"
    str+="\t\tmodfsb(m);\n"
    str+="\t}\n"
    return str

#conditional swap -  see Santos and Scott eprint 2025
def modcsw() :
    str="\t// conditional swap g and f if d=1\n"
    str+="\t"+pub()+"void modcsw(int b,int[] g,int[] f) {\n"
    str+="\t\tint mask=-b;\n"
    str+="\t\tfor (int i=0;i<{};i++) {{\n".format(N)
    str+="\t\t\tint delta=(g[i]^f[i])&mask;\n"
    str+="\t\t\tg[i]^=delta;\n"
    str+="\t\t\tf[i]^=delta;\n"
    str+="\t\t}\n"
    str+="\t}\n"
    return str

#conditional move
def modcmv() :
    str="\t// conditional move g to f if d=1\n"
    str+="\t"+pub()+"void modcmv(int b,int[] g,int[] f) {\n"
    str+="\t\tint mask=-b;\n"
    str+="\t\tfor (int i=0;i<{};i++) {{\n".format(N)
    str+="\t\t\tint delta=(g[i]^f[i])&mask;\n"
    str+="\t\t\tf[i]^=delta;\n"
    str+="\t\t}\n"
    str+="\t}\n"
    return str

#shift left
def modshl(n,base) :
    N=getN(n,base)
    mask=(1<<base)-1
    str="\t// shift left by less than a word\n"
    str+="\t"+pub()+"void modshl(int n,int[] a) {\n"
    str+="\t\ta[{}-1]=((a[{}-1]<<n))+(a[{}-2]>>>({}-n));\n".format(N,N,N,base)
    str+="\t\tfor (int i={}-2;i>=1;i--) {{\n".format(N)
    str+="\t\t\ta[i]=((a[i]<<n)&{})+(a[i-1]>>>({}-n));\n\t\t}}\n".format(H(mask),base)
    str+="\t\ta[0]=(a[0]<<n)&{};\n".format(H(mask))
    str+="\t}\n"
    return str

#shift right
def modshr(n,base) :
    N=getN(n,base)
    mask=(1<<base)-1
    str="\t// shift right by less than a word. Return shifted out part\n"
    str+="\t"+pub()+"int modshr(int n,int[] a) {\n"
    str+="\t\tint r=a[0]&((1<<n)-1);\n"
    str+="\t\tfor (int i=0;i<{}-1;i++) {{\n".format(N)
    str+="\t\t\ta[i]=(a[i]>>>n)+((a[i+1]<<({}-n))&{});\n\t\t}}\n".format(base,H(mask))
    str+="\t\ta[{}-1]=a[{}-1]>>>n;\n".format(N,N)
    str+="\t\treturn r;\n\t}\n"
    return str


#divide by 2
def modhaf(n,base) :
    N=getN(n,base)
    str="\t// divide by 2. Shift right 1 bit (or add p and shift right one bit)\n"
    str+="\t"+pub()+"void modhaf(int[] n) {\n"
    str+="\t\tint[] t=new int[{}];\n".format(N)
    if E:
        str+="\t\tint q=1<<{};\n".format(base)
    str+="\t\tprop(n);\n"
    str+="\t\tmodcpy(n,t);\n"
    str+="\t\tint lsb=modshr(1,t);\n"
    str+=addp(1);
    str+="\t\tprop(n);\n"
    str+="\t\tmodshr(1,n);\n"
    str+="\t\tmodcmv(1-lsb,t,n);\n"
    str+="\t}\n"
    return str

#set a=2^r
def mod2r() :
    str="\t// set a= 2^r\n"
    str+="\t"+pub()+"void mod2r(int r,int[] a) {\n"
    str+="\t\tint n=r/{};\n".format(base)
    str+="\t\tint m=r%{};\n".format(base)
    str+="\t\tmodzer(a);\n"
    str+="\t\tif (r>={}*8) {{\n".format(Nbytes)
    str+="\t\t\treturn;\n\t\t}\n"
    str+="\t\ta[n]=1;\n"
    str+="\t\ta[n]<<=m;\n"
    str+="\t\tnres(a);\n\t}\n"
    return str

#export to byte array
def modexp() :
    str="\t// export to byte array\n"
    str+="\t"+pub()+"void modexp(int[] a,byte[] b) {\n"
    str+="\t\tint[] c=new int[{}];\n".format(N)
    str+="\t\tmodcpy(a,c);\n"
    str+="\t\tredc(c);\n"
    str+="\t\tfor (int i={}-1;i>=0;i--) {{\n".format(Nbytes)
    str+="\t\t\tb[i]=(byte)(c[0]&0xff);\n"
    str+="\t\t\tmodshr(8,c);\n\t\t}\n"
    str+="\t}\n"
    return str

#import from byte array
def modimp() :
    str="\t// import from byte array\n"
    str+="\t"+pub()+"boolean modimp(byte[] b,int[] a) {\n"
    str+="\t\tfor (int i=0;i<{};i++) {{\n".format(N)
    str+="\t\t\ta[i]=0;\n\t\t}\n"
    str+="\t\tfor (int i=0;i<{};i++) {{\n".format(Nbytes)
    str+="\t\t\tmodshl(8,a);\n"
    str+="\t\t\ta[0]+=b[i]&0xff;\n\t\t}\n"
    str+="\t\tint res=modfsb(a);\n"
    str+="\t\tnres(a);\n"
    str+="\t\treturn res==1;\n\t}\n"
    return str

#get sign (parity)
def modsign() :
    str="\t// determine sign\n"
    str+="\t"+pub()+"int modsign(int[] a) {\n"
    str+="\t\tint[] c=new int[{}];\n".format(N)
    str+="\t\tmodcpy(a,c);\n"
    str+="\t\tredc(c);\n"
    str+="\t\treturn c[0]&1;\n\t}\n"
    return str

#compare for equality
def modcmp() :
    str="\t// return true if equal\n"
    str+="\t"+pub()+"boolean modcmp(int[] a,int[] b) {\n"
    str+="\t\tint[] c=new int[{}];\n".format(N)
    str+="\t\tint[] d=new int[{}];\n".format(N)
    str+="\t\tint eq=1;\n"
    str+="\t\tmodcpy(a,c); redc(c);\n"
    str+="\t\tmodcpy(b,d); redc(d);\n"
    str+="\t\tfor (int i=0;i<{};i++) {{\n".format(N)
    str+="\t\t\teq&=(((c[i]^d[i])-1)>>>{})&1;\n\t\t}}\n".format(base)
    str+="\t\treturn eq==1;\n"
    str+="\t}\n"
    return str

# ModArithField wrapper: the interface methods, as instance methods delegating to the static API.
# Every method is alias-safe (out may be any input). Montgomery form is handled in fromBigInteger
# (nres) and toBigInteger (redc, via modexp).
def interface(cname) :
    str="\t// ---- ModArithField implementation (Java backend only) ----\n\n"
    str+="\tprivate static final BigInteger MODULUS=new BigInteger(\"{:x}\",16);\n".format(p)
    str+="\tprivate static final int[] ONE=makeOne();\n\n"
    str+="\tprivate static int[] makeOne() {\n"
    str+="\t\tint[] a=new int[{}];\n".format(N)
    str+="\t\tmodone(a);\n"
    str+="\t\treturn a;\n\t}\n\n"
    str+="\t@Override\n\tpublic BigInteger getModulus() {\n\t\treturn MODULUS;\n\t}\n\n"
    str+="\t@Override\n\tpublic int limbs() {\n\t\treturn NLIMBS;\n\t}\n\n"
    str+="\t@Override\n\tpublic int[] newElement() {\n\t\treturn new int[NLIMBS];\n\t}\n\n"
    str+="\t@Override\n\tpublic void fromBigInteger(BigInteger x,int[] out) {\n"
    str+="\t\tif (x.signum()<0 || x.compareTo(MODULUS)>=0) {\n"
    str+="\t\t\tthrow new IllegalArgumentException(\"value out of range [0,p)\");\n\t\t}\n"
    str+="\t\tint[] a=new int[NLIMBS];\n"
    str+="\t\tfor (int i=0;i<NLIMBS;i++) {\n"
    str+="\t\t\ta[i]=x.shiftRight(RADIX*i).intValue()&((1<<RADIX)-1);\n\t\t}\n"
    str+="\t\tnres(a);\n"
    str+="\t\tmodcpy(a,out);\n\t}\n\n"
    str+="\t@Override\n\tpublic BigInteger toBigInteger(int[] a) {\n"
    str+="\t\tbyte[] b=new byte[NBYTES];\n"
    str+="\t\tmodexp(a,b);\n"
    str+="\t\treturn new BigInteger(1,b);\n\t}\n\n"
    str+="\t@Override\n\tpublic void add(int[] a,int[] b,int[] out) {\n"
    str+="\t\tif (out==b) {\n\t\t\tmodadd(a,out);\n\t\t} else {\n"
    str+="\t\t\tif (out!=a) {\n\t\t\t\tmodcpy(a,out);\n\t\t\t}\n"
    str+="\t\t\tmodadd(b,out);\n\t\t}\n\t}\n\n"
    str+="\t@Override\n\tpublic void sub(int[] a,int[] b,int[] out) {\n"
    str+="\t\tif (out==b && out!=a) {\n\t\t\tmodneg(out);\n\t\t\tmodadd(a,out);\n\t\t} else {\n"
    str+="\t\t\tif (out!=a) {\n\t\t\t\tmodcpy(a,out);\n\t\t\t}\n"
    str+="\t\t\tmodsub(b,out);\n\t\t}\n\t}\n\n"
    str+="\t@Override\n\tpublic void neg(int[] a,int[] out) {\n"
    str+="\t\tif (out!=a) {\n\t\t\tmodcpy(a,out);\n\t\t}\n"
    str+="\t\tmodneg(out);\n\t}\n\n"
    str+="\t@Override\n\tpublic void mul(int[] a,int[] b,int[] out) {\n"
    str+="\t\tif (out==b) {\n\t\t\tmodmul(a,out);\n\t\t} else {\n"
    str+="\t\t\tif (out!=a) {\n\t\t\t\tmodcpy(a,out);\n\t\t\t}\n"
    str+="\t\t\tmodmul(b,out);\n\t\t}\n\t}\n\n"
    str+="\t@Override\n\tpublic void sqr(int[] a,int[] out) {\n"
    str+="\t\tif (out!=a) {\n\t\t\tmodcpy(a,out);\n\t\t}\n"
    str+="\t\tmodsqr(out);\n\t}\n\n"
    str+="\t@Override\n\tpublic void mulSmall(int[] a,int k,int[] out) {\n"
    str+="\t\tif (k<0 || k>{}) {{\n".format(MAXSMALL)
    str+="\t\t\tthrow new IllegalArgumentException(\"multiplier out of range\");\n\t\t}\n"
    str+="\t\tif (out!=a) {\n\t\t\tmodcpy(a,out);\n\t\t}\n"
    str+="\t\tmodmli(k,out);\n"
    if trin>0 :
        str+="\t\tprop(out); // trinomial modmli leaves limbs 0 and {} unnormalised\n".format(trin)
    str+="\t}\n\n"
    str+="\t@Override\n\tpublic int maxSmallMultiplier() {\n\t\treturn "+"{}".format(MAXSMALL)+";\n\t}\n\n"
    str+="\t@Override\n\tpublic void inv(int[] a,int[] out) {\n"
    str+="\t\tif (out!=a) {\n\t\t\tmodcpy(a,out);\n\t\t}\n"
    str+="\t\tmodinv(null,out);\n\t}\n\n"
    str+="\t@Override\n\tpublic boolean isZero(int[] a) {\n\t\treturn modis0(a);\n\t}\n\n"
    str+="\t@Override\n\tpublic boolean equal(int[] a,int[] b) {\n\t\treturn modcmp(a,b);\n\t}\n\n"
    str+="\t@Override\n\tpublic void copy(int[] a,int[] out) {\n"
    str+="\t\tif (out!=a) {\n\t\t\tmodcpy(a,out);\n\t\t}\n\t}\n\n"
    str+="\t@Override\n\tpublic void one(int[] out) {\n\t\tmodcpy(ONE,out);\n\t}\n\n"
    str+="\t@Override\n\tpublic void zero(int[] out) {\n\t\tmodzer(out);\n\t}\n"
    return str

if len(sys.argv)!=3 :
    print("Syntax error")
    print("Valid syntax - python monty_java.py <word length> <prime> OR <prime> OR <prime expression>")
    print("For example - python monty_java.py 32 NIST256")
    print("For example - python monty_java.py 32 0x01fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa51868783bf2f966b7fcc0148f709a5d03bb5c9b8899c47aebb6fb71e91386409")
    exit(2)

WL=int(sys.argv[1])
if WL != 32 :
    print("Only 32-bit word length supported for Java (int limbs, long double-width)")
    exit(2)

prime=sys.argv[2]
p=0
base=0
limit=2*WL
if karatsuba :
    limit=2*WL-1

# Note that number base MUST be less than wordlength WL (unsaturated).
# The radix for an n-bit prime is 2^base where base is usually in the range 51-60 for a 64-bit processor, 26-30 for
# 32-bit and 12-13 for 16 bit
# The radix must be low enough so that the sum of L 2^(2*base) double length integers does not encroach on the sign bit,
# that is bits(L)+2*base<2*WL, where L=n/base (rounded up) is the number of limbs in the number representation. But
# at the same time radix should be high enough to minimize L. An underused top digit allows for lazy reduction.

# More named primes can be added here


### Start of user editable area

if prime=="NIST256" :
    p=2**256-2**224+2**192+2**96-1
    #if WL==64 :                          # manual override of default
    #    base=48

if prime=="NIST384" :
    p=2**384-2**128-2**96+2**32-1
#    if WL==64:
#        base=60
#    if WL==32 :
#        base=29

if prime=="X25519" :
    p=2**255-19

if prime=="X448" :
    p=2**448-2**224-1

if prime=="ED448" :
    p=2**448-2**224-1

if prime=="NIST521" :
    p=2**521-1
    #if WL==64 :
    #    base=60
    #if WL==32:
    #    karatsuba=True

if prime=="GM270" :
    p=2**270-2**162-1
    if WL==32 :
        base=29

if prime=="C414" :
    p=2**414-17

if prime=="PM512" :
    p=2**512-569
    if WL==64 :
        base=58

if prime=="GM270" :
    p=2**270-2**162-1
    if WL==32 :
        base=29

if prime=="GM266" :
    p=2**266-2**168-1
    if WL==32 :
        base=28
    if WL==64 :
        base=56

if prime=="GM240" :
    p=2**240-2**183-1
    if WL==32 :
        base=29
    if WL==64 :
        base=61

if prime=="GM360" :
    p=2**360-2**171-1
    if WL==32 :
        base=29
    if WL==64 :
        base=57

if prime=="GM480" :
    p=2**480-2**240-1
    if WL==64 :
        base=60
    if WL==32 :
        base=29

if prime=="GM384" :
    p=2**384-2**186-1
    if WL==32:
        base=29
    if WL==64:
        base=62

if prime=="GM512" :
    p=2**512-2**127-1
    if WL==32:
        base=29
        #karatsuba=True
    if WL==64:
        base=58

if prime=="PM266" :
    p=2**266-3

if prime=="PM336" :
    p=2**336-3

if prime=="NIST224" :
    p=2**224-2**96+1

if prime=="SECP256K1" :
    p=2**256-2**32-977

# Brainpool primes (RFC 5639), not Montgomery-friendly: generic full Montgomery reduction
if prime=="BRAINPOOLP256R1" :
    p=0xA9FB57DBA1EEA9BC3E660A909D838D726E3BF623D52620282013481D1F6E5377

if prime=="BRAINPOOLP384R1" :
    p=0x8CB91E82A3386D280F5D6F7E50E641DF152F7109ED5456B412B1DA197FB71123ACD3A729901D1A71874700133107EC53

if prime=="BRAINPOOLP512R1" :
    p=0xAADD9DB8DBE9C48B3FD4E6AE33C9FC07CB308DB3B3C9D20ED6639CCA703308717D4D9B009BC66842AECDA12AE6A380E62881FF2F2D82C68528AA6056583A48F3

if prime=="TWEEDLE" :
    p=0x40000000000000000000000000000000038aa127696286c9842cafd400000001

if prime=="SIDH434" :
    p=2**216*3**137-1

if prime=="SIDH503" :
    p=2**250*3**159-1

if prime=="SIDH610" :
    p=2**305*3**192-1

if prime=="SIDH751" :
    p=2**372*3**239-1

if prime=="MFP4" :
    p=3*67*(2**246)-1
    if WL==64:
        base=52

if prime=="MFP7" :
    p=2**145*(3**9)*(59**3)*(311**3)*(317**3)*(503**3)-1
    if WL==64:
        base=52

if prime=="MFP1973" :
    p=0x34e29e286b95d98c33a6a86587407437252c9e49355147ffffffffffffffffff
    if WL==64:
        base=52

if prime=="CSIDH512" :
    p=5326738796327623094747867617954605554069371494832722337612446642054009560026576537626892113026381253624626941643949444792662881241621373288942880288065659

# SQISIGN primes

if prime=="ED324" :
    p=3*2**324-1

if prime=="ED500" :
    p=27*2**500-1

if prime=="ED664" :
    p=17*2**664-1


# MIKE primes

if prime=="MIKE_FAST_1" :
    p=633*2**308-1

if prime=="MIKE_FAST_3" :
    p=593*2**474-1

if prime=="MIKE_FAST_5" :
    p=317*2**628-1

if prime=="MIKE_CONSERVATIVE_1" :
    p=117*2**374-1

if prime=="MIKE_CONSERVATIVE_3" :
    p=77*2**566-1

if prime=="MIKE_CONSERVATIVE_5" :
    p=41*2**758-1

### End of user editable area

extrabyte=0
field=True
named=(p!=0)
if p==0 :
    if not prime[0].isdigit() :
        print("This named prime not supported")
        exit(2)
    if prime[0]=='0' and prime[1]=='0' :
        field=False
        p=int(prime)
        if prime[2]=='0' :
            extrabyte=1
    else :
        p=eval(prime)

n=p.bit_length()
if n<120 or pow(3,p-1,p)!=1 :
    print("Not a sensible modulus, too small or not a prime")
    exit(2)

PM=False

if base==0 :
    base=getbase(n) #use default

trin=trinomial(p,base)
if trin>0 :
    print("Prime is a lucky trinomial")

b=2**base
N=getN(n,base)  # Number of digits in modulus (to given radix)
xcess=N*base-n  # excess bits in representation - should be 2 or greater, or 0 in which case extra "virtual" limb will be added

# Is it an exploitable Pseudo-Mersenne?
m=2**n-p
if m>1 and bits(m)+base<WL :
    PM=True
    print("Exploitable Pseudo Mersenne detected")

# find biggest power of 2 which divides p-1
p1=p-1
PM1D2=0
while (p1%2)==0 :
    PM1D2+=1
    p1>>=1
e=(1<<PM1D2)
PE=(p-1-e)//(2*e)  # exponent for use in inversion, QR check, and for square roots
if shutil.which("addchain") is not None :
    chainsrc="addchain"
    cline="addchain search {} > inv.acc".format(PE)
    subprocess.call(cline, shell=True)
    if remove_unused() :
        print("Problem in addchain - unused variables need to be removed")
    subprocess.call("addchain gen inv.acc > ac.txt", shell=True)
    os.remove("inv.acc")
else :
    chainsrc="built-in sliding window (addchain not found)"
    print("addchain not found - using built-in sliding-window addition chain")
    fallback_chain(PE,"ac.txt")
if not check_chain(PE,"ac.txt") :
    print("Error - addition chain does not compute the progenitor exponent")
    exit(1)

# get number of bytes for export
Nbytes=n//8
if (n%8)!=0 :
    Nbytes+=1
Nbytes+=extrabyte


#get non-trivial root of unity
qnr=0
roi=0
if PM1D2==1:
    roi=p-1
if PM1D2==2:
    roi=pow(2,(p-1)//4,p)
if PM1D2>2 :
    qnr=2
    while pow(qnr,(p-1)//2,p)==1 :
        qnr+=1
    roi=pow(qnr,(p-1)//e,p)

# convert to radix representation
ROI=makebig(roi,base,N)

mod8=p%8
print("Prime is of length",n,"bits and =",mod8,"mod 8. Chosen radix is",base,"bits, using",N,"limbs with excess of",xcess,"bits")
print("Using standard Comba for modmul")

# process prime, check if "virtual" extra limb required
ppw,E,npp=process_prime(p,base,N)

veryfastadd=False

npp+=4*N+1  # can we afford some more extreme lazy reduction? 2x2=4, plus one for carry-in

if npp*(2**base-1)**2 < 2**limit :
    veryfastadd=True
    print("Very fast modular addition possible")

# get M for pseudo-Mersenne 2^n-M
M=0
if PM :
    M=-ppw[0]

minus_ones=0
print("Displaying prime limbs (we like 0, -1, 1 and powers of 2)")
for i in range(0,len(ppw)) :
    if i>0 and ppw[i]==-1 :
        minus_ones+=1
    print(hex(ppw[i]))

if minus_ones>1 :
    print("Sorry - too many -1s for this script to handle")
    exit(1)

if E :
    print("Extra virtual limb added")
    R=getR(n+base,base) #add extra digit
else :
    R=getR(n,base)

# should only be an issue for bad user choice of radix
if xcess<2 and (not E) :
    print("Error - Excess is only one bit, consider change of radix")
    exit(1)


# detect if Montgomery-friendly, or not
b=2**base
ndash=inverse((R-p)%b,b)
assert (p*ndash+1)%b==0   # ndash = -1/p mod 2^base

# check if Montgomery friendly
fullmonty=True
if ndash==1 :
    fullmonty=False

# represent Montgomery constant to given radix
c=(R*R)%p              # Montgomery constant
cw=makebig(c,base,N)

maxdigit=2**base-1
maxnum=0
overflow_warnings=[]

# generate fused WL-bit modular multiplication and squaring code for shaped prime
# where the unsaturated radix is 2^base and base<WL


from contextlib import redirect_stdout

commit="d73deed" # upstream modarith commit this Java backend is derived from (same as pseudo_java.py)

if named :
    cname="Field"+prime
else :
    cname="FieldP{}".format(n)
fname=cname+".java"

# generate the code first, so that overflow warnings are seen before anything is written
body=[]
body.append(prop(n,base))
body.append(flat(n,base))
body.append(modfsb(n,base))
body.append(modadd(n,base))
body.append(modaddf(n,base))
body.append(modsub(n,base))
body.append(modsubf(n,base))
body.append(modneg(n,base))
body.append(modmli(n,base))
body.append(modmul(n,base))
body.append(modsqr(n,base))
body.append(modcpy())
body.append(modnsqr())
body.append(modpro())
body.append(modinv())
body.append(nres(n,base))
body.append(redc(n,base))
body.append(modis1(n,base))
body.append(modis0(n,base))
body.append(modltn())
body.append(modzer())
body.append(modone())
body.append(modint())
body.append(modqr())
body.append(modcmv())
body.append(modcsw())
body.append(modsqrt())
body.append(modshl(n,base))
body.append(modshr(n,base))
body.append(modhaf(n,base))
body.append(mod2r())
body.append(modexp())
body.append(modimp())
body.append(modsign())
body.append(modcmp())

if len(overflow_warnings)>0 :
    print("Error - overflow possible in",overflow_warnings,"- no code written")
    exit(1)

# output code in final form
with open(fname, 'w') as f:
    with redirect_stdout(f):
        print(LICENSE)
        print("package {};\n".format(PACKAGE))
        print("import java.math.BigInteger;\n")
        print("// Automatically generated modular arithmetic Java code")
        print("// Command line : python3 {} {} {}".format(os.path.basename(sys.argv[0]), sys.argv[1], sys.argv[2]))
        print("// Generator    : monty_java.py (Java backend of monty_rust.py), modarith commit {}".format(commit))
        print("// Python Script by Mike Scott (Technology Innovation Institute, UAE, 2025)")
        print("// Prime p      : 0x{:x}".format(p))
        print("// Montgomery representation, radix 2^{}, {} limbs of int (32-bit word mode), {}-bit prime, R=2^{}".format(base,N,n,R.bit_length()-1))
        print("// Addition chain for inversion: {}".format(chainsrc))
        print("// DO NOT EDIT: regenerate with the command line above, then run mvn spotless:apply.")
        print("/**")
        print(" * Arithmetic modulo the {}-bit prime 0x{:x}, generated by modarith (monty_java.py).".format(n,p))
        print(" *")
        print(" * <p>Static methods are the modarith API with the Rust argument order (inputs first, in/out")
        print(" * argument last). {@link #INSTANCE} implements {@link ModArithField} on top of them.")
        print(" */")
        print("@SuppressWarnings(\"all\")")
        print("public final class {} implements ModArithField {{\n".format(cname))
        print("\tpublic static final {} INSTANCE=new {}();\n".format(cname,cname))
        print("\tprivate {}() {{}}\n".format(cname))
        for s in body :
            print(s)
        print("\tstatic final int NLIMBS={};".format(N))
        print("\tstatic final int RADIX={};".format(base))
        print("\tstatic final int NBITS={};".format(n))
        print("\tstatic final int NBYTES={};".format(Nbytes))
        print("\tstatic final boolean MERSENNE=false;")
        print("\tstatic final int PMOD8={};".format(p%8))
        print("\tstatic final boolean MONTGOMERY=true;")
        if trin>0 :
            print("\tstatic final boolean MULBYINT=true;")
        else :
            print("\tstatic final boolean MULBYINT=false;")
        print("\t// Montgomery R = 2^RBITS (Java backend only, for tests)")
        print("\tstatic final int RBITS={};\n".format(R.bit_length()-1))
        print(interface(cname))
        print("}")
f.close()

# tabs to 4 spaces
src=open(fname).read().replace("\t","    ")
open(fname,"w").write(src)

os.remove("ac.txt")

print("field code is in",fname)

sys.exit(0)
