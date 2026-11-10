# Python program to generate reasonably efficient Java modular arithmetic code for pseudo-mersenne primes
# Java backend of pseudo_rust.py: same algorithms, same radix logic, only the code emission differs.
# Modulus should be a pseudo-mersenne of the form 2^n-m
# uses unsaturated radix
#
# In particular this script generates code for primes like
#
# X25519 = 2^255-19
# PM266 = 2^266-3
# NIST521 = 2^521-1
#
# uses the addchain utility if it is in the path - see https://github.com/mmcloughlin/addchain
# otherwise a built-in sliding-window addition chain is used (same ac.txt format)
#
# Execute this program as: python3 pseudo_java.py 32 X25519
# Code is output to files Field<NAME>.java (implements ModArithField) and Field<NAME>Test.java (JUnit 5)
#
# Only the 32-bit word mode is supported: SPINT=u32 -> int, DPINT=u64 -> long, SSPINT=i32 -> int, SDPINT=i64 -> long.
# Java has no unsigned types, so every Rust type cast is mapped explicitly:
#   u32 -> u64 widening       : (x&0xFFFFFFFFL)
#   i32 -> i32/u32 reinterpret: nothing (same bits)
#   u64 -> u32 narrowing      : (int)x
#   >> on SPINT/DPINT         : >>>   (logical)
#   >> on SSPINT/SDPINT       : >>    (arithmetic)
#   u8 -> u32                 : (b&0xff)
# add, sub and mul wrap modulo 2^32 / 2^64 in Java exactly as the unsigned Rust (release) / C code.
#
# Rust script by Mike Scott 22nd April 2024, TII
# Java backend for Protocol-Attacker (de.rub.nds.protocol.crypto.ec.modarith)
#

# Some default settings

karatsuba=False  # default setting (not ported to Java)
inline=True # unused in Java (the JIT decides)
makepublic=False # Java: True emits the modarith API as public static methods, False as package-private static; the ModArithField API is always public instance methods
fully_propagate=True # recommended set to True for Production code
PSCR=False # Power Side Channel Resistant conditional moves and swaps. Rust/C use a mutable static (R);
           # Java code must be stateless and the JVM gives no such guarantee anyway. Results are identical.

MODARITH_COMMIT="d73deed"
PACKAGE="de.rub.nds.protocol.crypto.ec.modarith"
LICENSE="""/*
 * Protocol-Attacker - A Framework to create Protocol Analysis Tools
 *
 * Copyright 2023-2023 Ruhr University Bochum, Paderborn University, Technology Innovation Institute, and Hackmanit GmbH
 *
 * Licensed under Apache License, Version 2.0
 * http://www.apache.org/licenses/LICENSE-2.0.txt
 */
"""

import sys
import subprocess
import os
import shutil

# u32 -> u64 widening of a (parenthesised or simple) int expression
def U(x) :
    return "({}&0xFFFFFFFFL)".format(x)

# workaround for addchain bug
def remove_unused() :
    # get all tokens
    fin = open("inv.acc")
    words = fin.read().split()
    fin.close()
    found=False

    #strip out some stuff
    for i in range(0,len(words)) :
        words[i]=words[i].replace('2*','')
        for char in words[i] :
            if char in "()":
                words[i]=words[i].replace(char,'')

    #remove operators
    while ("=" in words) :
        words.remove("=")
    while ("+" in words) :
        words.remove("+")
    while ("<<" in words) :
        words.remove("<<")
    while ("return" in words) :
        words.remove("return")

    #remove numbers
    i=0
    while (True) :
        if words[i].isdigit() :
            words.remove(words[i])
        else :
            i+=1
        if i>=len(words) :
            break

    #only variables left?
    #find those that occur only once
    unused=[]
    for i in range(0,len(words)) :
        var=words[i]
        if words.count(var) == 1 :
            found=True
            unused.append(var)

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

# Fallback when addchain is not installed: left-to-right sliding window chain for x^e,
# written in the format of "addchain gen" (first line "tmp t0 t1 ...", then double/add/shift lines)
def fallback_chain(e) :
    best=None
    for w in range(1,8) :
        bts=bin(e)[2:]
        ops=[]       # ("sq",k) or ("mul",v)
        i=0
        v0=None
        while i<len(bts) :
            if bts[i]=='0' :
                ops.append(("sq",1))
                i+=1
                continue
            j=min(i+w,len(bts))
            while bts[j-1]=='0' :
                j-=1
            v=int(bts[i:j],2)
            if v0 is None :
                v0=v
            else :
                ops.append(("sq",j-i))
                ops.append(("mul",v))
            i=j
        # merge consecutive squarings
        merged=[]
        for op in ops :
            if op[0]=="sq" and len(merged)>0 and merged[-1][0]=="sq" :
                merged[-1]=("sq",merged[-1][1]+op[1])
            else :
                merged.append(op)
        needed=sorted(set([v0]+[op[1] for op in merged if op[0]=="mul"]))
        top=max(needed)
        cost=(top//2+1 if top>1 else 0)+sum(1 for op in merged if op[0]=="mul")
        if best is None or cost<best[0] :
            best=(cost,w,v0,merged,top)
    cost,w,v0,merged,top=best
    lines=[]
    names={1:"x"}
    tmps=[]
    if top>1 :
        tmps.append("t0")                 # t0 = x^2
        lines.append("double t0 x")
        prev="x"
        for v in range(3,top+1,2) :
            name="t{}".format(len(tmps))
            tmps.append(name)
            lines.append("add {} {} t0".format(name,prev))
            names[v]=name
            prev=name
    # initial value z = x^v0, merged with the following squarings
    first_sq=0
    rest=merged
    if len(rest)>0 and rest[0][0]=="sq" :
        first_sq=rest[0][1]
        rest=rest[1:]
    lines.append("shift z {} {}".format(names[v0],first_sq))
    for op in rest :
        if op[0]=="sq" :
            lines.append("shift z z {}".format(op[1]))
        else :
            lines.append("add z z {}".format(names[op[1]]))
    f=open("ac.txt","w")
    f.write("tmp "+" ".join(tmps)+"\n")
    for l in lines :
        f.write(l+"\n")
    f.close()

# check that ac.txt computes x^e (exponent arithmetic), whoever produced it
def verify_chain(e) :
    f=open('ac.txt')
    lines=f.readlines()
    f.close()
    val={"x":1,"z":0}
    for t in lines[0].split()[1:] :
        val[t]=0
    for i in range(1,len(lines)) :
        info=lines[i].split()
        if len(info)==0 :
            continue
        if info[0]=="double" :
            val[info[1]]=2*val[info[2]]
        if info[0]=="add" :
            val[info[1]]=val[info[2]]+val[info[3]]
        if info[0]=="shift" :
            val[info[1]]=val[info[2]]<<int(info[3])
    if val["z"]!=e :
        print("Addition chain in ac.txt does not compute the required exponent")
        exit(1)
    return len(lines)-1

# Determine optimal radix
def getbase(n) :
    limbs=int(n/WL)

    while (True) :
        limbs=limbs+1
        if limbs==1 :   # must be at least 2 limbs
            limbs=2
        base=int(WL/2)
        while limbs*base<n :
            base=base+1
        if base>WL-3 :
            continue
        if limbs*(2**base-1)**2 < 2**limit :
            break
    return base


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

# int literal of a non-negative constant < 2^31 (all SPINT constants used here are)
def ilit(x) :
    if x<0 or x>=2**31 :
        print("Constant does not fit a Java int:",x)
        exit(1)
    return "0x{:x}".format(x)

# long literal of a non-negative constant < 2^63
def llit(x) :
    if x<0 or x>=2**63 :
        print("Constant does not fit a Java long:",x)
        exit(1)
    return "0x{:x}L".format(x)

#conditional add of p
def caddp(x) :
    str=""
    str+="\t\tn[0]-={}&carry;\n".format(ilit(m*x))
    str+="\t\tn[{}]+={}&carry;\n".format(N-1,ilit(x*TW))
    return str

#add p
def addp(x) :
    str=""
    str+="\t\tn[0]-={};\n".format(ilit(m*x))
    str+="\t\tn[{}]+={};\n".format(N-1,ilit(x*TW))
    return str

#subtract p
def subp(x) :
    str=""
    str+="\t\tn[0]+={};\n".format(ilit(m*x))
    str+="\t\tn[{}]-={};\n".format(N-1,ilit(x*TW))
    return str

def fhead(comment,sig) :
    return "\t// {}\n\t{}static {} {{\n".format(comment,"public " if makepublic else "",sig)

#propagate carries
def prop(n,base) :
    str=fhead("propagate carries","int prop(int[] n)")
    str+="\t\tint mask=(1<<{})-1;\n".format(base)
    str+="\t\tint carry=n[0]>>{};\n".format(base)        # (n[0] as SSPINT)>>base
    str+="\t\tn[0]&=mask;\n"
    str+="\t\tfor (int i=1;i<{};i++) {{\n".format(N-1)
    str+="\t\t\tcarry+=n[i];\n"                          # carry += n[i] as SSPINT
    str+="\t\t\tn[i]=carry&mask;\n"
    str+="\t\t\tcarry>>={};\n".format(base)              # SSPINT: arithmetic shift
    str+="\t\t}\n"
    str+="\t\tn[{}]+=carry;\n".format(N-1)
    str+="\t\treturn n[{}]>>{};\n\t}}\n".format(N-1,WL-1)  # ((n[N-1] as SSPINT)>>(WL-1)) as SPINT
    return str

#propagate carries and add p if negative, propagate carries again
def flat(n,base) :
    str=fhead("propagate carries and add p if negative, propagate carries again","int flatten(int[] n)")
    str+="\t\tint carry=prop(n);\n"
    str+=caddp(1)
    str+="\t\tprop(n);\n"
    str+="\t\treturn carry&1;\n\t}\n"
    return str

#final subtract
def modfsb(n,base) :
    str=fhead("Montgomery final subtract","int modfsb(int[] n)")
    str+=subp(1)
    str+="\t\treturn flatten(n);\n\t}\n"
    return str

#modular addition
def modadd(n,m,base) :
    str=fhead("Modular addition - can be used in all cases - reduce less than 2p","void modadd(int[] b,int[] n)")
    for i in range(0,N) :
        str+="\t\tn[{}]=n[{}]+b[{}];\n".format(i,i,i)
    str+=subp(2)
    str+="\t\tint carry=prop(n);\n"
    str+=caddp(2)
    str+="\t\tprop(n);\n"
    str+="\t}\n"
    return str

#fast modular addition
def modaddf(n,m,base) :
    str=fhead("Fast modular addition - can be used if output is consumed ONLY by multiplication or squaring","void modaddf(int[] b,int[] n)")
    for i in range(0,N) :
        str+="\t\tn[{}]=n[{}]+b[{}];\n".format(i,i,i)
    str+="\t\tprop(n);\n"
    str+="\t}\n"
    return str

#modular subtraction
def modsub(n,m,base) :
    str=fhead("Modular subtraction - can be used in all cases - reduce less than 2p","void modsub(int[] b,int[] n)")
    for i in range(0,N) :
        str+="\t\tn[{}]=n[{}]-b[{}];\n".format(i,i,i)
    str+="\t\tint carry=prop(n);\n"
    str+=caddp(2)
    str+="\t\tprop(n);\n"
    str+="\t}\n"
    return str

#modular subtraction
def modsubf(n,m,base) :
    str=fhead("Fast modular subtraction - can be used if output is ONLY consumed by multiplication or squaring","void modsubf(int[] b,int[] n)")
    for i in range(0,N) :
        str+="\t\tn[{}]=n[{}]-b[{}];\n".format(i,i,i)
    str+=addp(2)
    str+="\t\tprop(n);\n"
    str+="\t}\n"
    return str

#modular negation
def modneg(n,m,base) :
    str=fhead("Modular negation","void modneg(int[] n)")
    for i in range(0,N) :
        str+="\t\tn[{}]=0-n[{}];\n".format(i,i)
    str+="\t\tint carry=prop(n);\n"
    str+=caddp(2)
    str+="\t\tprop(n);\n"
    str+="\t}\n"
    return str

# In modmul/modsqr every (c[i] as DPINT) / (b[i] as DPINT) is read once into a long local cwI / bwI
# (=(c[i]&0xFFFFFFFFL)) before any limb is written, so the code is also alias-safe for b==c.
# mcI / tcI hold ((c[i]*mm) as u32) as DPINT and ((c[i]*2) as u32) as DPINT.

#multiplication macro
def getZM(str,row,n,m,base) :
    N=getN(n,base)
    xcess=N*base-n
    mm=m*2**xcess
    k=row+1
    L=N-1
    if karatsuba :
        print("Karatsuba is not ported to Java")
        exit(1)

    first=True
    while k<N :
        if EPM :
            if first :
                str+="\t\t"
            else :
                str+=" "
            str+="t+=mc{}*bw{};".format(k,L)
        else :
            if first :
                str+="\t\ttt=cw{}*bw{};".format(k,L)
                first=False
            else :
                str+=" tt+=cw{}*bw{};".format(k,L)
        L-=1
        k+=1
    if row<N-1:
        if overflow :
            str+=" lo=((int)tt)&mask;"
            if row==0 :
                str+=" t+={}*{};".format(U("lo"),llit(mm))
            else :
                if bad_overflow_mul :
                    str+=" t+=({}+hi)*{};".format(U("lo"),llit(mm))
                else :
                    str+=" t+={}*{};".format(U("(lo+hi)"),llit(mm))
            if bad_overflow_mul :
                str+=" hi=tt>>>{};".format(base)
            else :
                str+=" hi=(int)(tt>>>{});".format(base)
        else :
            if not EPM :
                str+=" tt*={};".format(llit(mm))
                str+=" t+=tt;"
    else :
        first=True

    k=0
    while k<=row :
        if first :
            str+="\t\tt+=cw{}*bw{};".format(k,row-k)
            first=False
        else :
            str+=" t+=cw{}*bw{};".format(k,row-k)
        k+=1
    if row==N-1 and overflow :
        if bad_overflow_mul :
            str+=" t+=hi*{};".format(llit(mm))
        else :
            str+=" t+={}*{};".format(U("hi"),llit(mm))
    str+=" int v{}=((int)t)&mask; t=t>>>{};\n".format(row,base)
    return str

#squaring macro
def getZS(str,row,n,m,base) :
    N=getN(n,base)
    xcess=N*base-n
    mm=m*2**xcess
    k=row+1
    L=N-1
    first=True
    dble=False
    if k<L :
        dble=True
    while k<L :
        if EPM :
            if mm!=2 :
                if dble :
                    if first :
                        str+="\t\t"
                    else :
                        str+=" "
                    str+="t+=mc{}*tc{};".format(k,L)
                else :
                    if first :
                        str+="\t\tt+=mc{}*cw{};".format(k,L)
                        first=False
                    else :
                        str+=" t+=mc{}*cw{};".format(k,L)
            else :
                if dble :
                    if first :
                        str+="\t\t"
                    else :
                        str+=" "
                    str+="t+=tc{}*tc{};".format(k,L)
                else :
                    if first :
                        str+="\t\tt+=tc{}*cw{};".format(k,L)
                        first=False
                    else :
                        str+=" t+=tc{}*cw{};".format(k,L)
        else :
            if first :
                str+="\t\ttt=cw{}*cw{};".format(k,L)
                first=False
            else :
                str+=" tt+=cw{}*cw{};".format(k,L)
        L-=1
        k+=1
    if dble :
        if not EPM :
            str+=" tt*=2;"
    if k==L :
        if EPM :
            if first :
                str+="\t\t"
            else :
                str+=" "
            if mm!=2 :
                str+="t+=mc{}*cw{};".format(k,k)
            else :
                str+="t+=tc{}*cw{};".format(k,k)
        else :
            if first :
                str+="\t\ttt=cw{}*cw{};".format(k,k)
                first=False
            else :
                str+=" tt+=cw{}*cw{};".format(k,k)
    first=True
    if row<N-1:
        if overflow :
            str+=" lo=((int)tt)&mask;"
        else :
            if not EPM :
                str+=" tt*={};".format(llit(mm))
                str+=" t+=tt;"
        str+=" "
    else:
        str+="\t\t"

    first=True
    k=0
    L=row

    dble=False
    if k<L :
        dble=True

    while k<L :
        if EPM and dble :
            str+="t+=cw{}*tc{};".format(k,L)
        else :
            if first :
                str+="t2=cw{}*cw{};".format(k,L)
                first=False
            else :
                str+=" t2+=cw{}*cw{};".format(k,L)
        k+=1
        L-=1

    if dble :
        if not EPM :
            str+=" t2*=2;"
    if k==L :
        if EPM :
            str+=" t+=cw{}*cw{};".format(k,k)
        else :
            if first :
                str+="t2=cw{}*cw{};".format(k,k)
                first=False
            else :
                str+=" t2+=cw{}*cw{};".format(k,k)

    if overflow :
        if row==N-1 :
            if bad_overflow_sqr :
                str+=" t+=hi*{};".format(llit(mm))
            else :
                str+=" t+={}*{};".format(U("hi"),llit(mm))
        else :
            if row==0 :
                str+=" t2+={}*{};".format(U("lo"),llit(mm))
            else :
                if bad_overflow_sqr :
                    str+=" t2+=({}+hi)*{};".format(U("lo"),llit(mm))
                else :
                    str+=" t2+={}*{};".format(U("(lo+hi)"),llit(mm))
            if bad_overflow_sqr :
                str+=" hi=tt>>>{};".format(base)
            else :
                str+=" hi=(int)(tt>>>{});".format(base)

    if not EPM :
        str+=" t+=t2;"
    str+=" int v{}=((int)t)&mask; t=t>>>{};\n".format(row,base)
    return str

# second reduction pass
def second_pass(str,n,m,base) :
    N=getN(n,base)
    mask=(1<<base)-1
    xcess=N*base-n
    smask=(1<<(base-xcess))-1
    str+="\t\t// second reduction pass\n"

    str+="\t\tint nv=v{};\n".format(N-1)
    if fred :
        if carry_on :
            print("fred and carry_on together do not type-check in the Rust original")
            exit(1)
        str+="\t\tint ut=(int)t;\n"                       # t as SPINT
        if xcess>0 :
            str+= "\t\tut=(ut<<{})+(nv>>>{}); nv&={};\n".format(xcess,base-xcess,ilit(smask))
    else :
        str+="\t\tlong ut=t;\n"                           # t as DPINT
        if xcess>0 :
            str+= "\t\tut=(ut<<{})+{}; nv&={};\n".format(xcess,U("(nv>>>{})".format(base-xcess)),ilit(smask))

    k=0
    if m>1 :
        if fred :
            str+= "\t\tut*={};\n".format(ilit(m))
        else :
            str+= "\t\tut*={};\n".format(llit(m))

    # (ut as SPINT): identity if fred, (int)ut otherwise
    uts="ut" if fred else "((int)ut)"
    if carry_on :
        str+= "\t\tint s=v0+({}&mask);\n".format(uts)
        str+= "\t\tc[0]=s&mask;\n"
        str+="\t\tut={}+(ut>>>{});\n".format(U("(s>>>{})".format(base)),base)
        str+="\t\ts=v1+({}&mask);\n".format(uts)
        str+= "\t\tc[1]=s&mask;\n"
        k+=1
    else :
        str+= "\t\tint s=v0+({}&mask);\n".format(uts)
        str+= "\t\tc[0]=s&mask;\n"

    if fred :
        str+= "\t\tint carry=(s>>>{})+(ut>>>{});\n".format(base,base)
    else :
        str+= "\t\tint carry=(s>>>{})+((int)(ut>>>{}));\n".format(base,base)
    k=k+1

    str+= "\t\tc[{}]=v{}+carry;\n".format(k,k)

    for i in range(k+1,N-1) :
        str+= "\t\tc[{}]=v{};\n".format(i,i)
    str+="\t\tc[{}]=nv;\n".format(N-1)
    if fully_propagate :
        str+="\t\tprop(c);\n"
    return str

# modular multiplication
def modmul(n,m,base) :
    N=getN(n,base)
    mask=(1<<base)-1
    xcess=N*base-n
    mm=m*2**xcess
    str=fhead("Modular multiplication, c=c*b mod 2p","void modmul(int[] b,int[] c)")
    str+="\t\tlong t=0;\n"
    for i in range(0,N) :
        str+="\t\tlong cw{}={};\n".format(i,U("c[{}]".format(i)))
    for i in range(0,N) :
        str+="\t\tlong bw{}={};\n".format(i,U("b[{}]".format(i)))
    if EPM :
        for i in range(1,N) :
            str+="\t\tlong mc{}={};\n".format(i,U("(c[{}]*{})".format(i,ilit(mm))))
    else :
        str+="\t\tlong tt=0;\n"
    if overflow :
        str+="\t\tint lo=0;\n"
        if bad_overflow_mul :
            str+="\t\tlong hi=0;\n"
        else :
            str+="\t\tint hi=0;\n"
    str+="\t\tint mask=(1<<{})-1;\n".format(base)

    for row in range(0,N) :
        str=getZM(str,row,n,m,base)

    str=second_pass(str,n,m,base)

    str+="\t}\n"
    return str

# modular squaring
def modsqr(n,m,base) :
    N=getN(n,base)
    mask=(1<<base)-1
    xcess=N*base-n
    mm=m*2**xcess
    str=fhead("Modular squaring, c=c*c mod 2p","void modsqr(int[] c)")
    str+="\t\tlong t=0;\n"
    for i in range(0,N) :
        str+="\t\tlong cw{}={};\n".format(i,U("c[{}]".format(i)))
    if EPM :
        for i in range(1,N) :
            str+="\t\tlong tc{}={};\n".format(i,U("(c[{}]*2)".format(i)))
        if mm!=2 :
            for i in range(1,N) :
                str+="\t\tlong mc{}={};\n".format(i,U("(c[{}]*{})".format(i,ilit(mm))))
    else :
        str+="\t\tlong tt=0;\n"
        str+="\t\tlong t2=0;\n"
    str+="\t\tint mask=(1<<{})-1;\n".format(base)

    if overflow :
        str+="\t\tint lo=0;\n"
        if bad_overflow_sqr :
            str+="\t\tlong hi=0;\n"
        else :
            str+="\t\tint hi=0;\n"

    for row in range(0,N) :
        str=getZS(str,row,n,m,base)

    str=second_pass(str,n,m,base)

    str+="\t}\n"
    return str

def modmli(n,m,base) :
    N=getN(n,base)
    mask=(1<<base)-1
    xcess=N*base-n
    str=fhead("Modular multiplication by an integer, c=c*b mod 2p","void modmli(int b,int[] c)")
    str+="\t\tlong t=0;\n"
    str+="\t\tint mask=(1<<{})-1;\n".format(base)

    for i in range(0,N) :
        str+="\t\tt+={}*{}; ".format(U("c[{}]".format(i)),U("b"))
        str+="int v{}=((int)t)&mask; t=t>>>{};\n".format(i,base)

    str=second_pass(str,n,m,base)

    str+="\t}\n"
    return str

def modcpy() :
    str=fhead("copy","void modcpy(int[] a,int[] c)")
    str+="\t\tfor (int i=0;i<{};i++) {{\n".format(N)
    str+="\t\t\tc[i]=a[i];\n"
    str+="\t\t}\n"
    str+="\t}\n"
    return str

def modnsqr() :
    str=fhead("square n times","void modnsqr(int[] a,int n)")
    str+="\t\tfor (int i=0;i<n;i++) {\n"
    str+="\t\t\tmodsqr(a);\n"
    str+="\t\t}\n"
    str+="\t}\n"
    return str

# uses https://github.com/mmcloughlin/addchain (or the built-in fallback) to create addition chain
def modpro() :
    f=open('ac.txt')
    lines=f.readlines()
    info=lines[0].split()
    ntmps=len(info)-1
    str=fhead("Calculate progenitor - use optimal addition chain","void modpro(int[] w,int[] r)")
    str+="\t\tint[] x=new int[{}];\n".format(N)
    str+="\t\tint[] z=new int[{}];\n".format(N)
    for i in range(0,ntmps) :
        str+="\t\tint[] t{}=new int[{}];\n".format(i,N)
    str+="\t\tmodcpy(w,x);\n"
    for i in range(1,len(lines)) :
        info=lines[i].split()
        if len(info)==0 :
            continue
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
    str=fhead("calculate inverse, provide progenitor h if available, null if not","void modinv(int[] h,int[] z)")
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
    str=fhead("Test for quadratic residue","boolean modqr(int[] h,int[] x)")
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

#modular square root
def modsqrt() :
    str=fhead("Modular square root, provide progenitor h if available, null if not","void modsqrt(int[] h,int[] x)")
    if PM1D2>1 :
        str+="\t\tint[] t=new int[{}];\n".format(N)
        str+="\t\tint[] b=new int[{}];\n".format(N)
        str+="\t\tint[] v=new int[{}];\n".format(N)
        str+="\t\tint[] z={"
        for i in range(0,N-1) :
            str+=ilit(ROI[i])
            str+=","
        str+=ilit(ROI[N-1])
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
    str=fhead("is unity?","boolean modis1(int[] a)")
    str+="\t\tint[] c=new int[{}];\n".format(N)
    str+="\t\tint d=0;\n"
    str+="\t\tmodcpy(a,c);\n"
    str+="\t\tredc(c);\n"
    str+="\t\tfor (int i=1;i<{};i++) {{\n".format(N)
    str+="\t\t\td|=c[i];\n\t\t}\n"
    str+="\t\tint c0=c[0];\n"
    str+="\t\treturn (1&((d-1)>>{})&(((c0^1)-1)>>{}))!=0;\n\t}}\n".format(base,base)   # SSPINT: arithmetic shifts
    return str

def modis0(n,base) :
    str=fhead("is zero?","boolean modis0(int[] a)")
    str+="\t\tint[] c=new int[{}];\n".format(N)
    str+="\t\tint d=0;\n"
    str+="\t\tmodcpy(a,c);\n"
    str+="\t\tredc(c);\n"
    str+="\t\tfor (int i=0;i<{};i++) {{\n".format(N)
    str+="\t\t\td|=c[i];\n\t\t}\n"
    str+="\t\treturn (1&((d-1)>>{}))!=0;\n\t}}\n".format(base)                        # SSPINT: arithmetic shift
    return str

def modltn() :
    str=fhead("is lexically less than?","boolean modltn(int[] a,int[] b)")
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
    str=fhead("set to zero","void modzer(int[] a)")
    str+="\t\tfor (int i=0;i<{};i++) {{\n".format(N)
    str+="\t\t\ta[i]=0;\n\t\t}\n"
    str+="\t}\n"
    return str

def modone() :
    str=fhead("set to one","void modone(int[] a)")
    str+="\t\ta[0]=1;\n"
    str+="\t\tfor (int i=1;i<{};i++) {{\n".format(N)
    str+="\t\t\ta[i]=0;\n\t\t}\n"
    str+="\t\tnres(a);\n"
    str+="\t}\n"
    return str

def modint() :
    str=fhead("set to integer","void modint(int x,int[] a)")
    str+="\t\ta[0]=x;\n"
    str+="\t\tfor (int i=1;i<{};i++) {{\n".format(N)
    str+="\t\t\ta[i]=0;\n\t\t}\n"
    str+="\t\tnres(a);\n"
    str+="\t}\n"
    return str

# convert to internal form
def nres(n,base) :
    str=fhead("Convert n to n-residue form, n=nres(m)","void nres(int[] n)")
    str+="\t}\n"
    return str

#convert back to integer form
def redc(n,base) :
    str=fhead("Convert m back to normal form, m=redc(n)","void redc(int[] m)")
    str+="\t\tmodfsb(m);\n"
    str+="\t}\n"
    return str

#conditional swap -  see Santos and Scott eprint 2025
def modcsw() :
    str=fhead("conditional swap g and f if d=1","void modcsw(int b,int[] g,int[] f)")
    if PSCR :
        print("PSCR needs mutable static state, not ported to Java")
        exit(1)
    else :
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
    str=fhead("conditional move g to f if d=1","void modcmv(int b,int[] g,int[] f)")
    if PSCR :
        print("PSCR needs mutable static state, not ported to Java")
        exit(1)
    else :
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
    str=fhead("shift left by less than a word","void modshl(int n,int[] a)")
    str+="\t\ta[{}]=(a[{}]<<n)+(a[{}]>>>({}-n));\n".format(N-1,N-1,N-2,base)
    str+="\t\tfor (int i={};i>=1;i--) {{\n".format(N-2)
    str+="\t\t\ta[i]=((a[i]<<n)&{})+(a[i-1]>>>({}-n));\n\t\t}}\n".format(ilit(mask),base)
    str+="\t\ta[0]=(a[0]<<n)&{};\n".format(ilit(mask))
    str+="\t}\n"
    return str

#shift right
def modshr(n,base) :
    N=getN(n,base)
    mask=(1<<base)-1
    str=fhead("shift right by less than a word. Return shifted out part","int modshr(int n,int[] a)")
    str+="\t\tint r=a[0]&((1<<n)-1);\n"
    str+="\t\tfor (int i=0;i<{};i++) {{\n".format(N-1)
    str+="\t\t\ta[i]=(a[i]>>>n)+((a[i+1]<<({}-n))&{});\n\t\t}}\n".format(base,ilit(mask))
    str+="\t\ta[{}]=a[{}]>>>n;\n".format(N-1,N-1)
    str+="\t\treturn r;\n\t}\n"
    return str

#divide by 2
def modhaf(n,base) :
    N=getN(n,base)
    str=fhead("divide by 2. Shift right 1 bit (or add p and shift right one bit)","void modhaf(int[] n)")
    str+="\t\tint[] t=new int[{}];\n".format(N)
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
    str=fhead("set a= 2^r","void mod2r(int r,int[] a)")
    str+="\t\tint n=r/{};\n".format(base)
    str+="\t\tint m=r%{};\n".format(base)
    str+="\t\tmodzer(a);\n"
    str+="\t\tif (r>={}*8) {{\n".format(Nbytes)
    str+="\t\t\treturn;\n\t\t}\n"
    str+="\t\ta[n]=1;\n"
    str+="\t\ta[n]<<=m;\n\t}\n"
    return str

#export to byte array
def modexp() :
    str=fhead("export to byte array","void modexp(int[] a,byte[] b)")
    str+="\t\tint[] c=new int[{}];\n".format(N)
    str+="\t\tmodcpy(a,c);\n"
    str+="\t\tredc(c);\n"
    str+="\t\tfor (int i={};i>=0;i--) {{\n".format(Nbytes-1)
    str+="\t\t\tb[i]=(byte)(c[0]&0xff);\n"
    str+="\t\t\tmodshr(8,c);\n\t\t}\n"
    str+="\t}\n"
    return str

#import from byte array
def modimp() :
    str=fhead("import from byte array","boolean modimp(byte[] b,int[] a)")
    str+="\t\tfor (int i=0;i<{};i++) {{\n".format(N)
    str+="\t\t\ta[i]=0;\n\t\t}\n"
    str+="\t\tfor (int i=0;i<{};i++) {{\n".format(Nbytes)
    str+="\t\t\tmodshl(8,a);\n"
    str+="\t\t\ta[0]+=b[i]&0xff;\n\t\t}\n"                     # b[i] as SPINT (u8 zero-extended)
    str+="\t\tint res=modfsb(a);\n"
    str+="\t\tnres(a);\n"
    str+="\t\treturn res==1;\n\t}\n"
    return str

#get sign (parity)
def modsign() :
    str=fhead("determine sign","int modsign(int[] a)")
    str+="\t\tint[] c=new int[{}];\n".format(N)
    str+="\t\tmodcpy(a,c);\n"
    str+="\t\tredc(c);\n"
    str+="\t\treturn Integer.remainderUnsigned(c[0],2);\n\t}\n"   # (c[0]%2) on u32
    return str

#compare for equality
def modcmp() :
    str=fhead("return true if equal","boolean modcmp(int[] a,int[] b)")
    str+="\t\tint[] c=new int[{}];\n".format(N)
    str+="\t\tint[] d=new int[{}];\n".format(N)
    str+="\t\tint eq=1;\n"
    str+="\t\tmodcpy(a,c); redc(c);\n"
    str+="\t\tmodcpy(b,d); redc(d);\n"
    str+="\t\tfor (int i=0;i<{};i++) {{\n".format(N)
    str+="\t\t\teq&=(((c[i]^d[i])-1)>>>{})&1;\n\t\t}}\n".format(base)    # SPINT: logical shift
    str+="\t\treturn eq==1;\n"
    str+="\t}\n"
    return str

# Largest k for which modmli(k,c) is safe for every element (limbs below the radix, top limb below
# (2p-1)>>(base*(N-1))): no 64-bit overflow, no truncation in the casts of the second pass, limbs
# below 2^31 before prop (prop reads them as signed) and result below 2p. Monotone in k.
def mli_safe(k) :
    mask=(1<<base)-1
    top=(2*p-1)>>(base*(N-1))
    t=0
    v=[]
    for i in range(0,N) :
        ci=mask if i<N-1 else top
        t=t+ci*k
        if t>=2**64 :
            return False
        v.append(min(t,mask))
        t=t>>base
    nv=v[N-1]
    if fred :
        if t>=2**32 :
            return False
        ut=t
        if xcess>0 :
            ut=(ut<<xcess)+(nv>>(base-xcess))
            if ut>=2**32 :
                return False
        ut*=m
        if ut>=2**32 :
            return False
    else :
        ut=t
        if xcess>0 :
            ut=(ut<<xcess)+(nv>>(base-xcess))
            if ut>=2**64 :
                return False
        ut*=m
        if ut>=2**64 :
            return False
    if carry_on :
        s=v[0]+mask
        ut=(s>>base)+(ut>>base)
        s=v[1]+mask
        kk=2
    else :
        s=v[0]+mask
        kk=1
    if (ut>>base)>=2**31 :
        return False
    carry=(s>>base)+(ut>>base)
    if v[kk]+carry>=2**31 :
        return False
    # value bound of the output: low limbs + carried limb + top limb below 2^(n) (masked)
    val=mask+sum((mask<<(base*i)) for i in range(1,N-1))+(carry<<(base*kk))+(((1<<(base-xcess))-1)<<(base*(N-1)))
    if val>=2*p :
        return False
    return True

def max_small_multiplier() :
    lo=0
    hi=2**31-1
    if not mli_safe(lo) :
        print("modmli unusable")
        exit(1)
    while lo<hi :
        mid=(lo+hi+1)//2
        if mli_safe(mid) :
            lo=mid
        else :
            hi=mid-1
    return lo

def interface(name) :
    str ="\t// ---- ModArithField (alias-safe wrappers around the modarith API above) ----\n\n"
    str+="\t@Override\n\tpublic BigInteger getModulus() {\n\t\treturn MODULUS;\n\t}\n\n"
    str+="\t@Override\n\tpublic int limbs() {\n\t\treturn NLIMBS;\n\t}\n\n"
    str+="\t@Override\n\tpublic int[] newElement() {\n\t\treturn new int[NLIMBS];\n\t}\n\n"
    str+="\t@Override\n\tpublic void fromBigInteger(BigInteger x,int[] out) {\n"
    str+="\t\tif (x.signum()<0 || x.compareTo(MODULUS)>=0) {\n"
    str+="\t\t\tthrow new IllegalArgumentException(\"value not in [0, p)\");\n\t\t}\n"
    str+="\t\tfor (int i=0;i<NLIMBS;i++) {\n"
    str+="\t\t\tout[i]=x.shiftRight(RADIX*i).intValue()&((1<<RADIX)-1);\n\t\t}\n"
    str+="\t\tnres(out);\n\t}\n\n"
    str+="\t@Override\n\tpublic BigInteger toBigInteger(int[] a) {\n"
    str+="\t\tbyte[] b=new byte[NBYTES];\n"
    str+="\t\tmodexp(a,b);\n"
    str+="\t\treturn new BigInteger(1,b);\n\t}\n\n"
    str+="\t@Override\n\tpublic void add(int[] a,int[] b,int[] out) {\n"
    str+="\t\tif (out==b) {\n\t\t\tmodadd(a,out);\n\t\t} else {\n"
    str+="\t\t\tif (out!=a) {\n\t\t\t\tmodcpy(a,out);\n\t\t\t}\n\t\t\tmodadd(b,out);\n\t\t}\n\t}\n\n"
    str+="\t@Override\n\tpublic void sub(int[] a,int[] b,int[] out) {\n"
    str+="\t\tif (out==b && out!=a) {\n\t\t\t// out=-b+a\n\t\t\tmodneg(out);\n\t\t\tmodadd(a,out);\n\t\t} else {\n"
    str+="\t\t\tif (out!=a) {\n\t\t\t\tmodcpy(a,out);\n\t\t\t}\n\t\t\tmodsub(b,out);\n\t\t}\n\t}\n\n"
    str+="\t@Override\n\tpublic void neg(int[] a,int[] out) {\n"
    str+="\t\tif (out!=a) {\n\t\t\tmodcpy(a,out);\n\t\t}\n\t\tmodneg(out);\n\t}\n\n"
    str+="\t@Override\n\tpublic void mul(int[] a,int[] b,int[] out) {\n"
    str+="\t\tif (out==b) {\n\t\t\tmodmul(a,out);\n\t\t} else {\n"
    str+="\t\t\tif (out!=a) {\n\t\t\t\tmodcpy(a,out);\n\t\t\t}\n\t\t\tmodmul(b,out);\n\t\t}\n\t}\n\n"
    str+="\t@Override\n\tpublic void sqr(int[] a,int[] out) {\n"
    str+="\t\tif (out!=a) {\n\t\t\tmodcpy(a,out);\n\t\t}\n\t\tmodsqr(out);\n\t}\n\n"
    str+="\t@Override\n\tpublic void mulSmall(int[] a,int k,int[] out) {\n"
    str+="\t\tif (k<0 || k>MAX_SMALL_MULTIPLIER) {\n"
    str+="\t\t\tthrow new IllegalArgumentException(\"small multiplier out of range\");\n\t\t}\n"
    str+="\t\tif (out!=a) {\n\t\t\tmodcpy(a,out);\n\t\t}\n\t\tmodmli(k,out);\n\t}\n\n"
    str+="\t@Override\n\tpublic int maxSmallMultiplier() {\n\t\treturn MAX_SMALL_MULTIPLIER;\n\t}\n\n"
    str+="\t@Override\n\tpublic void inv(int[] a,int[] out) {\n"
    str+="\t\tif (out!=a) {\n\t\t\tmodcpy(a,out);\n\t\t}\n\t\tmodinv(null,out);\n\t}\n\n"
    str+="\t@Override\n\tpublic boolean isZero(int[] a) {\n\t\treturn modis0(a);\n\t}\n\n"
    str+="\t@Override\n\tpublic boolean equal(int[] a,int[] b) {\n\t\treturn modcmp(a,b);\n\t}\n\n"
    str+="\t@Override\n\tpublic void copy(int[] a,int[] out) {\n\t\tmodcpy(a,out);\n\t}\n\n"
    str+="\t@Override\n\tpublic void one(int[] out) {\n\t\tmodone(out);\n\t}\n\n"
    str+="\t@Override\n\tpublic void zero(int[] out) {\n\t\tmodzer(out);\n\t}\n"
    return str

def header_comment(name,chain_src,chain_len) :
    str ="// Automatically generated modular arithmetic Java code for pseudo-Mersenne primes\n"
    str+="// Generator     : {} (Java backend of pseudo_rust.py, https://github.com/mcarrickscott/modarith)\n".format(os.path.basename(sys.argv[0]))
    str+="// Command line  : python3 {} {} {}\n".format(os.path.basename(sys.argv[0]),sys.argv[1],sys.argv[2])
    str+="// modarith      : commit {}\n".format(MODARITH_COMMIT)
    str+="// Modulus       : 2^{}-{}\n".format(n,m)
    str+="// Representation: {}-bit words, radix 2^{}, {} limbs, excess {} bits\n".format(WL,base,N,xcess)
    str+="// Inversion     : addition chain from {} ({} steps)\n".format(chain_src,chain_len)
    str+="// Python Script by Mike Scott (Technology Innovation Institute, UAE, 2025)\n"
    str+="// DO NOT EDIT: regenerate with the command line above, then run mvn spotless:apply.\n"
    return str

def java_class(name,chain_src,chain_len) :
    cls="Field"+name
    str=LICENSE
    str+="package {};\n\n".format(PACKAGE)
    str+=header_comment(name,chain_src,chain_len)
    str+="\nimport java.math.BigInteger;\n\n"
    str+="/**\n * GF(p) arithmetic for p = 2^{}-{}, generated by modarith {}.\n".format(n,m,os.path.basename(sys.argv[0]))
    str+=" *\n * <p>The static methods are the modarith API (same names and argument order as the Rust code:\n"
    str+=" * inputs first, the in/out element last). The instance methods implement {{@link ModArithField}}.\n */\n"
    str+="public final class {} implements ModArithField {{\n\n".format(cls)
    str+="\tpublic static final {} INSTANCE=new {}();\n\n".format(cls,cls)
    str+="\tstatic final int NLIMBS={};\n".format(N)
    str+="\tstatic final int RADIX={};\n".format(base)
    str+="\tstatic final int NBITS={};\n".format(n)
    str+="\tstatic final int NBYTES={};\n".format(Nbytes)
    str+="\tstatic final int PMOD8={};\n".format(p%8)
    str+="\tstatic final boolean MERSENNE=true;\n"
    str+="\tstatic final boolean MONTGOMERY=false;\n"
    str+="\tstatic final boolean MULBYINT=true;\n"
    str+="\tstatic final int MAX_SMALL_MULTIPLIER={};\n".format(ilit(MAXMLI))
    str+="\tprivate static final BigInteger MODULUS=new BigInteger(\"{:x}\",16);\n\n".format(p)
    str+="\tprivate {}() {{}}\n\n".format(cls)
    for f in [prop(n,base),flat(n,base),modfsb(n,base),modmli(n,m,base),modadd(n,m,base),modaddf(n,m,base),
              modsub(n,m,base),modsubf(n,m,base),modneg(n,m,base),modmul(n,m,base),modsqr(n,m,base),modcpy(),
              modnsqr(),modpro(),modinv(),nres(n,base),redc(n,base),modis1(n,base),modis0(n,base),modltn(),
              modzer(),modone(),modint(),modqr(),modcmv(),modcsw(),modsqrt(),modshl(n,base),modshr(n,base),
              modhaf(n,base),mod2r(),modexp(),modimp(),modsign(),modcmp()] :
        str+=f+"\n"
    str+=interface(name)
    str+="}\n"
    return str.replace("\t","    ")

# JUnit 5 differential test, @CLASS@/@TESTCLASS@/@HEADER@ are substituted
TEST_TEMPLATE=r'''package de.rub.nds.protocol.crypto.ec.modarith;

@HEADER@
import static org.junit.jupiter.api.Assertions.*;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.TreeMap;
import org.junit.jupiter.api.Test;

/**
 * Differential test of {@link @CLASS@} against BigInteger arithmetic mod p. Every result is also
 * checked to be in the closed internal form: limbs 0..N-2 in [0, 2^RADIX), value in [0, 2p).
 * Inputs cover that whole form (canonical and non-canonical values in [p, 2p)). Sizes can be
 * raised with system properties modarith.random, modarith.chains, modarith.chainLength,
 * modarith.inversions, modarith.fullEdge.
 */
public class @TESTCLASS@ {

    static final @CLASS@ F = @CLASS@.INSTANCE;
    static final BigInteger P = F.getModulus();
    static final BigInteger TWO_P = P.shiftLeft(1);
    static final int N = @CLASS@.NLIMBS;
    static final int R = @CLASS@.RADIX;
    static final int MASK = (1 << R) - 1;

    static final int RANDOM = Integer.getInteger("modarith.random", 20000);
    static final int CHAINS = Integer.getInteger("modarith.chains", 4);
    static final int CHAIN_LENGTH = Integer.getInteger("modarith.chainLength", 10000);
    static final int INVERSIONS = Integer.getInteger("modarith.inversions", 300);
    static final boolean FULL_EDGE = Boolean.getBoolean("modarith.fullEdge");
    static final long SEED = Long.getLong("modarith.seed", 0x6d6f64617269746dL);

    /** Number of checked results per operation (read by the standalone harness). */
    static final Map<String, Long> COUNTS = new TreeMap<>();

    static synchronized void count(String op) {
        COUNTS.merge(op, 1L, Long::sum);
    }

    /** Internal form of v in [0, 2p): limbs 0..N-2 masked, the rest in the top limb. */
    static int[] raw(BigInteger v) {
        assertTrue(v.signum() >= 0 && v.compareTo(TWO_P) < 0);
        int[] a = new int[N];
        for (int i = 0; i < N - 1; i++) {
            a[i] = v.shiftRight(R * i).intValue() & MASK;
        }
        a[N - 1] = v.shiftRight(R * (N - 1)).intValueExact();
        return a;
    }

    /** Integer value of the limbs (each limb read as signed). */
    static BigInteger value(int[] a) {
        BigInteger r = BigInteger.ZERO;
        for (int i = N - 1; i >= 0; i--) {
            r = r.shiftLeft(R).add(BigInteger.valueOf(a[i]));
        }
        return r;
    }

    static void checkForm(String op, int[] a) {
        assertEquals(N, a.length, op);
        for (int i = 0; i < N - 1; i++) {
            if (a[i] < 0 || a[i] > MASK) {
                fail(op + ": limb " + i + " out of range: " + Integer.toHexString(a[i]));
            }
        }
        BigInteger v = value(a);
        if (v.signum() < 0 || v.compareTo(TWO_P) >= 0) {
            fail(op + ": value out of [0, 2p): " + v.toString(16));
        }
    }

    static void check(String op, int[] out, BigInteger expected) {
        checkForm(op, out);
        BigInteger e = expected.mod(P);
        assertEquals(e, value(out).mod(P), op);
        assertEquals(e, F.toBigInteger(out), op + " (toBigInteger)");
        count(op);
    }

    /** Edge values in [0, 2p). */
    static List<BigInteger> edgeValues(boolean full) {
        List<BigInteger> l = new ArrayList<>();
        BigInteger one = BigInteger.ONE;
        BigInteger two = BigInteger.TWO;
        int n = P.bitLength();
        BigInteger c = one.shiftLeft(n).subtract(P);
        Random rnd = new Random(SEED ^ 1);
        BigInteger r = new BigInteger(n, rnd).mod(P);
        BigInteger[] base = {
            BigInteger.ZERO, one, two, BigInteger.valueOf(3), P.subtract(one), P.subtract(two),
            P.subtract(one).shiftRight(1), P.add(one).shiftRight(1), c, c.add(one), c.subtract(one),
            one.shiftLeft(64), one.shiftLeft(n - 1), one.shiftLeft(n - 1).subtract(one),
            one.shiftLeft(n).subtract(one), r, r.modInverse(P), P, P.add(one), TWO_P.subtract(one),
            TWO_P.subtract(two), P.add(P.subtract(one).shiftRight(1))
        };
        for (BigInteger b : base) {
            l.add(b);
        }
        // all limbs at max, top limb at max for values below p and below 2p
        BigInteger lowMax = one.shiftLeft(R * (N - 1)).subtract(one);
        l.add(lowMax);
        l.add(P.subtract(one).shiftRight(R * (N - 1)).shiftLeft(R * (N - 1)).add(lowMax));
        l.add(TWO_P.subtract(one).shiftRight(R * (N - 1)).shiftLeft(R * (N - 1)).add(lowMax));
        // limb / radix boundaries
        for (int k = 0; k <= n + 1; k++) {
            if (!full && k % R != 0 && k % R != 1 && k % R != R - 1 && k % 32 != 0 && k < n - 2) {
                continue;
            }
            BigInteger pk = one.shiftLeft(k);
            l.add(pk.subtract(one));
            l.add(pk);
            l.add(pk.add(one));
            l.add(P.subtract(pk));
            l.add(TWO_P.subtract(pk));
        }
        List<BigInteger> out = new ArrayList<>();
        for (BigInteger v : l) {
            if (v.signum() >= 0 && v.compareTo(TWO_P) < 0 && !out.contains(v)) {
                out.add(v);
            }
        }
        // non-canonical twins v+p
        int size = out.size();
        for (int i = 0; i < size; i++) {
            BigInteger w = out.get(i).add(P);
            if (w.compareTo(TWO_P) < 0 && !out.contains(w)) {
                out.add(w);
            }
        }
        return out;
    }

    static BigInteger randomValue(Random rnd) {
        int kind = rnd.nextInt(8);
        BigInteger v;
        switch (kind) {
            case 0: // random limbs at their extremes
                v = BigInteger.ZERO;
                for (int i = N - 1; i >= 0; i--) {
                    int limb;
                    switch (rnd.nextInt(4)) {
                        case 0:
                            limb = 0;
                            break;
                        case 1:
                            limb = MASK;
                            break;
                        case 2:
                            limb = rnd.nextInt(4);
                            break;
                        default:
                            limb = MASK - rnd.nextInt(4);
                    }
                    v = v.shiftLeft(R).add(BigInteger.valueOf(limb));
                }
                return v.mod(TWO_P);
            case 1: // near p or 2p
                v = BigInteger.valueOf(rnd.nextInt(1 << 20));
                return rnd.nextBoolean() ? P.subtract(v).subtract(BigInteger.ONE).add(TWO_P).mod(TWO_P) : TWO_P.subtract(v).subtract(BigInteger.ONE);
            case 2: // small
                return BigInteger.valueOf(rnd.nextInt(1 << 20));
            default:
                return new BigInteger(P.bitLength() + 1, rnd).mod(TWO_P);
        }
    }

    /** Input element: canonical via fromBigInteger when below p, raw otherwise. */
    static int[] element(BigInteger v, Random rnd) {
        if (v.compareTo(P) < 0 && rnd.nextBoolean()) {
            int[] a = F.newElement();
            F.fromBigInteger(v, a);
            checkForm("fromBigInteger", a);
            assertEquals(v, F.toBigInteger(a));
            count("fromBigInteger");
            return a;
        }
        return raw(v);
    }

    static int randomK(Random rnd) {
        int max = F.maxSmallMultiplier();
        return max == Integer.MAX_VALUE ? rnd.nextInt() & Integer.MAX_VALUE : rnd.nextInt(max + 1);
    }

    static int[] smallMultipliers(Random rnd) {
        int max = F.maxSmallMultiplier();
        int[] k = new int[24];
        int[] fixed = {0, 1, 2, 3, 4, 8, 19, 121665, 121666, max, max - 1, max >>> 1};
        for (int i = 0; i < k.length; i++) {
            k[i] = i < fixed.length ? Math.min(Math.max(fixed[i], 0), max) : randomK(rnd);
        }
        return k;
    }

    /** All binary and unary interface operations on a, b (fresh outputs). */
    static void allOps(BigInteger va, BigInteger vb, int[] a, int[] b, int[] ks) {
        int[] a0 = a.clone();
        int[] b0 = b.clone();
        int[] o = F.newElement();
        F.add(a, b, o);
        check("add", o, va.add(vb));
        F.sub(a, b, o);
        check("sub", o, va.subtract(vb));
        F.mul(a, b, o);
        check("mul", o, va.multiply(vb));
        F.sqr(a, o);
        check("sqr", o, va.multiply(va));
        F.neg(a, o);
        check("neg", o, va.negate());
        for (int k : ks) {
            F.mulSmall(a, k, o);
            check("mulSmall", o, va.multiply(BigInteger.valueOf(k)));
        }
        assertEquals(va.mod(P).signum() == 0, F.isZero(a));
        count("isZero");
        assertEquals(va.mod(P).equals(vb.mod(P)), F.equal(a, b));
        count("equal");
        F.copy(a, o);
        assertArrayEquals(a, o);
        count("copy");
        // inputs untouched
        assertArrayEquals(a0, a);
        assertArrayEquals(b0, b);
    }

    @Test
    public void testEdgeValues() {
        Random rnd = new Random(SEED ^ 2);
        List<BigInteger> edge = edgeValues(FULL_EDGE);
        int[] ks = smallMultipliers(rnd);
        // full cross product of a core set; the full edge set against itself only with modarith.fullEdge
        List<BigInteger> partners = FULL_EDGE ? edge : edge.subList(0, Math.min(edge.size(), 40));
        int[] ksShort = {1, F.maxSmallMultiplier()};
        for (BigInteger va : edge) {
            int[] a = raw(va);
            allOps(va, va, a, a, ks);
            for (BigInteger vb : partners) {
                allOps(va, vb, a, raw(vb), ksShort);
                allOps(vb, va, raw(vb), a, ksShort);
            }
            // equality of v and v+p
            if (va.add(P).compareTo(TWO_P) < 0) {
                assertTrue(F.equal(a, raw(va.add(P))));
                count("equal");
            }
            int[] o = F.newElement();
            F.inv(a, o);
            check("inv", o, va.mod(P).signum() == 0 ? BigInteger.ZERO : va.modInverse(P));
        }
    }

    @Test
    public void testRandom() {
        Random rnd = new Random(SEED ^ 3);
        int[] ks = smallMultipliers(rnd);
        for (int i = 0; i < RANDOM; i++) {
            BigInteger va = randomValue(rnd);
            BigInteger vb = randomValue(rnd);
            int[] k1 = {ks[rnd.nextInt(ks.length)], randomK(rnd)};
            allOps(va, vb, element(va, rnd), element(vb, rnd), k1);
        }
    }

    @Test
    public void testInverse() {
        Random rnd = new Random(SEED ^ 4);
        int[] o = F.newElement();
        int[] z = F.newElement();
        F.inv(z, o);
        check("inv", o, BigInteger.ZERO);
        F.inv(raw(P), o);
        check("inv", o, BigInteger.ZERO);
        int[] prod = F.newElement();
        for (int i = 0; i < INVERSIONS; i++) {
            BigInteger va = randomValue(rnd);
            int[] a = element(va, rnd);
            F.inv(a, o);
            BigInteger e = va.mod(P).signum() == 0 ? BigInteger.ZERO : va.modInverse(P);
            check("inv", o, e);
            F.mul(a, o, prod);
            check("mul", prod, va.multiply(e));
            if (e.signum() != 0) {
                assertTrue(F.equal(prod, raw(BigInteger.ONE)));
            }
            // in place
            F.inv(a, a);
            check("inv", a, e);
        }
    }

    @Test
    public void testConversions() {
        Random rnd = new Random(SEED ^ 5);
        int[] a = F.newElement();
        for (int i = 0; i < RANDOM / 10 + 10; i++) {
            BigInteger v = randomValue(rnd).mod(P);
            F.fromBigInteger(v, a);
            check("fromBigInteger", a, v);
            assertEquals(v, F.toBigInteger(a));
        }
        assertThrows(IllegalArgumentException.class, () -> F.fromBigInteger(P, F.newElement()));
        assertThrows(IllegalArgumentException.class, () -> F.fromBigInteger(BigInteger.ONE.negate(), F.newElement()));
        assertThrows(IllegalArgumentException.class, () -> F.mulSmall(a, -1, F.newElement()));
        if (F.maxSmallMultiplier() < Integer.MAX_VALUE) {
            assertThrows(IllegalArgumentException.class, () -> F.mulSmall(a, F.maxSmallMultiplier() + 1, F.newElement()));
        }
        F.one(a);
        check("one", a, BigInteger.ONE);
        F.zero(a);
        check("zero", a, BigInteger.ZERO);
        assertTrue(F.isZero(a));
        assertEquals(N, F.limbs());
        assertEquals(N, F.newElement().length);
    }

    /** Remaining modarith API (static methods). */
    @Test
    public void testModarithApi() {
        Random rnd = new Random(SEED ^ 6);
        int nb = @CLASS@.NBYTES;
        int count = RANDOM / 20 + 50;
        for (int i = 0; i < count; i++) {
            BigInteger va = i < 4 ? BigInteger.valueOf(i) : randomValue(rnd);
            BigInteger vb = randomValue(rnd);
            BigInteger ra = va.mod(P);
            int[] a = element(va, rnd);
            int[] b = element(vb, rnd);
            int[] c = a.clone();
            // export / import
            byte[] bytes = new byte[nb];
            @CLASS@.modexp(a, bytes);
            assertEquals(ra, new BigInteger(1, bytes));
            count("modexp");
            int[] d = F.newElement();
            assertTrue(@CLASS@.modimp(bytes, d));
            check("modimp", d, ra);
            // import of a value in [p, min(2p, 2^(8*NBYTES))) reduces and reports false
            BigInteger big = ra.add(P);
            if (big.bitLength() <= 8 * nb) {
                byte[] bb = new byte[nb];
                byte[] be = big.toByteArray();
                int off = be.length > nb ? be.length - nb : 0;
                System.arraycopy(be, off, bb, nb - (be.length - off), be.length - off);
                assertFalse(@CLASS@.modimp(bb, d));
                check("modimp", d, ra);
            }
            // sign, unity, zero, ordering
            assertEquals(ra.testBit(0) ? 1 : 0, @CLASS@.modsign(a));
            count("modsign");
            assertEquals(ra.equals(BigInteger.ONE), @CLASS@.modis1(a));
            count("modis1");
            assertEquals(ra.signum() == 0, @CLASS@.modis0(a));
            count("modis0");
            assertEquals(ra.compareTo(vb.mod(P)) < 0, @CLASS@.modltn(a, b));
            count("modltn");
            // halving
            c = a.clone();
            @CLASS@.modhaf(c);
            check("modhaf", c, ra.multiply(BigInteger.TWO.modInverse(P)));
            // quadratic residue and square root
            boolean qr = ra.signum() == 0 || ra.modPow(P.shiftRight(1), P).equals(BigInteger.ONE);
            assertEquals(qr, @CLASS@.modqr(null, a));
            count("modqr");
            int[] s = a.clone();
            int[] h = F.newElement();
            @CLASS@.modpro(a, h);
            assertEquals(qr, @CLASS@.modqr(h, a));
            if (qr) {
                @CLASS@.modsqrt(null, s);
                checkForm("modsqrt", s);
                BigInteger sv = value(s).mod(P);
                assertEquals(ra, sv.multiply(sv).mod(P));
                count("modsqrt");
                s = a.clone();
                @CLASS@.modsqrt(h, s);
                assertEquals(sv, value(s).mod(P));
            }
            // inverse with progenitor
            c = a.clone();
            @CLASS@.modinv(h, c);
            check("modinv(h)", c, ra.signum() == 0 ? BigInteger.ZERO : ra.modInverse(P));
            // lazy add/sub feeding a multiplication
            c = a.clone();
            @CLASS@.modaddf(b, c);
            @CLASS@.modmul(b, c);
            check("modaddf+modmul", c, va.add(vb).multiply(vb));
            c = a.clone();
            @CLASS@.modsubf(b, c);
            @CLASS@.modsqr(c);
            check("modsubf+modsqr", c, va.subtract(vb).pow(2));
            // conditional move / swap
            int[] f = a.clone();
            int[] g = b.clone();
            @CLASS@.modcmv(0, g, f);
            assertArrayEquals(a, f);
            @CLASS@.modcmv(1, g, f);
            assertArrayEquals(b, f);
            f = a.clone();
            @CLASS@.modcsw(0, g, f);
            assertArrayEquals(a, f);
            assertArrayEquals(b, g);
            @CLASS@.modcsw(1, g, f);
            assertArrayEquals(b, f);
            assertArrayEquals(a, g);
            count("modcmv/modcsw");
            // integers, powers of two
            int x = rnd.nextInt(Integer.MAX_VALUE) & MASK;
            @CLASS@.modint(x, c);
            check("modint", c, BigInteger.valueOf(x));
            int r = rnd.nextInt(P.bitLength());
            @CLASS@.mod2r(r, c);
            check("mod2r", c, BigInteger.ONE.shiftLeft(r));
            // modnsqr
            c = a.clone();
            int t = rnd.nextInt(8);
            @CLASS@.modnsqr(c, t);
            check("modnsqr", c, ra.modPow(BigInteger.ONE.shiftLeft(t), P));
            // modcmp, modone, modzer, modcpy
            assertEquals(ra.equals(vb.mod(P)), @CLASS@.modcmp(a, b));
            assertTrue(@CLASS@.modcmp(a, raw(ra.add(P).compareTo(TWO_P) < 0 ? ra.add(P) : ra)));
            count("modcmp");
        }
    }

    /** Random chains on 4 registers (aliasing out==a, out==b, a==b, all three) vs a BigInteger shadow. */
    @Test
    public void testChains() {
        Random rnd = new Random(SEED ^ 7);
        int regs = 4;
        for (int chain = 0; chain < CHAINS; chain++) {
            int[][] x = new int[regs][];
            BigInteger[] s = new BigInteger[regs];
            for (int i = 0; i < regs; i++) {
                s[i] = randomValue(rnd);
                x[i] = element(s[i], rnd);
                s[i] = s[i].mod(P);
            }
            for (int step = 0; step < CHAIN_LENGTH; step++) {
                int ia = rnd.nextInt(regs);
                int ib = rnd.nextInt(regs);
                int io = rnd.nextInt(regs);
                int op = rnd.nextInt(100);
                BigInteger e;
                String name;
                if (op < 25) {
                    F.mul(x[ia], x[ib], x[io]);
                    e = s[ia].multiply(s[ib]);
                    name = "chain.mul";
                } else if (op < 40) {
                    F.sqr(x[ia], x[io]);
                    e = s[ia].multiply(s[ia]);
                    name = "chain.sqr";
                } else if (op < 55) {
                    F.add(x[ia], x[ib], x[io]);
                    e = s[ia].add(s[ib]);
                    name = "chain.add";
                } else if (op < 70) {
                    F.sub(x[ia], x[ib], x[io]);
                    e = s[ia].subtract(s[ib]);
                    name = "chain.sub";
                } else if (op < 77) {
                    F.neg(x[ia], x[io]);
                    e = s[ia].negate();
                    name = "chain.neg";
                } else if (op < 87) {
                    int k = rnd.nextBoolean() ? rnd.nextInt(9) : randomK(rnd);
                    F.mulSmall(x[ia], k, x[io]);
                    e = s[ia].multiply(BigInteger.valueOf(k));
                    name = "chain.mulSmall";
                } else if (op < 89) {
                    F.inv(x[ia], x[io]);
                    e = s[ia].signum() == 0 ? BigInteger.ZERO : s[ia].modInverse(P);
                    name = "chain.inv";
                } else if (op < 92) {
                    F.copy(x[ia], x[io]);
                    e = s[ia];
                    name = "chain.copy";
                } else if (op < 94) {
                    F.one(x[io]);
                    e = BigInteger.ONE;
                    name = "chain.one";
                } else if (op < 95) {
                    F.zero(x[io]);
                    e = BigInteger.ZERO;
                    name = "chain.zero";
                } else {
                    e = randomValue(rnd).mod(P);
                    F.fromBigInteger(e, x[io]);
                    name = "chain.fromBigInteger";
                }
                s[io] = e.mod(P);
                check(name, x[io], s[io]);
                for (int i = 0; i < regs; i++) {
                    if (i != io) {
                        assertEquals(s[i], value(x[i]).mod(P), "register clobbered");
                    }
                }
                assertEquals(s[ia].signum() == 0, F.isZero(x[ia]));
                assertEquals(s[ia].equals(s[ib]), F.equal(x[ia], x[ib]));
                count("chain.isZero/equal");
            }
        }
    }
}
'''

def java_test(name) :
    cls="Field"+name
    t=TEST_TEMPLATE.replace("@CLASS@",cls).replace("@TESTCLASS@",cls+"Test")
    hdr ="// Automatically generated differential test for {}.java\n".format(cls)
    hdr+="// Generator     : {}, command line: python3 {} {} {}, modarith commit {}\n".format(os.path.basename(sys.argv[0]),os.path.basename(sys.argv[0]),sys.argv[1],sys.argv[2],MODARITH_COMMIT)
    t=t.replace("@HEADER@",hdr)
    return LICENSE+t

if len(sys.argv)!=3 :
    print("Syntax error")
    print("Valid syntax - python pseudo_java.py <word length> <prime> OR <prime> OR <prime expression>")
    print("For example - python pseudo_java.py 32 X25519")
    print("For example - python pseudo_java.py 32 2**255-19")
    exit(2)

WL=int(sys.argv[1])
if WL != 32 :
    print("Only the 32-bit word length is supported for Java (int limbs, long products)")
    exit(2)

prime=sys.argv[2]

n=0
base=0
m=0
limit=2*WL
if karatsuba :
    limit=2*WL-1

# Note that number base MUST be less than wordlength WL (unsaturated).
# The radix for an n-bit prime is 2^base where base is usually in the range 26-30 for 32-bit.
# The radix must be low enough so that the sum of L 2^(2*base) double length integers does not encroach on the sign bit,
# that is bits(L)+2*base<2*WL, where L=n/base (rounded up) is the number of limbs in the number representation. But
# at the same time radix should be high enough to minimize L. An underused top digit allows for lazy reduction.


### Start of user editable area

# More named primes can be added here
p=0
if prime=="PM266" :
    p=2**266-3

if prime=="NUMS256W" :
    p=2**256-189

if prime=="NUMS256E" :
    p=2**256-189

if prime=="NIST521" :
    p=2**521-1

if prime=="X25519" :
    p=2**255-19

if prime=="ED25519" :
    p=2**255-19

if prime=="C2065" :
    p=2**206-5

if prime=="PM336" :
    p=2**336-3

if prime=="PM383" :
    p=2**383-187

if prime=="C414" :
    p=2**414-17

if prime=="PM512" :
    p=2**512-569

if prime=="SECP256K1" :
    p=2**256-2**32-977

name=prime
if p==0 :
    if prime[0].isdigit() :
        p=eval(prime)
        name="Custom"
    else :
        print("This named prime not supported (not a pseudo-Mersenne?)")
        exit(2)

### End of user editable area

n=p.bit_length()
if n<120 or pow(3,p-1,p)!=1 :
    print("Not a sensible modulus, too small or not a prime")
    exit(2)

if base==0 :
    base=getbase(n)   # use default radix
m=2**n-p
b=2**base

# find biggest power of 2 which divides p-1
p1=p-1
PM1D2=0
while (p1%2)==0 :
    PM1D2+=1
    p1>>=1
e=(1<<PM1D2)
PE=(p-1-e)//(2*e)
if shutil.which("addchain") is not None :
    cline="addchain search {} > inv.acc".format(PE)
    subprocess.call(cline, shell=True)
    if remove_unused() :
        print("Problem in addchain - unused variables need to be removed")
    subprocess.call("addchain gen inv.acc > ac.txt", shell=True)
    os.remove("inv.acc")
    chain_src="addchain"
else :
    print("addchain not found - using built-in sliding window addition chain")
    fallback_chain(PE)
    chain_src="built-in sliding window (addchain not installed)"
chain_len=verify_chain(PE)

if m>=b :
    print("Not an exploitable pseudo-Mersenne - Use Montgomery method instead")
    exit(1)

# get number of limbs
N=getN(n,base)
xcess=N*base-n
mm=m*2**xcess

# check for excess too large
if mm >= 2**(WL-1) :
    print("Unfortunate choice of radix - excess",xcess,"too large - try using smaller radix")
    exit(1)

if (n%base)==0 :
    TW=b
else :
    TW=(1<<(n%base)) # Top word of prime

# get number of bytes for export
Nbytes=n//8
if (n%8)!=0 :
    Nbytes+=1

# get non-trivial root of unity
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

overflow=False
bad_overflow_mul=False
bad_overflow_sqr=False
if (b-1)*(b-1)*mm*N >= 2**(2*WL) :
    overflow=True
    print("Possibility of overflow... using alternate method")
    if (N-1)*(b-1)**2 >= 2**(2*WL-3) :
        bad_overflow_mul=True
        bad_overflow_sqr=True
if bad_overflow_mul :
    print("Overflow requires extra resource")

# faster reduction
fred=False
if (N+1)*(b-1)*mm < 2**WL :
    fred=True
    print("Tighter reduction")

# check if multiplication can be done single precision
EPM=False
if not overflow :
    if mm*(b-1)<2**WL :
        EPM=True
        print("Fully Exploitable Pseudo-Mersenne detected")

# Do we need to propagate carries a bit further?
carry_on=False
if m*(2**(2*WL-base+xcess)+2**(base-xcess)) >= 2**(2*base) :
    print("Must propagate carries one limb further in second pass")
    carry_on=True

MAXMLI=max_small_multiplier()
print("Largest safe small multiplier for modmli:",MAXMLI)

modulus=p

cls="Field"+name
with open(cls+'.java', 'w') as f:
    f.write(java_class(name,chain_src,chain_len))
with open(cls+'Test.java', 'w') as f:
    f.write(java_test(name))
os.remove("ac.txt")

print("Field code is in {}.java, test in {}Test.java".format(cls,cls))

sys.exit(base)
