#!/usr/bin/env python3
"""Exact self-audit of the unrestricted i=3 cofactor reduction.

The proof is in Library/notes/erdos699_joint_lift_wss.md, sections 6-8.
This program does not prove Erdos 699 or its arbitrary-high carry step.
Its nonempty controls retain the n-1/n-2 low-digit conditions and can fail
at a prime of n. No prospective counterexample is declared from them.
"""
from fractions import Fraction
from math import gcd
from hashlib import sha256
import argparse
import json


def require(value: bool, message: str) -> None:
    if not value:
        raise AssertionError(message)


def vp(n: int, p: int) -> int:
    require(n > 0 and p >= 2, 'positive valuation arguments')
    result = 0
    while n % p == 0:
        result += 1
        n //= p
    return result


def oddpart(n: int) -> int:
    require(n > 0, 'positive odd part argument')
    return n // (n & -n)


def inspect(n: int, j: int) -> dict:
    require(n % 4 == 0 and 3 < j and 2*j <= n, 'original range')
    theta = Fraction((n-j)*(n-j-1), (n-1)*(n-2))
    x, D = theta.numerator, theta.denominator
    G, R = gcd(n-1,j), gcd(n-1,j-1)
    eta = 3 if vp(n-1,3) == 1 and j % 3 == 2 else 1
    Q = oddpart(gcd(n-2,j))
    require(n-1 == eta*G*R and gcd(G,R) == 1, 'exact n-1 allocation')
    require(D == eta*Q, 'exact denominator, including exceptional 3')
    L = eta*G
    require((j-1) % R == 0, 'integral m')
    m = (j-1)//R
    require(m > 0 and 2*m < L and gcd(m,L) == 1, 'primitive half-range')
    require((L+m) % Q == 0, 'Q divides L+m')
    t = (L+m)//Q
    E = Q*(L-m)**2 - x*eta*G**2
    require(E > 0 and t > 0, 'positive exact residual')
    require(E*(n-2) == Q*m*(L-m), 'cancelled denominator-gap identity')
    w = E*t
    require(w*(n-2) == m*(L*L-m*m), 'primitive cubic identity')
    require(w % L == pow(m,3,L) and gcd(w,L) == 1, 'primitive residue')
    require(8*(n-2) < 3*L**3, 'uniform size consequence')
    return dict(n=n,j=j,eta=eta,G=G,R=R,Q=Q,L=L,m=m,x=x,D=D,E=E,t=t,w=w)


def run(limit: int) -> dict:
    require(limit >= 80000, 'retain the explicit nonempty control')
    spf = list(range(limit+1))
    for p in range(2,int(limit**.5)+1):
        if spf[p] == p:
            for a in range(p*p,limit+1,p):
                if spf[a] == a:
                    spf[a] = p
    def factors(a: int) -> list[tuple[int,int]]:
        result=[]
        while a > 1:
            p=spf[a]; power=1
            while a % p == 0:
                a//=p; power*=p
            result.append((p,power))
        return result
    stream=sha256(); controls=0; eta_counts={1:0,3:0}; samples={}
    residue_checks=0
    for n in range(8,limit+1,4):
        mod=1; residues=[0]
        for p, power in factors(n-1):
            if p == 3 and power == 3:
                continue
            inverse=pow(mod,-1,power)
            residues=[a+mod*((b-a)*inverse % power)
                      for a in residues for b in (0,1)]
            mod*=power
        second=[power for p,power in factors(n-2)
                if p > 2 and not (p == 3 and power == 3)]
        for a in residues:
            for j in range(a,n//2+1,mod):
                if j <= 3:
                    continue
                residue_checks+=1
                if any(j % power > 2 for power in second):
                    continue
                row=inspect(n,j)
                controls+=1; eta_counts[row['eta']]+=1
                samples.setdefault(row['eta'],row)
                stream.update(f'{n},{j},{row["eta"]},{row["E"]},{row["t"]}\n'.encode())
    control=inspect(76672,26775)
    require(control['L']==63 and control['m']==22 and control['E']==control['t']==1,
            'fixed algebraic control')
    n,j,p=76672,26775,599
    def binomial_val(n: int,k: int,p: int) -> int:
        result=0; power=p
        while power<=n:
            result+=n//power-k//power-(n-k)//power
            power*=p
        return result
    require(binomial_val(n,3,p)==binomial_val(n,j,p)==1,'missing prime-of-n control')
    require(controls>0,'do not call vacuous tests a nonempty interface audit')
    return dict(scope='Exact self-audit only; no whole-conjecture proof or novelty claim',
                nmax=limit,n_minus_one_candidate_pairs=residue_checks,
                full_low_layer_controls=controls,eta_counts=eta_counts,
                samples=samples,control=control,
                unexcluded_control_has_common_prime=599,
                control_stream_sha256=stream.hexdigest())


if __name__ == '__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--nmax',type=int,default=300000)
    args=parser.parse_args()
    print(json.dumps(run(args.nmax),sort_keys=True,indent=2))
