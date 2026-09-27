#!/usr/bin/env python3
"""Exact original AP digit-relation masks; no floating Fourier estimates.

The uniform Fourier bound is proved by the Hadamard transfer identity in the
accompanying note. This checks original AP lifts, exact root-polynomial zeros,
and the finite-state mask on the same complete conditional fibre.
"""
from fractions import Fraction as F
from math import gcd, isqrt, lcm
import argparse
from itertools import combinations


def require(test,message):
    if not test: raise ValueError(message)


def is_prime(p):
    return p>=2 and all(p%d for d in range(2,isqrt(p)+1))


def f_digit(r,p,t):
    a=[(r//p**j)%p for j in range(t)]
    return sum(a[j]*a[j+1] for j in range(t-1))%p


def lift(m,residues):
    require(gcd(m,15)==1,'Residual modulus coprime to both old primes')
    L=len(residues);D=15**(L-1)
    rows=[]
    for e,r in enumerate(residues):
        g=3**e*5**(L-1-e)
        a=g*((r*pow(g,-1,m))%m)
        s=((r*pow(g,-1,m)-1)*pow(15,-1,m))%m
        rows.append((a,m*g,g*(1+15*s)))
    require(len({d for _,d,_ in rows})==L,'Distinct original moduli')
    require(all(d>1 and d%2 for _,d,_ in rows),'Odd nonunit originals')
    require(lcm(*(d for _,d,_ in rows))==m*D,'Full original period')
    for i,(_,_,w) in enumerate(rows):
        for j,(a,d,_) in enumerate(rows):
            require((w%d==a)==(i==j),'Original private point against every label')
    actual=[]
    for z in range(m):
        N=D*((z*pow(D,-1,m))%m)
        hits=[N%d==a for a,d,_ in rows]
        require(hits==[z==r for r in residues],'Actual physical residual coordinate')
        actual.append(sum(hits))
    return actual,L*L,m*L


def pp_reduce(coeff,p,n):
    # Phi_(p*n)(X)=sum_(j=0)^(p-1) X^(j*n), with n a power of p.
    out=coeff[:(p-1)*n]
    for r in range(n):
        for j in range(p-1): out[r+j*n]-=coeff[r+(p-1)*n]
    return out


def graph(p,t):
    require(is_prime(p) and p>=7 and t>=1,'Ordered old3/5 and one future prime')
    n=p**t;m=p*n
    holes={r+n*f_digit(r,p,t) for r in range(n)}
    residues=[z for z in range(m) if z not in holes for _ in range(2)]
    actual,priv,pullback=lift(m,residues)
    require(actual==[0 if z in holes else 2 for z in range(m)],'Literal graph multiplicity')
    require(all(sum(actual[r+j*n]>0 for j in range(p))==p-1 for r in range(n)),
            'No complete top prime cycle')
    g=[a-1 for a in actual]
    require(F(sum(g),m)==1-F(2,p),'Fixed positive surplus')
    zero,nonzero=0,0
    for k in range(1,m):
        coeff=[0]*m
        for z,value in enumerate(g): coeff[(-k*z)%m]+=value
        vanishes=not any(pp_reduce(coeff,p,n))
        require(vanishes==(k%p==0),'Exactly lower conductors vanish')
        zero+=vanishes;nonzero+=not vanishes
    masks=[]
    for z in range(m):
        r=z%n;top=z//n
        digits=[(r//p**j)%p for j in range(t)]
        last,total=digits[0],0
        for digit in digits[1:]: last,total=digit,(total+last*digit)%p
        require(total==f_digit(r,p,t),'Same finite-state joint digit relation')
        delta=(top-total)%p
        phase=[0]*p
        for j in range(p): phase[(j*delta)%p]+=1
        reduced=[a-phase[-1] for a in phase[:-1]]
        require(reduced==([p]+[0]*(p-2) if delta==0 else [0]*(p-1)),
                'Exact factorized character average is the graph indicator')
        masks.append(int(delta==0))
    require(F(sum(masks),m)==F(1,p),'Fixed positive hole mass')
    require(F(sum(a*b for a,b in zip(g,masks)),m)==-F(1,p),'Negative same-fibre mask moment')
    # Check the finite p-Fourier orthogonality used by the transfer proof.
    for k in range(1,p):
        for a in range(p):
            for b in range(p):
                exponents=[0]*p
                for j in range(p): exponents[(k*j*(a-b))%p]+=1
                reduced=[x-exponents[-1] for x in exponents[:-1]]
                require(reduced==([p]+[0]*(p-2) if a==b else [0]*(p-1)),
                        'Hadamard transfer matrix has T* T=p I')
    # Check the polynomial recurrence by comparing its phase at each coefficient.
    for k in range(1,p):
        vectors=[[0] for _ in range(p)]
        for depth in range(1,t+1):
            previous=vectors;vectors=[]
            for b in range(p):
                phases=[]
                for j in range(p): phases.extend((x-k*b*j)%p for x in previous[j])
                direct=[(-k*(f_digit(r,p,depth)+b*((r//p**(depth-1))%p)))%p
                        for r in range(p**depth)]
                require(phases==direct,'Exact same-variable Rudin-Shapiro recurrence')
                vectors.append(phases)
    require(0 in holes, 'Integer zero is actually uncovered')
    for e in range(t+1):
        counts=[0]*(p**e)
        for z in holes: counts[z%(p**e)]+=1
        require(all(c==p**(t-e) for c in counts), 'Every proper prefix has hole ratio1/p')
    require(F(sum((a-1)*(a-2)**2 for a in actual),m)==-F(4,p),
            'Original multiplicity cubic also detects this particular family')
    return dict(p=p,t=t,m=m,labels=len(residues),private=priv,pullback=pullback,
                holes=len(holes),primitive_nonzero=nonzero,lower_zero=zero,
                mean=str(1-F(2,p)),mask_moment=str(-F(1,p)))



def relation_state(digits,p):
    last,total=digits[0],0
    for digit in digits[1:]: last,total=digit,(total+last*digit)%p
    return last,total


def state_width(p,t):
    require(is_prime(p) and p>=7 and t>=4,'Fixed-height layered width scope')
    reached={}
    for a in range(p):
        for s in range(p):
            word=((s-a)%p,1,a)
            require(relation_state(word,p)==(a,s),'Every running state is reachable')
            reached[a,s]=word
    pairs=0
    for (a,s),(b,u) in combinations(reached,2):
        next_digit=0 if s!=u else 1
        suffix=(next_digit,)+(0,)*(t-4)
        top=(s+a*next_digit)%p
        require(relation_state(reached[a,s]+suffix,p)[1]==top
                and relation_state(reached[b,u]+suffix,p)[1]!=top,
                'One common remaining input distinguishes every state pair')
        pairs+=1
    prefix_counts=[[0]*(p**e) for e in range(t+1)]
    for r in range(p**t):
        digits=[r//p**j%p for j in range(t)]
        _,top=relation_state(digits,p)
        require(top==f_digit(r,p,t),'Streaming relation uses the original low digits')
        z=r+p**t*top
        for e,counts in enumerate(prefix_counts):counts[z%(p**e)]+=1
    for e,counts in enumerate(prefix_counts):
        require(all(c==p**(t-e) for c in counts),'Exact proper-prefix graph counts')
    return dict(prime=p,low_digits=t,running_states=p*p,distinguished_pairs=pairs,
                graph_members=p**t,prefix_cells=sum(map(len,prefix_counts)))


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--check',action='store_true')
    parser.add_argument('--prime',type=int,default=7)
    parser.add_argument('--depth',type=int,default=2)
    args=parser.parse_args()
    value=graph(args.prime,args.depth)
    states=state_width(args.prime,4)
    print('PASS',value['private'],'private modular checks;',
          value['pullback'],'literal CRT fibre checks')
    print(value)
    print(states)

if __name__=='__main__':main()
