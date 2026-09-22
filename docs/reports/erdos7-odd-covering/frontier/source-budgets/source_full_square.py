#!/usr/bin/env python3
"""Actual canonical-cylinder and pair masses for report339's complete F_N.

The common clean-coordinate compression preserves a square maximizer for
the plain law and the fixed row weights. These are actual intersections;
the formula does not assert that their separate maxima coexist.
"""
from fractions import Fraction as F
from functools import lru_cache
from itertools import product

CELLS=(0,3,1,4,7)


def choices(a):
    if type(a) is not int or a < 0:
        raise ValueError('Nonnegative integer ternary exponent required')
    return (0,) if a==0 else (0,1) if a==1 else (0,3,4) if a==2 else (3,4,18)


class CompressedSource:
    def __init__(self,N,weighted=False):
        if type(N) is not int or N<3 or type(weighted) is not bool:
            raise ValueError('F_N source requires N>=3')
        self.N=N
        self.weighted=weighted
        self.t=(1-F(1,3**(N-2)))/18
        self.q=(1-F(1,5**N))/4
        self.u=(5+F(1,7**N))/6
        self.z=1-self.q
        self.weights=(F(11,8),F(5,4),F(1),F(1),F(1)) if weighted else (F(1),)*5
        self.eta=(F(1,9)-self.t,F(1,9),F(1,9),F(1,9),F(1,9))
        self.n=(self.z*self.eta[0],self.z/9,(1-3*self.q)/9,
                (1-2*self.q)/9,(1-2*self.q)/9-self.t*self.q)
        self.gamma=(1-1/(7*self.u),1-2/(7*self.u),F(1),F(1),F(1))
        self.normalization=sum(w*g*n for w,g,n in zip(self.weights,self.gamma,self.n))
        self.haar_normalization=self.u*self.normalization

    @lru_cache(None)
    def three_vectors(self,A,r):
        """Unweighted (raw35, pure3) masses, restricted to each surviving mod9 cell."""
        if not (type(A) is int and type(r) is int and 0<=A<=self.N and r in choices(A)):
            raise ValueError('Noncanonical three cylinder')
        if A<=2:
            mask=tuple(j%3**A==r for j in CELLS)
            return (tuple(n*int(m) for n,m in zip(self.n,mask)),
                    tuple(e*int(m) for e,m in zip(self.eta,mask)))
        j=CELLS.index(r%9)
        pure=[F(0)]*5
        raw=[F(0)]*5
        pure[j]=F(1,3**A)
        raw[j]=pure[j]*(self.z if r in (3,18) else 1-2*self.q)
        return tuple(raw),tuple(pure)

    @lru_cache(None)
    def mass(self,A,r,B,E):
        """Probability of actual canonical cylinder (A,r; B,4; E,4).

        A coordinate at exponent0 imposes no condition. All source originals
        through N remain in the law; B/E do not truncate the source family.
        """
        if not (type(B) is int and type(E) is int and 0<=B<=self.N and 0<=E<=self.N):
            raise ValueError('Test exponent exceeds source period')
        raw,pure=self.three_vectors(A,r)
        vec=raw if B==0 else pure
        if E==0:
            ans=sum(w*g*x for w,g,x in zip(self.weights,self.gamma,vec))
        else:
            ans=sum(w*x for w,x in zip(self.weights,vec))/self.u
        return ans/F(5**B*7**E)/self.normalization

    def pair_mass(self,left,right):
        """Inputs (a,b,e,r); result is the actual intersection, never a cap."""
        a,b,e,r=left
        A,B,E,s=right
        self.mass(a,r,b,e)
        self.mass(A,s,B,E)
        if (r-s)%3**min(a,A):
            return F(0)
        return self.mass(max(a,A),r if a>=A else s,max(b,B),max(e,E))

    def option_matrix(self,h):
        """Flat options and exact Gram matrix; enforce one option per label.

        For x one-hot by (a,b,e), x^T M x is the complete squared load:
        diagonal once, distinct unordered pairs twice.
        """
        if not 0<=h<=self.N:
            raise ValueError('Head exceeds source period')
        options=[(a,b,e,r) for a,b,e in product(range(h+1),repeat=3) for r in choices(a)]
        return options,[[self.pair_mass(x,y) for y in options] for x in options]

    def square(self,layout):
        return sum(self.pair_mass(x,y) for x in layout for y in layout)

    def centered_square(self):
        """Integrate the complete centered4 layout, including every label pair."""
        return sum((2*a+1)*(2*b+1)*(2*e+1)*self.mass(a,4%3**a,b,e)
                   for a,b,e in product(range(self.N+1),repeat=3))

    def deep_coefficients(self):
        """Mass(A,r,B,E)=3^-A5^-B7^-E C[r,B>0,E>0], A>=3."""
        return {(r,b,e):self.mass(3,r,b,e)*3**3*5**b*7**e
                for r,b,e in product((3,4,18),(0,1),(0,1))}
