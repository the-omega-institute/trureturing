---
slug: hoster-stump-2025-chow-polynomials-simplicial-posets
bibkey: hosterstump2025chow
doi: null
url: https://arxiv.org/abs/2508.15538v1
triage: theorem
motivation_gids:
  - D5/S3/Zeros/SimplicialPosetChowRefutation.result
---

# Hoster–Stump Conjecture 1.5: simplicial-poset Chow polynomials

## Problem

Elena Hoster and Christian Stump, *Chow polynomials of simplicial posets
with positive h-vector are real-rooted*, arXiv:2508.15538v1, Section 1,
Conjecture 1.5, states:

> Let P be a simplicial poset. Then H_P̂(x), H_P̂*(x) and H^aug_P̂(x) are real-rooted. Moreover, the roots of both H_P̂(x) and H_P̂*(x) interlace the roots of H^aug_P̂(x) = H^aug_P̂*(x).

This dossier anchors that single conjecture. The settlement refutes its first
assertion, and therefore the conjunction, without negating its other
real-rootedness assertions separately. The definitions are in Section 1,
page 1, equations (1.1)–(1.2); the conjecture is on page 3 and on page 4
of the FPSAC 2026 abstract.

## Motivation

The face poset of two tetrahedra meeting in one vertex is a finite graded
simplicial poset. Each maximal lower interval is a Boolean lattice of rank
four, but its Chow polynomial has a non-real complex root. It is already a
connected cone, so connectedness and being a cone do not restore the
unconditional conjecture.

## Gap

Issue #14658 preregisters CHOW-1, the verbatim conjecture, tier 1,
literature checks and the literal Lean conventions. Its source and literature
checks record no prior settlement in the checked scope: MathDB p/369893,
arXiv:2605.28474, arXiv:2510.00951, arXiv:2609.15946 and
arXiv:2411.04070v3. No claim of exhaustive literature absence is made.

## Route

The public flag f-vector counts maximal chains in the rank-selected subposet
of $\widehat P=\operatorname{WithTop}P$, retaining both endpoints. Original
elements have intrinsic rank $(\operatorname{Order.height}x).\operatorname{toNat}$;
the added top has rank $n+1$. The private chain enumeration agrees with this
literal definition on every rank set needed for the witness's flag h-sums.
The carrier contains exactly the subsets of $\{0,1,2,3\}$ or
$\{0,4,5,6\}$. Its maximal Boolean intervals have rank four.

## Falsifier

**Proved in the module:** `D5/S3/Zeros/SimplicialPosetChowRefutation.result`
is literally $\neg\operatorname{claim}$. For $P_2$ the polynomial is
$H(x)=x^4+23x^3+43x^2+23x+1$. Put
$a=(23-\sqrt{365})/2$ and $b=(23+\sqrt{365})/2$. The consumed private
lemmas `H_P2`, `H_P2_factorization`, `a_bounds`, `H_P2_root` and `z_im_ne`
establish
$H(x)=(x^2+ax+1)(x^2+bx+1)$, $0<a<2$, and the zero
$z=(-a+i\sqrt{4-a^2})/2$ with nonzero imaginary part.

## Evidence

The Lean module and its Scribe carry the settlement. The axiom closure of
every public declaration is contained in
$\{\texttt{propext},\texttt{Classical.choice},\texttt{Quot.sound}\}$.
The independent computations below use integer face and flag counts;
NumPy root counts are numerical observations and the SymPy script uses
exact algebraic roots. All three commands exit 0. The sources below can be
saved together under any directory; `triage.py` resolves `check.py` next to
itself or accepts its path as the first argument. Required packages are NumPy and SymPy.

### Computation source: check.py

Command (working directory `/private/tmp`): `python3 /tmp/op-chow/rework1/scripts/check.py`; exit 0.
SHA-256: `d39dfb1aca16750c15b1c463ab8cb06f6cf4c9dbc1d1b904f626fb543a88d173`.

```python
from itertools import combinations, chain
import numpy as np
def faces(q):
    F=set()
    for j in range(q):
        fac=(0,3*j+1,3*j+2,3*j+3)
        for k in range(5):
            for s in combinations(fac,k): F.add(frozenset(s))
    return F
def flag_alpha(F,T):
    # chains with one element at each rank in T (ranks = card); elements of P (top excluded since T ⊆ {1..n})
    T=sorted(T)
    if not T: return 1
    levels=[[f for f in F if len(f)==r] for r in T]
    cnt={f:1 for f in levels[0]}
    for lv in levels[1:]:
        cnt={g:sum(c for f,c in cnt.items() if f<g) for g in lv}
    return sum(cnt.values())
def H(q,n=4):
    F=faces(q)
    def beta(S): return sum((-1)**(len(S)-len(T))*flag_alpha(F,T) for k in range(len(S)+1) for T in combinations(sorted(S),k))
    poly=np.poly1d([0])
    iso=[S for k in range(n) for S in combinations(range(2,n+1),k) if all(i+1 not in S for i in S)]
    for S in iso:
        poly=poly+beta(S)*np.poly1d([1,0])**len(S)*np.poly1d([1,1])**(n-2*len(S))
    ranks=[sum(1 for f in F if len(f)==r) for r in range(n+1)]
    return poly, ranks, iso
for q in [2,3,4,10]:
    p,ranks,iso=H(q)
    r=np.roots(p.coeffs)
    print(q, ranks, [int(c) for c in p.coeffs], "nonreal roots:", sum(abs(z.imag)>1e-9 for z in r), "expected", [1,11*q+1,21*q+1,11*q+1,1])
# h-vector q=2
import math
f=[1,7,12,8,2]; n=4
h=np.poly1d([0])
for i in range(n+1): h=h+f[i]*np.poly1d([1,0])**i*np.poly1d([-1,1])**(n-i)
print("h-vector q=2 (h0..h4):", list(reversed([int(round(c)) for c in h.coeffs])))
```

### Computation source: triage.py

Command (working directory `/private/tmp`): `python3 /tmp/op-chow/rework1/scripts/triage.py`; exit 0.
SHA-256: `78dd9f1e32360b0b183424e19bf1b3ffd7b81b4bcf3726cfb05f0b2c6687e48e`.

```python
from itertools import combinations
import numpy as np
import os, sys
_here = os.path.dirname(os.path.abspath(__file__))
_check = sys.argv[1] if len(sys.argv) > 1 else os.path.join(_here, 'check.py')
exec(open(_check).read().split("for q in [2,3,4,10]")[0])
def polys(q,n=4):
    F=faces(q)
    def alpha(T): return flag_alpha(F,T)
    def beta(S): return sum((-1)**(len(S)-len(T))*alpha(T) for k in range(len(S)+1) for T in combinations(sorted(S),k))
    iso=lambda lo,hi:[S for k in range(n+1) for S in combinations(range(lo,hi+1),k) if all(i+1 not in S for i in S)]
    X=np.poly1d([1,0]); O=np.poly1d([1,1])
    H=sum((beta(S)*X**len(S)*O**(n-2*len(S)) for S in iso(2,n)),np.poly1d([0]))
    Ha=sum((beta(S)*X**len(S)*O**(n+1-2*len(S)) for S in iso(1,n)),np.poly1d([0]))
    # dual: beta_{P^*}(S) = beta_{P}(n+1-S)
    Hd=sum((beta(tuple(sorted(n+1-s for s in S)))*X**len(S)*O**(n-2*len(S)) for S in iso(2,n)),np.poly1d([0]))
    return H,Ha,Hd
for q in [1,2,3]:
    for name,p in zip(["H","Haug","Hdual"],polys(q)):
        r=np.roots(p.coeffs); print(q,name,[int(round(c)) for c in p.coeffs],"nonreal:",sum(abs(z.imag)>1e-9 for z in r))
```

Explicit-input command (working directory `/private/tmp`):
`python3 /tmp/op-chow/rework1/scripts/triage.py /tmp/op-chow/rework1/scripts/check.py`; exit 0.

### Computation source: exact.py

Command (working directory `/private/tmp`): `python3 /tmp/op-chow/rework1/scripts/exact.py`; exit 0.
SHA-256: `28e1acddf3808b6618663bbdbe8305b1a9b476031349768d980b152e47b18778`.

```python
from itertools import combinations
import json
import sympy as s
x=s.symbols('x')

def counts(facets):
    faces=set()
    for f in facets:
        for k in range(5): faces.update(map(frozenset,combinations(f,k)))
    def alpha(T):
        if not T: return 1
        count={frozenset():1}
        for rank in sorted(T):
            count={g:sum(c for f,c in count.items() if f<=g)
                   for g in faces if len(g)==rank}
        return sum(count.values())
    def beta(S):
        return sum((-1)**(len(S)-k)*alpha(T)
                   for k in range(len(S)+1) for T in combinations(S,k))
    polynomials={}
    for name,low,aug,dual in [('H',2,0,False),('Haug',1,1,False),('Hdual',2,0,True)]:
        val=0
        for k in range(5):
            for S in combinations(range(low,5),k):
                if any(i+1 in S for i in S): continue
                selected=tuple(sorted(5-i for i in S)) if dual else S
                val+=beta(selected)*x**k*(1+x)**(4+aug-2*k)
        p=s.Poly(s.expand(val),x)
        roots=p.all_roots()
        assert all(z.is_real in (True,False) for z in roots)
        polynomials[name]={'coefficients':[int(v) for v in p.all_coeffs()],
                           'factorization':str(s.factor(p.as_expr())),
                           'nonreal_root_count':sum(z.is_real is False for z in roots)}
    ranks=[sum(len(f)==k for f in faces) for k in range(5)]
    h=s.Poly(s.expand(sum(ranks[i]*x**i*(1-x)**(4-i) for i in range(5))),x)
    return {'ranks':ranks,'h_vector':[int(h.nth(i)) for i in range(5)],
            'beta_24':beta((2,4)),'polynomials':polynomials}

result={}
for q in [1,2,3,4,10]:
    result[str(q)]=counts([(0,3*j+1,3*j+2,3*j+3) for j in range(q)])
    assert result[str(q)]['polynomials']['H']['coefficients']==[1,11*q+1,21*q+1,11*q+1,1]
    assert result[str(q)]['beta_24']==1-q
result['edge']=counts([(0,1,2,3),(0,1,4,5)])
q=s.symbols('q',integer=True)
D=(11*q+1)**2-4*(21*q-1)
assert s.expand(D-(11*q-3)**2)==4*(q-1)
result['family_discriminant_difference']=str(s.expand(D-(11*q-3)**2))
print(json.dumps(result,indent=2))
```

## Triage

### What the settlement shows

**Family — proved by the following paper argument; computed for
$q=2,3,4,10$ by `check.py` and `exact.py`; not a uniform Lean theorem.**
Let $K_q$ have facets $\{0,3j+1,3j+2,3j+3\}$ for $0\le j<q$.
All share just vertex zero. Every partial chain of selected ranks extends
inside the Boolean interval of a containing facet: insert faces at each
missing selected cardinality and retain both endpoints. Thus maximal
chains in the selected subposet have one face at each selected rank,
which justifies using the chain counts below in the literal flag definition.
The flag counts on
$\varnothing,\{2\},\{3\},\{4\},\{2,4\}$ are
$1,6q,4q,q,6q$: every positive-rank face of size at least two belongs to
one facet, and each facet contains six edges. Inclusion–exclusion gives
$1,6q-1,4q-1,q-1,1-q$. Equation (1.1) therefore gives

$$H_q(x)=(1+x)^4+(11q-3)x(1+x)^2+(1-q)x^2
=x^4+(11q+1)x^3+(21q+1)x^2+(11q+1)x+1.$$

Write $A=11q+1$ and $D=A^2-4(21q-1)$. Then
$a=(A-\sqrt D)/2$ and $b=(A+\sqrt D)/2$ satisfy
$a+b=A$, $ab=21q-1$ and
$H_q=(x^2+ax+1)(x^2+bx+1)$.
For every integer $q\ge2$, $D-(11q-3)^2=4(q-1)>0$ and
$D<A^2$. Consequently $0<a<2$, so $x^2+ax+1$ has two non-real
zeros. This algebraic derivation proves the uniform mathematical statement;
the kernel-checked scope of this module is the single witness $q=2$.
The computed coefficient vectors are $[1,23,43,23,1]$,
$[1,34,64,34,1]$, $[1,45,85,45,1]$ and $[1,111,211,111,1]$,
respectively, each with two non-real roots.

**Mechanism — proved in the module at $q=2$; proved by the paper
calculation for the family; computed by the three scripts on their stated
samples.** The negative isolated flag entry is
$\beta(\{2,4\})=1-q$. At $q=2$ it is $-1$ (private `beta24_card`);
the rank counts are $(1,7,12,8,2)$ and the h-vector is
$(1,3,-3,1,0)$, computed by `exact.py`. The h-vector is defined by
$\sum_{i=0}^4 f_{i-1}t^i(1-t)^{4-i}$.
For $q=1$, `exact.py` gives h-vector $(1,0,0,0,0)$ and
$H_1=(x+1)^2(x^2+10x+1)$: $a=2$ is precisely the real-rooted
boundary. Gluing the second simplex at the common vertex makes $a<2$;
private `a_bounds`, `H_P2_root` and `z_im_ne` prove that departure at $q=2$.
`triage.py` reports two numerical non-real roots for $H_1$ at tolerance
$10^{-9}$; its exact polynomial has the repeated real root $-1$.
That numerical count is not an exact classification. `check.py` omits the
trailing zero h-coordinate; `exact.py` computes all five coordinates.

**Surviving assertions — computed, with exact confirmation.**
For $q=1,2,3$, `triage.py` and `exact.py` give zero non-real roots for
both the augmented polynomial (1.2) and the dual polynomial (rank reversal
$\beta_{\widehat P^*}(S)=\beta_{\widehat P}(5-S)$).

| $q$ | augmented coefficients, descending | dual coefficients, descending | non-real roots in each |
| --- | --- | --- | --- |
| 1 | $[1,16,48,48,16,1]$ | $[1,15,33,15,1]$ | 0 |
| 2 | $[1,30,94,94,30,1]$ | $[1,28,64,28,1]$ | 0 |
| 3 | $[1,44,140,140,44,1]$ | $[1,41,95,41,1]$ | 0 |

`exact.py` additionally confirms these two root properties for $q=4,10$.
**Open:** a uniform Lean proof for this family and unconditional
real-rootedness of $H^{\rm aug}$ and $H^*$ for every simplicial poset.
**Proved as a logical consequence of the refutation:** the proposed
real-rooted interlacing assertion involving $H$ cannot hold for $P_2$,
because $H$ is not real-rooted. No separate augmented-versus-dual
interlacing statement is proved here.

**Two tetrahedra sharing an edge — computed by `exact.py`.**
Facets $\{0,1,2,3\}$ and $\{0,1,4,5\}$ give rank counts
$(1,6,11,8,2)$, h-vector $(1,2,-1,0,0)$ and
$H=(x+1)^2(x^2+20x+1)$, with zero non-real roots. This negative-h
example is real-rooted, so negative h-coordinates alone do not force
failure. The classification of other gluings remains open.

**Sharpness and source consequences — proved by the witness and a
paper argument.** The source's positive-h-vector hypothesis cannot be
dropped even for connected cones: each facet of $K_2$ contains vertex
zero, making the complex a connected cone, and the module refutes its
unconditional real-rootedness. Theorems 1.1–1.2 keep their positive-h
hypothesis; this example does not contradict them. Those source theorems
state the positive-h results and are not on this module's dependency path.
The complete Conjecture 1.5 is refuted; separate unconditional augmented
and dual conjectures remain open. Consequences using the full conjecture
require additional hypotheses or an independent proof.

## ASSUMED-UNVERIFIED

Literature absence beyond the preregistration's checked scope is not
verified. The family derivation, cone observation, h-vectors and neighbouring
polynomials are not claimed as additional Lean declarations. Finite exact
samples do not prove the open uniform augmented or dual assertions.
Information-escape registration is paused under CLAUDE.md §3.9.
