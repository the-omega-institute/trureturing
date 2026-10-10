---
slug: lee-2026-reduction-operator-invertibility
bibkey: lee2026longrangeswap
doi: 10.1088/1742-5468/ae80b5
url: https://arxiv.org/abs/2604.12136v1
triage: theorem
motivation_gids:
  - D5/S3/StatisticalMechanics/LongRangeSwap/LeeReductionInvertibility.result
---

## Problem

Eunghyun Lee, *Integrability of multispecies long-range swap models with
species-dependent interpolation*, arXiv:2604.12136v1, Remark 3.1 after
Equation (28), source label `1122am331`, conjectures:

> These results lead us to conjecture that $\mathfrak A_k$ is invertible for all parameters $\mu_i \in [0,1]$.

LEE-A is preregistered in [#14343](https://github.com/the-omega-institute/trureturing/issues/14343).
For every $N\ge1$, $n\ge2$, $j\ge1$, $k\ge0$ with $j+k+1\le n$ and
$\mu\in[0,1]^N$, the literal recursion
$\mathfrak A_0=I$,
$\mathfrak A_k=I-\mathcal B_{k+1}\mathfrak A_{k-1}^{-1}\mathcal B'_k$
has invertible matrices on words $\operatorname{Fin}(n)\to\operatorname{Fin}(N)$.

## Motivation

The source's Proposition 2.2, “Integrability under invertibility”, uses these
operators to reduce the model to two-particle interactions. The source's
Yang–Baxter result then supplies integrability. The frozen motivation
`LeeReductionInvertibility.result` proves LEE-A on the entire closed parameter cube.

## Gap

The source's Section 2.3 calls invertibility for arbitrary species compositions
in the interior parameter regime open. The scalar spectral-radius experiments
in Remark 3.1 do not establish the general assertion. Literature readings in
#14343 report only arXiv v1, no OpenAlex citations, and no MathDB matching
settlement; exhaustive absence of another published proof is ASSUMED-UNVERIFIED.

## Route

Use the extended walk on block positions $0,\ldots,m+1$, with absorbing
boundary rows. Each interior row has nonnegative outgoing $B,B'$ masses
summing to one. Its interior restriction is substochastic. A deterministic
choice of positive-weight edges reaches the boundary in at most $2Nm$ steps.
The general attained-maximum principle forces every zero-boundary harmonic
chain to vanish. Backward extension through the earlier invertible pivots
and strong induction give invertibility of every pivot; those pivots equal
the literal $\mathfrak A_k$ recursion.

## Falsifier

A counterexample would be valid $N,n,j,k,\mu$ with
$\det(\mathfrak A_k)=0$. `result : claim` proves that no such counterexample
exists in the stated real matrix model. The finite computation below is an
independent consistency check, not the proof of the unbounded statement.

## Evidence

Kernel evidence: `D5.S3.StatisticalMechanics.LongRangeSwap.LeeReductionInvertibility.result`.
Its live proof uses `pivots_isUnit`, `extend`, `harmonic_chain_zero`,
`LeeCollisionExit.Path.exits`, and
`FiniteBinaryDirichletMaximum.maximum_zero_of_two_successor_exit`.
The axiom closure of every public declaration is contained in
$\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.
Source definitions $B,B'$ are Equation (7), label `138am42`, and the
adjacent word-coordinate operators are Lemma 3.4, Equation (26).
Information-escape registration is paused under CLAUDE.md §3.9.

## Triage

### What the settlement shows

- **Proved — mechanism.** `Path.exits` constructs an exit of length at most
  $2Nm$ with positive product of the chosen weights. Its private rank proof
  uses `minimum_nonincreasing` and `direction_constant_minimum`: the minimum
  collision label never increases, and a constant minimum allows at most one
  reversal. This applies to the closed cube, including binary parameters.
  `harmonic_chain_zero` consumes the attained-maximum principle and this
  path. `extend` and `pivots_isUnit` construct and certify the Gaussian
  elimination pivots, and `result` identifies them with $\mathfrak A_k$.
  These are kernel-checked declarations. `Path.exits` itself permits every
  real parameter vector; the nonnegative two-mass maximum principle uses
  the closed cube. The general maximum theorem permits any state type with
  an attained uniform bound, without a finiteness assumption. Invertibility
  outside the closed cube is open here. Finite-dimensional injectivity
  of the corresponding zero-boundary block system implies its invertibility
  (paper argument from this proved uniqueness); a separate block-matrix
  representation theorem is not delivered.
- **Proved — consequence by paper argument.** Combining LEE-A with the
  source's Proposition 2.2, “Integrability under invertibility”, removes its
  invertibility condition for arbitrary species compositions and
  $\mu_i\in[0,1]$. The reduction to two-particle interactions and the source's
  Yang–Baxter theorem therefore give general integrability. This consequence
  uses the published proposition and theorem; the stochastic model and
  Yang–Baxter conclusion are not themselves formalized here.
- **Open — spectral-radius extension.** Remark 3.1 reports
  $\rho(\mathcal B_{k+1}\mathfrak A_{k-1}^{-1}\mathcal B'_k)<1$ for
  $N=n\le4$. That is the source's numerical observation, not a computation
  reproduced here. The strict inequality for general $N,n$ remains open;
  invertibility is proved without this bound.
- **Computed — exact-rational determinants.** Command
  `/usr/bin/time -l python3 /tmp/op-lee/exact_check.py` exited 0. The scope is
  $N=1,2,3$, $n=2,3$, all valid $j,k$, and
  $\mu\in\{0,1/3,1/2,1\}^N$: 336 samples, all determinants nonzero.
  SymPy determinants agree exactly with independent Fraction Gaussian
  determinants. This finite grid does not certify other parameter values;
  the uniform extension is instead proved by `result`.

### Exact-rational computation source

Requires Python 3 and SymPy. Save the following bytes as `exact_check.py`,
create `/tmp/op-lee`, and run the command above.
Script SHA-256: `f53510c2c2c1e05ca0867c3349c41079545eb64f4fa8dbfdd59346fd8ddc83d9`.
Result-data SHA-256: `44ff07994aae4ce51d681ca26bf4dbac52cf03dffc063b668a2336468f4489ab`.

```python
from itertools import product
from fractions import Fraction
from pathlib import Path
from hashlib import sha256
import json,sympy as S

def local(pi,nu,mu,prime=False):
 if pi==nu and nu[0]==nu[1]:return 1-mu[nu[0]] if prime else mu[nu[0]]
 if pi==(nu[1],nu[0]) and (nu[1]<nu[0] if prime else nu[0]<nu[1]):return S.Integer(1)
 return S.Integer(0)
def adjacent(words,s,mu,prime=False):
 return S.Matrix([[local(pi[s:s+2],nu[s:s+2],mu,prime) if all(pi[r]==nu[r] for r in range(len(pi)) if r not in (s,s+1)) else 0 for nu in words] for pi in words])
def check():
 readings=[]
 grid=[S.Rational(0),S.Rational(1,3),S.Rational(1,2),S.Rational(1)]
 for N in range(1,4):
  for n in range(2,4):
   words=list(product(range(N),repeat=n));eye=S.eye(len(words))
   for mu in product(grid,repeat=N):
    for j in range(1,n):
     a=eye
     for k in range(n-j):
      if k:a=eye-adjacent(words,j+k-1,mu)*a.inv()*adjacent(words,j+k-2,mu,True)
      det=a.det(method='domain-ge')
      # independent Fraction Gaussian determinant, no SymPy determinant calls
      q=[[Fraction(int(x.p),int(x.q)) for x in row] for row in a.tolist()]
      independent=Fraction(1)
      for i in range(len(q)):
       pivot=next((r for r in range(i,len(q)) if q[r][i]),None)
       if pivot is None:independent=Fraction(0);break
       if pivot!=i:q[i],q[pivot]=q[pivot],q[i];independent=-independent
       d=q[i][i];independent*=d
       for r in range(i+1,len(q)):
        c=q[r][i]/d
        for s in range(i+1,len(q)):q[r][s]-=c*q[i][s]
        q[r][i]=0
      assert independent==Fraction(int(det.p),int(det.q)),(N,n,j,k,mu,det,independent)
      readings.append({'N':N,'n':n,'j':j,'k':k,'mu':list(map(str,mu)),'det':str(det),'independent_det':str(independent)})
      if det==0:raise AssertionError(readings[-1])
 p=Path('/tmp/op-lee/exact-results.json');p.write_text(json.dumps(readings,indent=2))
 print(json.dumps({'samples':len(readings),'all_nonzero':True,'grid':list(map(str,grid)),'data':str(p),'sha256':sha256(p.read_bytes()).hexdigest()}))
if __name__=='__main__':check()
```

## ASSUMED-UNVERIFIED

The literature search does not prove exhaustive publication-level novelty.
The accessible arXiv text and Crossref metadata support the source locator;
no claim is made to have verified an inaccessible journal PDF. The paper-level
integrability consequence is separate from the kernel-checked matrix result.
