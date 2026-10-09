---
slug: rico-zyczkowski-2024-nonlinear-majorization-monotone
bibkey: ricozyczkowski2024measurements
doi: 10.1088/1751-8121/ad7dc2
url: https://arxiv.org/abs/2308.05835v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Measurements/RicoZyczkowskiMonotoneRefutation.result
---

# A commuting obstruction to the nonlinear measurement monotone

## Problem

A. Rico and K. Życzkowski, *Discrete dynamics in the set of quantum
measurements*, J. Phys. A 57 (2024) 435302, arXiv:2308.05835v2,
Appendix C.1, Conjecture 1, asks whether blockwise bistochastic dynamics
preserve the centered-prefix Hilbert–Schmidt norm in the following sense:

> Let $P\in\Delta_{n,d}$ and $Q\in\Delta_{n,d}$ be blockwise probability
> vectors. If there exists a blockwise bistochastsic matrix $B\in B_{n,d}$
> such that $Q=B\ast P$, then for any ordering of $\{Q_i\}$ there exists
> an ordering of $\{P_i\}$ such that
> $\left\|\sum_{i=1}^{k}(P_i-1/n)\right\|_2\geq
> \left\|\sum_{i=1}^{k}(Q_i-1/n)\right\|_2$
> for all $1\leq k\leq n$, where
> $\|A\|_2=\sqrt{\operatorname{tr}(A^\dagger A)}$ is the 2-norm.

Definitions 1, 3 (Eq. (19)) and 5 give positive semidefinite effects
summing to $I_d$, positive semidefinite blocks with $d\geq2$ and both
block row and column sums $I_d$, and the principal-square-root product
$Q_i=\sum_j\sqrt{P_j}B_{ij}\sqrt{P_j}$. Here $1/n$ in the centered
prefix denotes $(1/n)I_d$. Issue #14670 preregisters this tier-1 question.

## Motivation

The frozen declaration
`D5/S3/Quantum/Measurements/RicoZyczkowskiMonotoneRefutation.result`
proves `¬ claim`. A three-outcome, two-dimensional diagonal measurement
is sufficient to refute the universally quantified assertion.

## Gap

Issue #14670 records the source, MathDB p/359456, arXiv searches and
later-paper readings. No settlement was found in that searched scope.
This bounded literature reading does not establish exhaustive priority.
Appendix C.2 settles the two-outcome restriction rather than the full
conjecture.

## Route

Using zero-based indices, the formal witness is

$$P_0=\operatorname{diag}(5/12,1/6),\qquad
P_1=\operatorname{diag}(1/6,5/12),\qquad
P_2=\operatorname{diag}(5/12,5/12).$$

On coordinate zero let $\rho_0$ exchange outcomes zero and one; on
coordinate one let $\rho_1$ be the identity. Set

$$B_{ij}=\operatorname{diag}\left(
\frac9{10}\mathbf1_{j=\rho_0(i)}+\frac1{30},
\frac9{10}\mathbf1_{j=\rho_1(i)}+\frac1{30}\right).$$

The diagonal positive semidefinite roots give

$$Q_0=\operatorname{diag}(11/60,11/60),\qquad
Q_1=Q_2=\operatorname{diag}(49/120,49/120).$$

Every input effect satisfies $\|P_j-I_2/3\|_2^2\leq5/144$, while
$\|Q_0-I_2/3\|_2^2=9/200>5/144$. Thus the output ordering beginning
with $Q_0$ violates the inequality at $k=1$ for every input permutation.

## Falsifier

The witness satisfies both POVM conditions, both bistochastic identity
resolutions and the literal principal-square-root product. All blocks
commute. The failure is independent of the input ordering; it does not
replace the existential input permutation with a fixed permutation.

## Evidence

The canonical module is
`D5/S3/Quantum/Measurements/RicoZyczkowskiMonotoneRefutation.lean`.
Its public definitions are `BlockBistoch`, `IsBlockProduct`, `hs` and
`claim`; its only public theorem is `result : ¬ claim`. It reuses the
frozen `IsPOVM` predicate. Private facts `P_prob`, `Q_prob`, `B_bistoch`,
`block_product`, `P_hs_sq`, `Q_hs_sq` and `prefix_one` supply the formal
witness and comparison used by `result`. The axiom closure of every
public declaration is contained in {`propext`, `Classical.choice`,
`Quot.sound`}.

## Triage

Resolution: Refuted. `proof_shape: result: bind-only`;
`escape_witness: none`;
`admission_basis: open-problem-resolution (#14670; Refuted)`.
The fixed numerical certificates have utility `kind=certified-instance`
under `refutes`, with the literal types `claim : Prop` and
`result : ¬ claim`.

### What the settlement shows

- **Proved in this module:** the $n=3,d=2$ witness satisfies the source's
  assumptions and violates $k=1$ for every input ordering. Evidence:
  the private witness facts and the kernel-checked theorem `result`.
- **Computed, with a paper proof of the all-size family:** for every
  $n\geq3,d\geq2,0<a<1/n$ and $\sqrt{5/8}<t<1$, the construction below
  violates $k=1$. The exact checker covers only the 110 cases
  $3\leq n\leq12$, $2\leq d\leq12$, with $a=1/(2n)$ and $t=9/10$.
  Uniform Lean verification of this family is open.
- **Proved by the paper argument below (mechanism):** diagonal dynamics
  is one scalar bistochastic matrix per coordinate. Classical
  majorization holds separately on each coordinate. Different coordinate
  permutations align the negative deviations in a single output effect,
  defeating every common input ordering. The finite instance is also
  kernel checked through `block_product` and `result`.
- **Proved in the source or classical theory (boundary cases):**
  Appendix C.2 proves $n=2$ for the source's matrix dynamics. At
  $d=1$ the dynamics becomes scalar bistochastic dynamics, and classical
  majorization holds with conventional decreasing orderings. This
  classical sorted-prefix conclusion does not by itself establish an
  arbitrary-output-order absolute-prefix conclusion. The scalar
  absolute-prefix extension is not claimed here. These boundary results
  are literature evidence, not new Lean theorems; $d=1$ is outside
  `BlockBistoch`'s literal $d\geq2$ domain.
- **Open (surviving restrictions):** whether the inequality holds for
  coordinate-independent dynamics $B_{ij}=b_{ij}I_d$, or for an adjusted
  conclusion allowing orderings chosen separately per coordinate.
  The present coordinate-dependent, common-ordering obstruction does
  not settle either restriction.
- **Literature boundary for other source results:** Theorems 2 and 3
  address linear monotones for sortable measurements. This witness
  refutes the unrestricted nonlinear Conjecture 1 and gives no
  refutation of those sortable-measurement theorems. Any conclusion
  requiring Conjecture 1 as an unconditional hypothesis lacks that
  hypothesis; no such conclusion is exported by this module.

### All-size construction and paper proof

Put $c=1/n$. The first two diagonal coordinates of the first three
input effects are $(c+a/2,c-a)$, $(c-a,c+a/2)$ and $(c+a/2,c+a/2)$.
Every remaining entry is $c$. Each coordinate sums to one, and every
entry is positive because $0<a<c$. Let $\rho_0$ swap outcomes zero and
one, and let every other $\rho_r$ be the identity. Define

$$B_{ij}^{(r)}=t\mathbf1_{j=\rho_r(i)}+(1-t)c.$$

Each coordinate matrix is bistochastic and every entry is strictly
positive for $0<t<1$. Hence its diagonal blocks are positive definite
and both block resolutions equal $I_d$. Commutation gives
$\sqrt{P_j}B_{ij}\sqrt{P_j}=P_jB_{ij}$, so
$Q_i^{(r)}=tP_{\rho_r(i)}^{(r)}+(1-t)c$.
In particular, the centered first output has coordinates
$(-ta,-ta,0,\ldots,0)$. The centered squared input norms are
$5a^2/4$, $5a^2/4$, $a^2/2$ and zero for all remaining effects.
Thus

$$\|Q_0-cI_d\|_2^2=2t^2a^2>\frac54a^2
=\max_j\|P_j-cI_d\|_2^2,$$

where the strict inequality is exactly $t>\sqrt{5/8}$. This proves
failure at the first prefix for all the stated parameters on paper.
It also explains why the commuting setting does not force a common
permutation across coordinates.

### Exact computation

Command: `python3 /tmp/op-rz/check.py`; exit code: 0.
Script SHA-256: `02876a92308857348a8f3ed9d4b4896cf9acb436efbbe757ba17ab401043060b`.
The exact-rational result is $Q_0=(11/60,11/60)$,
$\max_j\|P_j-I_2/3\|_2^2=5/144$,
$\|Q_0-I_2/3\|_2^2=9/200$ and gap $37/3600$.
All 110 stated finite cases violate the first-prefix inequality.
The complete script source follows; save it as `check.py` and run
`python3 check.py` to reproduce the same scope.

```python
from fractions import Fraction as F
from itertools import permutations
def family(n,d,a,t):
    c=F(1,n)
    P=[[c]*d for _ in range(n)]
    P[0][0]=c+a/2; P[0][1]=c-a
    P[1][0]=c-a;   P[1][1]=c+a/2
    P[2][0]=c+a/2; P[2][1]=c+a/2
    # remaining effects absorb: coordinates sum check
    for k in range(d):
        s=sum(P[i][k] for i in range(n)); assert s==1,(n,d,k,s)
    # B0: coordinate 0 swaps outcomes 0,1; identity elsewhere; B_t = t B0 + (1-t) J/n
    def B(i,j,k):
        perm = (1 if (k==0 and {i,j}=={0,1}) else 0) if (k==0 and (i in (0,1) or j in (0,1))) and i!=j else (1 if i==j and not (k==0 and i in (0,1)) else 0)
        return t*perm + (1-t)*c
    for k in range(d):
        for i in range(n):
            assert sum(B(i,j,k) for j in range(n))==1 and sum(B(j,i,k) for j in range(n))==1
            for j in range(n): assert B(i,j,k)>0
    # diagonal commuting: sqrt(P_j) B_ij sqrt(P_j) = P_j B_ij entrywise
    Q=[[sum(P[j][k]*B(i,j,k) for j in range(n)) for k in range(d)] for i in range(n)]
    dev=lambda X: sum((x-c)**2 for x in X)
    return P,Q,max(dev(p) for p in P),dev(Q[0])
P,Q,mp,q0=family(3,2,F(1,6),F(9,10))
print("n=3 d=2 Q1:",Q[0],"maxP dev",mp,"Q1 dev",q0,"violation",q0>mp, "gap", q0-mp)
bad=0
for n in range(3,13):
    for d in range(2,13):
        a=F(1,2*n); t=F(9,10)
        P,Q,mp,q0=family(n,d,a,t)
        bad+= (q0>mp)
print("violations over 3<=n<=12, 2<=d<=12:", bad, "of", 10*11)
```

## ASSUMED-UNVERIFIED

The bounded literature absence, bibliographic metadata and boundary
results are external evidence. Only the concrete refutation is verified
by this Lean module; the all-size parameter family is proved on paper
and finitely checked, without a uniform Lean theorem. The two surviving
restrictions remain open.

Information-escape registration is paused under CLAUDE.md §3.9.
