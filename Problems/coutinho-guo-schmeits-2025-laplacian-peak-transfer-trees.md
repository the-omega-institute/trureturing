---
slug: coutinho-guo-schmeits-2025-laplacian-peak-transfer-trees
bibkey: coutinho2025peak
doi: 10.48550/arXiv.2505.11986
url: https://arxiv.org/abs/2505.11986v4
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Dynamics/LaplacianPeakTransferTrees.result
---

# Infinitely many non-star trees admit Laplacian peak state transfer

## Problem

Gabriel Coutinho, Krystal Guo and Vincent Schmeits, *Peak state transfer in
continuous quantum walks*, arXiv:2505.11986v4, Section 7, Open Problem 7.1
(p. 21), ask:

> Determine whether infinitely many such trees, not isomorphic to the star graph, admit Laplacian peak state transfer.

Figure 10 (p. 22) includes a root with three hubs and two leaves per hub.
For the real Laplacian $L=D-A=\sum_\theta\theta E_\theta$, Section 3 defines
$U(t)=e^{itL}$ and $B(L)=\sum_\theta|E_\theta|$, summing over distinct
eigenvalues and taking absolute values entrywise. Peak transfer between
distinct vertices $r,h$ means $|U(\tau)_{h,r}|=B(L)_{h,r}$ at some real time.
The source does not require that value to equal one.

## Motivation

**Proved:** `D5/S3/Quantum/Dynamics/LaplacianPeakTransferTrees.result`
proves `claim`: arbitrarily large finite trees, excluded from every star
isomorphism class $K_{1,m}$, have distinct vertices with Laplacian peak
transfer. Preregistration [#14801](https://github.com/the-omega-institute/trureturing/issues/14801)
names this settlement LPST-1. The settling Scribe node records
`OpenProblemResolutionClaim` with resolution `Proved`.

## Gap

The source supplies stars and one small non-star example, rather than an
unbounded family. Arbitrarily large orders in the Lean conclusion imply
infinitely many isomorphism classes. The claim includes all natural lower
bounds, connectedness and acyclicity, exclusion of every $K_{1,m}$, and the
source's spectral bound and exponential conventions.

## Route

For a positive odd natural number $s$, put
$\ell=s(s+1)$, $k=\ell+1$, and $n=1+k(\ell+1)=1+k^2$.
Join a root to $k$ hubs, and each hub to $\ell$ leaves.
The degrees are $k,\ell+1,1$; connectedness and $n-1$ edges prove that this
is a tree. Both the root and a hub have degree at least two, excluding a
star. Relabelling gives a graph on `Fin n`.

On vectors constant on the root, hubs and leaves, the Laplacian acts by

$$
Q=\begin{pmatrix}k&-k&0\\-1&\ell+1&-\ell\\0&-1&1\end{pmatrix}.
$$

Its relevant eigenvalues are $0$, $a=s^2+1$ and $b=(s+1)^2+1$.
The explicit eigenvectors have cell values
$w_0=(1,1,1)$, $w_a=(-ks,-s^2,1)$ and
$w_b=(k(s+1),-(s+1)^2,1)$, and

$$
e_r=\frac{w_0}{ab}-\frac{w_a}{a(b-a)}+\frac{w_b}{b(b-a)}.
$$

The root-to-hub projection entries are
$1/(ab)$, $(a-1)/(a(b-a))$ and $-(b-1)/(b(b-a))$.
For odd $s$, the three phases at $\pi$ are $1,1,-1$, so all contributions
to $U(\pi)_{h,r}$ have the same phase. This realizes the alignment criterion
described in the source's Lemma 5.2.

The private declarations `root_decomposition` and `phases` and their
consumers lead to `tree_peak`; `result` takes $s=2N+1$ for every lower bound
$N$. The frozen `EnergyEigenstateStationarity.exp_mulVec_of_eigenvector`
is used by `real_eigenvector_exp` for the matrix exponential action.
`lapPropagator` uses `ProjectionProbabilityFlow.hamiltonianPropagator`
at $-\tau$; `RationalWeightPathTransfer.hamiltonianPropagator_neg` supplies
the private conversion to the source expression $\exp(i\tau L)$ in
`root_evolution`.

## Falsifier

The settlement would fail its stated criterion if the public spectral or
exponential definitions differed from Section 3, an odd positive parameter
failed to attain the bound, or the preregistration's literature scope
already contained a settlement. The Lean definitions follow the binding
conventions of #14801; `result : claim` carries no additional hypotheses.
Numerical samples support the construction but do not replace its proof.

## Evidence

The kernel evidence is the settling module and its Scribe. Every theorem
and lemma, including `result`, has proof shape `bind-only` after inlining:
the root decomposition uses rational normalization, the phases use parity
and exponential identities, and their consumers apply frozen or Mathlib
facts and normalize. No escape witness survives the bypass test. Admission
is `open-problem-resolution` (#14801; Proved). Utility is
`none`: the result and helpers concern symbolic parameters and unbounded
orders, with no fixed numerical certificate, finite enumeration, executable
checker or numeric-reduction declaration.

The escape registration of `result` is `DTR-Declared` with
`declared_validated` at
`Reg/D5/S3/Quantum/Dynamics/LaplacianPeakTransferTrees.lean`.
The compiled registration selects the graph operand of `IsTree` through
the enrolled `DependentFamily` template, with a source-equivalence bridge
and open continuation. `.unknown` marks an unknown residual and proves no
undecidability or inexhaustibility.

Experiment entry:
[trureturing-experiments@602ec65402d492351ebc19230b04caa93001cda8, numerical check](https://github.com/the-omega-institute/trureturing-experiments/tree/602ec65402d492351ebc19230b04caa93001cda8/docs/reports/coutinho-guo-schmeits-2025-laplacian-peak-transfer-trees).
The entry's `check.py` has SHA-256
`64d43c273db0a1935d94840271e9795b5937df9fb5283f8e687546b813c90542`.
Command:
`OPENBLAS_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 python3 /Users/auric/trureturing-experiments/docs/reports/coutinho-guo-schmeits-2025-laplacian-peak-transfer-trees/check.py`.
Exit code: 0. The full Laplacian is tested for $s=1,2,3,4,5$ at $\pi$;
the even cases additionally use 2001 equally spaced times in $[0,2\pi]$.
Eigenvalue grouping tolerance is $10^{-7}$.

| $s$ | $n$ | distinct eigenvalues | $B(L)_{h,r}$ | $\lvert U(\pi)_{h,r}\rvert$ |
| --- | --- | --- | --- | --- |
| 1 | 10 | 6 | 0.533333333333 | 0.533333333333 |
| 2 | 50 | 6 | 0.360000000000 | 0.320000000000 |
| 3 | 170 | 6 | 0.268907563025 | 0.268907563025 |
| 4 | 442 | 6 | 0.213675213675 | 0.209150326797 |
| 5 | 962 | 6 | 0.176904176904 | 0.176904176904 |

The odd-case absolute discrepancies are respectively
$4.44\cdot10^{-16}$, $5.55\cdot10^{-17}$ and $2.78\cdot10^{-17}$.
The grid maxima for $s=2,4$ are respectively
$0.3200000000000002$ and $0.21356574055583671$.
These are floating-point readings over the stated finite scope.

## Triage

### What the settlement shows

- **Proved, kernel:** `lap_cell` gives the invariant cell-constant
  subspace. `w0_eigen`, `wa_eigen` and `wb_eigen` give eigenvalues
  $0,a=s^2+1,b=(s+1)^2+1$. `root_decomposition` places $e_r$ in their span.
- **Proved, kernel and algebraic argument:** `hub_projection` gives the
  coefficients $1/(ab)$, $(a-1)/(a(b-a))$, $-(b-1)/(b(b-a))$.
  For $s\ge1$, $a,b,b-a$ and both numerators are positive; the signs are
  therefore $+,+,-$. The kernel helper bounds the latter magnitudes
  nonnegatively; strict positivity follows from $s^2>0$ and $(s+1)^2>0$.
- **Proved, kernel:** `phases` gives $1,1,-1$ for odd $s$ at $\pi$;
  `tree_peak` proves attainment of the triangle bound at that time.
- **Proved, kernel and algebraic argument:** `tree_bound` gives
  $B(L)_{h,r}=1/n+(a-1)/(a(b-a))+(b-1)/(b(b-a))$.
  Since $n=ab$, simplifying yields
  $B(L)_{h,r}=2(s+1)^2/(((s+1)^2+1)(2s+1))$.
  Moreover $0<B(L)_{h,r}\le2/(2s+1)\to0$ as $s\to\infty$.
  The Section 3 triangle bound thus bounds the root-to-hub transfer
  probability by $B(L)_{h,r}^2\to0$: this family has no uniform positive
  root-to-hub transfer probability. This does not rule out other vertex
  pairs or other families. The defining root-hub edge makes the transfer
  distance exactly one; these limit and distance conclusions are
  mathematical arguments here, not additional public Lean theorems.
- **Computed:** for $s=2,4$, the experiment entry in Evidence gives gaps
  at $\pi$ of $0.04$ and approximately $0.004524886878$, and grid maxima
  $0.3200000000000002<0.36000000000000076$ and
  $0.21356574055583671<0.21367521367521503$. The computed non-attainment
  applies only to $\pi$ and the stated grid, not to every real time or
  every even parameter.
- **Open:** an infinite non-star tree family with Laplacian peak transfer
  at distance at least two; no such conclusion is in `result`.
- **Open:** an infinite non-star tree family with peak-transfer
  probability bounded below by a common positive constant.
- **Open:** classification of Laplacian peak state transfer in trees.
- **Open:** the source's adjacency-dynamics question on trees.

**Proved:** the order $1+(s(s+1)+1)^2$ strictly increases, by
`order_strictMono`. The first member is the source's 10-vertex example;
`treeFin_isTree` and `treeFin_not_star` certify all positive parameters
as non-star trees. Odd positive parameters give the unbounded peak-transfer
family, settling the named infinitude question. The source's bounding
matrix and phase criterion keep their stated scope; the other questions
listed above receive no settlement from this result. Uniform attainment
or non-attainment for even parameters is **open** beyond the finite
computed scope.

## ASSUMED-UNVERIFIED

Literature currency beyond the arXiv and MathDB scope recorded in #14801
is unverified by this implementation seat. The preregistration supplies
the source and literature attestation; no broader novelty claim is made.
The four-slot escape registration is `DTR-Declared` with
`declared_validated`, a source-equivalence bridge and open continuation;
`.unknown` marks an unknown residual and proves no undecidability or
inexhaustibility.
