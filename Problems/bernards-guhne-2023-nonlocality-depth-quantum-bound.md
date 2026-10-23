---
slug: bernards-guhne-2023-nonlocality-depth-quantum-bound
bibkey: bernards2023nonlocalitydepth
doi: 10.1103/PhysRevA.107.022412
url: https://arxiv.org/abs/2205.04250v2
triage: theorem
motivation_gids:
  - D5/S3/QuantumBounds/NonlocalityDepthQuantumBound.result
---

# Exact quantum bound of the Bernards–Gühne nonlocality-depth family

## Problem

F. Bernards and O. Gühne, *Bell inequalities for nonlocality depth*,
arXiv:2205.04250v2, Phys. Rev. A 107, 022412, Section III.F, Eqs. (28)–(29),
define the permutation-symmetric Bell functional

$$F_n=\sum_{\ell=1}^n(-1)^{1+\lceil\ell/2\rceil}\ell
(1\ldots1\,2\ldots2).$$

The bracket sums distinct party permutations, with $n-\ell$ settings 1
and $\ell$ settings 2. The source states:

> In the following, we discuss numerical findings concerning the Bell inequalities F_n for n ≤ 8 parties. We find, that the quantum bound of the inequalities is F_n = √2 n 2^{n−2} (29) up to numerical precision, which is achieved by choosing A₁ = B₁ = … = σ_x and A₂ = B₂ = … = σ_z

For every integer $n\ge3$, the maximum over all finite local dimensions,
binary observables and density matrices is exactly
$Q_n=\sqrt2\,n2^{n-2}$. This is a uniform extension and proof of the numerical
finding; the source does not state a general-$n$ conjecture.
The preregistration is [#16626](https://github.com/the-omega-institute/trureturing/issues/16626).

### Statement echo

| Source clause | Lean counterpart | Scope |
| --- | --- | --- |
| Every party number $n\ge3$ | `claim`, quantified `n` and lower bound | All such natural numbers |
| Finite local dimensions | `d`, local carriers `Fin (d j)` | Arbitrary finite dimensions, including empty carriers |
| Two binary measurements at each party | `A j s`, literal Hermitian and shift conditions | Hermitian matrices with both shifts positive semidefinite; general binary POVMs |
| Full correlators and distinct party permutations | Entrywise product in `bellOp`, Boolean setting strings | Entrywise tensor product; Hamming weight supplies the coefficient and multiplicity |
| Arbitrary states | Positive semidefinite `ρ` with trace one in `claim` | Literal body of the existing `GHZMeasureBiseparableBound.IsDensity`; no duplicate predicate |
| Exact quantum maximum | `IsGreatest` in `claim`; `result` | Universal upper bound and attained value |
| Source's X/Z optimum | X/Y phase-adjusted GHZ realization in `result` | Equivalent local measurement plane; the explicit X/Z conjugation is a prose identification |
| Shift and involution hypotheses of the auxiliary estimate | `Upper.unweighted_bound` | Auxiliary inputs discharged by dilation and party decomposition inside `result`; no extra assumption in `claim` |

## Motivation

The settling declaration is `D5/S3/QuantumBounds/NonlocalityDepthQuantumBound.result`.
Its admission basis is `escape-witness`; the witness is
`Upper.unweighted_bound`, the shifted all-party positive-semidefinite estimate.
The source's two-cell classical bound has a separate owner,
`HybridMerminDepthBound.result`; it is a different maximum.

## Gap

Eq. (29) reports numerical optimization through eight parties. The missing
statement is a dimension-independent upper bound with exact attainment for
every $n\ge3$. The general-$n$ extension is admitted through its mathematical
escape witness, rather than through author-stated-open-problem admission.

## Route

Write $c_h=(-1)^{1+\lceil h/2\rceil}$. The identity $c_{h+2}=-c_h$
makes the two-party unweighted polynomial a signed CHSH operator.
`Block.signed_bound` applies pinned Mathlib `tsirelson_inequality`.
`Upper.unweighted_bound` propagates that estimate through arbitrarily many
parties by a positive spectator certificate. Its conclusion holds for all
natural phase shifts and arbitrary finite local carriers.

Distributing Hamming weight over the marked parties writes the Bell operator
as $n$ terms. `Upper.weighted_upper` applies the shifted estimate to each
term. `Upper.weighted_upper_binary` compresses Hermitian involution dilations
to obtain the bound for all binary observables. `expectation_upper` applies
`RHLinalg.trace_mul_nonneg_of_posSemidef` to pass to state expectations.
The local declarations named here are private consumed proof steps.

For attainment, the X/Y operator interchanges the two constant basis vectors
with amplitude $n2^{n-2}(-1+i)$. `Attainment.psi_eigenvector` and
`Attainment.rho_attains` establish the phase-adjusted GHZ eigenvector and
its rank-one density expectation inside `result`. The coefficient sign,
finite tensor entries, contraction shifts and normalization are kept in the
literal conventions of `claim`.

## Falsifier

A finite-dimensional binary-observable state with expectation greater than
$Q_n$, or failure of the exhibited rank-one state to attain $Q_n$, would
contradict `result`. Numerical checks cover only the finite scope stated
below and do not establish the universal bound.

## Evidence

`NonlocalityDepthQuantumBound.result` proves `claim` in Lean.
`Upper.unweighted_bound` is the all-party shifted bound on its proof path.
The axiom closure of each public declaration is contained in
$\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.
One `OpenProblemResolutionClaim` records `Proved` at the frozen `result` node.

The escape audit is unfinished for `one_add_posSemidef_of_contraction`,
`Upper.unweighted_bound`, `result`, and the publicized
`FibonacciGrayPath.hamming_cons`. The scoped report contains no
`declared_validated` registration for these targets. Their template gaps and
missing variation, sensitivity, observational-dependence and source-selection
evidence are covered by [#16779](https://github.com/the-omega-institute/trureturing/issues/16779).
No Reg source or successful registration is claimed.

### Experiment

[The pinned experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/6d3320a8c7ec6b9e7c44f07485821ee931d562ce/docs/reports/bernards-guhne-2023-nonlocality-depth-quantum-bound)
contains `check.py`, SHA-256
`89350cf04db5c2d4dd91bc82f17d1bdc99bb3c20b07a9fcbe4cb796bd65dc3c6`.
Command: `python3 check.py` from that directory; exit 0, `ALL_OK`.
The exact integer amplitude check covers $n=3,\ldots,14$.
Float64 maximal eigenvalues for X/Z and X/Y settings cover $n=3,\ldots,8$,
with 200 random qubit projective setting pairs per party number staying
below $Q_n$. The random setting pairs are shared by all parties; this is
not a sampling of all independent party settings or all local dimensions.

## Triage

Tier 1, numerical exact-constant question. Resolution: `Proved`.
Admission basis: `escape-witness`; `utility: none`; `generality: G`.

### What the settlement shows

- **Mechanism — kernel-checked:** `Upper.unweighted_bound` proves the
  shifted all-party estimate by induction from the signed CHSH block.
  `result` proves the universal weighted maximum and simultaneous GHZ
  attainment. The sign recursion and private intermediate lemmas are
  proof steps of these declarations, not additional public results.
- **Consequences — proved in prose:** against the source's classical bound
  $C_n=n2^{n-2}>0$, division gives $Q_n/C_n=\sqrt2$ for every $n\ge3$.
  This exact algebraic consequence uses the source's classical value and
  the kernel-checked quantum value; no Lean declaration of the ratio is
  claimed. The experiment computes the quantum amplitudes for
  $n=3,\ldots,14$ and maximal eigenvalues for $n=3,\ldots,8$ only.
  Finite computation is not evidence for a universal ratio without that
  algebraic derivation.
- **White-noise consequence — proved in prose:** the exhibited Pauli
  full correlators are traceless. Mixing the attaining state with the
  maximally mixed state by noise fraction $p$ therefore gives
  $(1-p)Q_n$. It exceeds $C_n$ exactly when
  $p<1-1/\sqrt2$. This derivation is not a separate kernel theorem.
- **Open:** quantum bounds of hybrid families (24) and (27) for other
  $(k,m)$; the settling theorem does not model these different families.
- **Experiment — computed:** the pinned `check.py` entry above, exit 0,
  gives exact amplitudes through 14 parties, float64 eigenvalues through
  eight parties and the stated random setting checks. No unbounded
  conclusion is attributed to these computations.
- **Literature — source reading:** Bernards' thesis, DOI
  `10.25819/ubsi/10149`, Section 8.6, Eqs. (8.27)–(8.28), repeats the
  $n\le8$ numerics. Werner–Wolf (`quant-ph/0102024`) and Bancal et al.
  (`arXiv:1201.2055`) provide general machinery without evaluating this
  $F_n$. These literature readings are supplied by the search and
  implementation seats; completeness is `ASSUMED-UNVERIFIED`.
- **Source implications:** Eq. (29) gains an exact proof and the
  general-party extension. The source's other Bell families, nonlocality
  models and experimental certification conditions retain their own
  hypotheses; no further quantum optimum is asserted.

## ASSUMED-UNVERIFIED

Literature completeness, worldwide priority, authenticity of external
sources and the physical source-to-matrix interpretation are not Lean
conclusions. The thesis and general-machinery literature readings do not
establish an exhaustive screen. The escape audit is unfinished under
#16779. The separate hybrid-family quantum questions remain open.
