---
slug: nishioka-sato-2021-bernoulli-harmonic-zeta-identity
bibkey: nishioka2021freescalar
doi: 10.1007/JHEP05(2021)074
url: https://arxiv.org/abs/2101.02399v5
triage: theorem
motivation_gids:
  - D5/S3/Quantum/FockSpace/HyperbolicScalarZetaIdentity.result
---

# A Bernoulli–harmonic–zeta identity for the free scalar on hyperbolic space

## Problem

T. Nishioka and Y. Sato (arXiv:2101.02399, hep-th; JHEP 05 (2021) 074)
compute the free energy of a conformally coupled free scalar on hyperbolic
space. In the derivative of the spectral zeta function for even dimension they
need, for every `k ≥ 0`,

`−2^{−2k−2}/(k+1) H_{2k+1} − Σ_{m=1}^{k} 2^{−2k−2}(2^{2m}−2)/(k−m+1) · B_{2m}/(2m)
+ Σ_{j=0}^{2k+1} (−1)^j/2^{2k−j} · C(2k+1, j) H_j ζ(−j) + (1 − 2^{−2k−1}) H_{2k+1} B_{2k+2}/(k+1) = 0`

(eq. (C.12) of the published text), and state: "We confirmed (C.12) up to
k = 100 numerically. However, we do not know a proof of (C.12)." Issue #11322
fixes the reading: `H_j` the harmonic numbers, `B_n` the Bernoulli numbers
with `B_1 = −1/2`, `ζ` the Riemann zeta function.

## Motivation

The identity removes all terms other than `ζ'(−j)` from `∂_s ζ_{H^d}(0, 1/2)`,
which the paper uses for the free energy on `H^d` and its defect C-theorem.
The follow-up on the free fermion (arXiv:2102.11468) records that the scalar
case was checked only numerically. The frozen declaration
`D5/S3/Quantum/FockSpace/HyperbolicScalarZetaIdentity.result` proves the
identity for every `k`; the physical consequence is not formalized.

## Gap

Issue #11322 preregisters the reading, the route and the literature check.
arXiv v5 and the published JHEP text state the identity without proof.
INSPIRE lists 38 citing records; the 34 arXiv full texts were searched and
none proves or restates it. Boyadzhiev (arXiv:1701.00544) evaluates
`Σ C(n, k) H_k B_k`, a different sum.

These readings are `not-found-in-searched-scope`; they do not establish an
exhaustive worldwide literature search, priority, or the absence of an
independent answer.

## Route

Put `N = 2k + 2` and `b_m = Σ_i C(m, i) 2^i B_i`.
1. `b_m = (2 − 2^m) B_m`, from `e^t · 2t/(e^{2t} − 1) = 2t/(e^t − 1) − 2t/(e^{2t} − 1)`;
   in particular `b_m = 0` for odd `m`.
2. With `ζ(−j) = (−1)^j B_{j+1}/(j+1)` and after multiplying by `2^N (k+1)`, the
   middle sum is `Σ_{1≤i≤N−1} b_i (1/i + 1/(N−i))` and the zeta sum is
   `Σ_{1≤i≤N} C(N, i) 2^i B_i H_{i−1}`.
3. `C(n, i)(H_n − H_i) = Σ_{j=1}^{n} C(n−j, i)/j` and
   `Σ_i C(n, i) 2^i B_i / i = Σ_{j=1}^{n} (b_j − 1)/j` turn the zeta sum into sums
   of `b_i/i` and `b_{N−i}/i`, which cancel against the middle sum; what is left
   is `−H_{N−1} − 1/N + H_N = 0`.

## Falsifier

The answer would change if `B_1` were taken as `+1/2` or `ζ(0)` differed from
`−1/2`; or if `H_j` were shifted: replacing `H_j` by `H_{j+1}` gives
`−5/12` at `k = 0`.

## Evidence

Exact rational arithmetic (issue #11322): the left side is `0` for
`k = 0, …, 60`. Dropping `2^{−2k−1}` from the last coefficient gives
`1/12, −11/2880, …`, and no zero for `k ≤ 20`.

The canonical source is
`D5/S3/Quantum/FockSpace/HyperbolicScalarZetaIdentity.lean`. Its public
declarations are `claim` and `result`. The frozen module state has statement
identity
`sha256:356ea220510eb946186fe98dc8c09827f4c48710f5ba1759ae515d8d8331bc5b`.
The result declaration has statement identity
`sha256:fc7f2aa577e096bb0f6203e18e5592dcdc8f994af0f4e8cdca30688a856ea95c`.
The Freeze event is
`sha256:8c34d203a5594a3ab5f6338b1e7db08e0ffcd431eafb3071bdea5f3d1d285c8d`
and has no project-level frozen prerequisites. The proof uses only the standard
axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`,
`native_decide`, or new axiom.

## Triage

Tier 1 external named conjecture, preregistered in issue #11322 before any
Lean. `theorem`; resolution `proved`. The public theorem has
`proof_shape: content`: the evaluation of `b_m`, the harmonic–binomial
identities and the telescoping are proved in the module. Its escape witness
is form (1), and its admission basis is `open-problem-resolution`. Utility
`none`: the identity is proved for every `k`.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty,
priority, or the absence of an independent answer. The Lean kernel does not
authenticate the external source or its version history.
