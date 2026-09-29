---
slug: angelinos-2022-bform-averaged-enumerator
bibkey: angelinos2022narain
doi: 10.48550/arXiv.2206.14825
url: https://arxiv.org/abs/2206.14825v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Information/BFormCodeAveragedEnumerator.result
---

# The averaged enumerator of B-form codes

## Problem

N. Angelinos, D. Chakraborty and A. Dymarsky (arXiv:2206.14825, hep-th; JHEP
11 (2022) 118) build Narain CFTs from codes over `F_p × F_p`. For prime `p` the
generating matrix is `(I | B^T)` with `B` antisymmetric mod `p` and `B_ii = 0`;
the codewords are `(r, B^T r)`, `r ∈ Z_p^c`. Averaging the full enumerator
polynomial over the `p^{c(c−1)/2}` such `B` at `x_ab = t_a t_b`, `t_a = t_{−a}`,
they state:

> We conjecture the form of corresponding averaged enumerator polynomial based
> on invariance under MacWilliams identity and explicit checks for
> sufficiently small n and prime p

with eq. (barP):
`P̄ = t_0^{2c} + (Σ_{k=0}^{p−1} (Σ_{a,b} cos(2πkab/p) t_a t_b)^c − p t_0^c (Σ_a t_a)^c) / p^c`.

Issue #11296 fixes the reading: `p` prime, `c ≥ 0`, `t : Z/p → ℂ` even, and in
the cosine `k, a, b` are the representatives `0, …, p − 1`.

## Motivation

The averaged enumerator gives the averaged partition function of the code CFT
ensemble, which the paper compares with the holographic "U(1) gravity"
prediction. The frozen declaration
`D5/S3/Quantum/Information/BFormCodeAveragedEnumerator.result` proves eq. (barP)
for every prime `p`, every `c` and every even `t`.

## Gap

Issue #11296 preregisters the reading, the route and the literature check. The
paper has one arXiv version. INSPIRE lists 38 citing records; the 36 arXiv full
texts were searched and none proves eq. (barP). Dymarsky–Shapere
(arXiv:2009.01244) give the `p = 2` average without a written proof.
arXiv:2310.06012 proves the average over all codes, a different ensemble. The
2024 PhD thesis of N. Angelinos was not readable.

These readings are `not-found-in-searched-scope`; they do not establish an
exhaustive worldwide literature search, priority, or the absence of an
independent answer.

## Route

1. Exchange the sums over `B` and `r`; the term `r = 0` gives `t_0^{2c}`.
2. For `r ≠ 0`, `r · B^T r = 0`, and `B ↦ B^T r` maps the B-form matrices onto
   `r^⊥` (a matrix supported on row and column `j`, with `r_j ≠ 0`, reaches any
   `s ∈ r^⊥`). All fibres have the same size, so the sum over `B` is
   `p^{c(c−1)/2} / p^{c−1}` times the sum over `s ∈ r^⊥`.
3. Write `[r · s = 0] = p^{−1} Σ_k ψ(k r · s)` with the standard additive
   character `ψ`. The sum over `r, s` factors into
   `(Σ_{a,b} ψ(kab) t_a t_b)^c`; the row `r = 0` gives `p t_0^c (Σ_a t_a)^c`.
4. Since `t` is even, `Σ_{a,b} ψ(kab) t_a t_b` equals the cosine sum.

## Falsifier

The answer would change if the average were taken over all codes rather than
the B-form ones, or if `t` were not even (a non-even `t` at `(p, c) = (3, 2)`
gives 441.33 against 454.83 for the formula).

## Evidence

Exact rational averages over all `B` and `r` (issue #11296) against the formula
at 50 digits, for random rational even `t` and
`(p, c) ∈ {(2,1), (2,2), (2,3), (2,4), (3,1), (3,2), (3,3), (5,2), (5,3), (7,2)}`:
the largest difference is `2.4·10⁻⁴⁸`.

The canonical source is
`D5/S3/Quantum/Information/BFormCodeAveragedEnumerator.lean`. Its public
declarations are `IsBForm`, `enumerator`, `claim` and `result`. The frozen
module state has statement identity
`sha256:d83ffc595ee5d2d3392359a50a396f6bf0162cd14d9955b003ca53e8b6554754`.
The result declaration has statement identity
`sha256:be58fcd358ee925fa63d598d89140a27ed7edad84adf563a3c71a13f82fd4534`.
The Freeze event is
`sha256:e2538d573612982b772b8d0f4edb5d1857596f24f2658c2c6b4746c610139cef`
and has no project-level frozen prerequisites. The proof uses only the standard
axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`,
`native_decide`, or new axiom.

## Triage

Tier 1 external named conjecture, preregistered in issue #11296 before any
Lean. `theorem`; resolution `proved`. The public theorem has
`proof_shape: content`: the fibre count, the count of B-form matrices, the
character expansion and the cosine reduction are proved in the module. Its
escape witness is form (2), and its admission basis is
`open-problem-resolution`. Utility `none`: the statement holds for every prime
`p`, every `c` and every even `t`.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty,
priority, or the absence of an independent answer. The Lean kernel does not
authenticate the external source or its version history.
