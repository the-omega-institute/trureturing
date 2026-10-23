---
slug: mitra-2022-unsharpness-white-noise-monotonicity-refutation
bibkey: mitra2022unsharpness
doi: 10.1007/s10773-022-05219-2
url: https://arxiv.org/abs/2201.02578v3
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Measurements/MitraUnsharpnessWhiteNoiseRefutation.result
---

# Mitra's instrument-independent unsharpness measure is not monotone under white noise for qubit observables

## Problem

A. Mitra, *Quantifying unsharpness of observables in an outcome-independent way*, Int. J. Theor. Phys. 61, 236 (2022), arXiv:2201.02578v3, defines instrument-independent unsharpness measures of an observable A = {A_i}.
- **The measures.** With the X-matrix X^A = Σ_i ‖A_i‖A_i, they are E(A) = ‖I − X^A‖ and E′(A) = Tr[(I/d)(I − X^A)] (Eqs. (44) and (48)).
- **Monotonicity criteria.** Theorems 3 and 4 show that E and E′ are non-decreasing under the white noise A^λ_i = λA_i + (1 − λ)I/n exactly when Σ^A_1 ≥ Σ^A_2 (Eq. (50)) and Σ′^A_1 ≥ Σ′^A_2 (Eq. (60)) hold. Here Σ^A_1 = x^A_min − 1/n and Σ^A_2 = Σ_i ‖A_i‖/n − x^A_min, with x^A_min the lowest eigenvalue of X^A.
- **The conjecture.** Propositions 1–2 prove both inequalities for dichotomic qubit observables. Then: "Conjecture 1. For any qubit observable A, inequality Σ^A_1 ≥ Σ^A_2 and inequality Σ′^A_1 ≥ Σ′^A_2 hold and therefore, E(A^λ) ≥ E(A) and E′(A^λ) ≥ E′(A) for all 1 ≥ λ ≥ 0."

The verbatim statements are in [the literature note](../Library/QuantumBounds/mitra2022unsharpness.md).

Issue [#17118](https://github.com/the-omega-institute/trureturing/issues/17118) fixes the reading: every qubit POVM with any number n ≥ 1 of outcomes, the operator norm, and all four clauses. The conjecture is refuted.

## Motivation

E would be an unsharpness measure consistent with a resource-theoretic framework only if adding white noise never decreased it; the source states that this follows if Conjecture 1 is proved (§IV.B, §VI).

## Gap

Issue #17118 records the literature check before any Lean:
- arXiv v1–v3, with v3 stating Conjecture 1;
- Buscemi–Kobayashi–Minagawa (Quantum 8, 1235 (2024), arXiv:2303.07737v2), read in full, show that Mitra's autocorrelation measure is not a sharpness monotone, which is a different functional and operation;
- Mitra–Mukherjee–Lee (arXiv:2505.11331v5), read in full, does not treat the conjecture;
- the repository had no entry for the paper.

`not-found-in-searched-scope`.

## Route

Take n = 4 and the diagonal effects A_1 = diag(12, 1)/40, A_2 = diag(13, 1)/40, A_3 = diag(14, 1)/40, A_4 = diag(1, 37)/40.
1. **The POVM.** The effects are positive semidefinite and sum to I.
2. **The norms.** The operator norm of a nonnegative diagonal matrix is its largest entry (`Matrix.l2_opNorm_diagonal`), so the norms are 12/40, 13/40, 14/40 and 37/40, with sum 19/10.
3. **The X-matrix.** X^A = diag(273, 704)/800. Its lowest eigenvalue is 273/800, from the trace and determinant of the Hermitian eigenvalues.
4. **The contradiction.** Σ^A_1 = 273/800 − 1/4 = 73/800 and Σ^A_2 = (19/10)/4 − 273/800 = 107/800, so Σ^A_1 < Σ^A_2.

## Falsifier

The refutation would not hold if:
- the module's observables were narrower than the source's qubit observables, or excluded the witness;
- its norm, X-matrix or lowest eigenvalue differed from the source's;
- the first clause were not part of the conjecture.

The module quantifies over every POVM `Fin n → Matrix (Fin 2) (Fin 2) ℂ` (the frozen `ConcealmentKernelNecessityRefutation.IsPOVM`), uses the norm `‖Matrix.toEuclideanCLM M‖`, and takes the minimum of the two Hermitian eigenvalues. Its `claim` keeps all four clauses of Conjecture 1.

## Evidence

The canonical source is `D5/S3/Quantum/Measurements/MitraUnsharpnessWhiteNoiseRefutation.lean` (238 lines).
- It defines `opNorm`, `X`, `xMin`, `sigma1`, `sigma2`, `sigma1Prime`, `sigma2Prime`, `E`, `EPrime`, `noisy`, `claim`, `diag2` and `witness`, and proves `result : ¬ claim`.
- The POVM predicate is the frozen `ConcealmentKernelNecessityRefutation.IsPOVM` at d = 2, and the witness is a POVM by the frozen `ConcealmentKernelNecessityRefutation.diagonal_povm`.
- It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- `result` is the refutation result of a `refutes` utility, which CLAUDE.md §3.9 exempts from four-slot registration.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Measurements/MitraUnsharpnessWhiteNoiseRefutation.lean.json`, statement `sha256:f7b5f14e673aeaaa28cf94a07eae1a7923f6bd82c4387c90ef5ad072b3e18056`.

Declaration statements:
- `result`: `sha256:b9d00e7f0caa9b90a65fce681d6f5048defd18e45fb544eada4930d2ccb583c2`;
- `claim`: `sha256:eb5aaf37197b44032e205a5b0991055598739d1a3591278bfa5bb20d79994b2d`.

## Triage

Tier 1 conjecture of a 2022 paper, preregistered in issue #17118 before any Lean.
`counterexample`; resolution `refuted`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none: after inlining, the POVM check, the diagonal operator norms, the X-matrix, its lowest eigenvalue and the strict inequality are instantiations of pinned Mathlib results followed by normalization | open-problem-resolution |

Every other public declaration is a definition used by a public statement. The module's 9 private theorems are bind-only helpers consumed on the proof path of `result`, and its compiler-generated declarations also lie on the proof path of `result`. The bind-only form is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; no escape witness is claimed. The utility is `certified-instance` with basis `refutes` the module's `claim`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** the four-outcome qubit POVM above has Σ^A_1 = 73/800 < Σ^A_2 = 107/800, so Conjecture 1 fails.

**Computed, not formalized** (orchestrator, exact fractions and NumPy, 15 October 2026):
- For the witness, E(A^λ) − E(A) = (1 − λ)(73 − 107λ)/800, which is negative for 73/107 < λ < 1. At λ = 9/10 it is −233/80000. So by Theorem 3 the white-noise monotonicity of E fails as well.
- The witness satisfies the second inequality: Σ′^A_1 = 577/1600 ≥ Σ′^A_2 = −217/1600.
- Over 200,000 random qubit POVMs with 2 to 6 outcomes:
  - the smallest value of Σ_1 − Σ_2 was −0.0405, at n = 4;
  - the smallest value of Σ′_1 − Σ′_2 was +0.0086, at n = 2.

**Argued, not formalized.**
- The mechanism: in the witness, the weight of the first basis vector is split among three effects of comparable size. X^A = Σ_i ‖A_i‖A_i weights each effect by its norm, so it is small in that direction (273/800), while the sum of the norms stays large (19/10). Since Σ_1 − Σ_2 = 2x_min − (Σ_i ‖A_i‖ + 1)/n, the inequality fails once x_min drops below (Σ_i ‖A_i‖ + 1)/(2n) = 29/80.
- Σ′_1 − Σ′_2 = Tr X^A − (Σ_i ‖A_i‖ + 1)/n depends on X^A only through its trace, which here is 977/800.

**Open.**
- Whether the second inequality Σ′^A_1 ≥ Σ′^A_2, and hence the white-noise monotonicity of E′, holds for every qubit observable.

**Effect on the paper.** The monotonicity of E under white noise, and so its use as an unsharpness measure in the resource-theoretic sense of §VI, fails for qubit observables with four outcomes. The question for E′ remains open.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The statements in "Computed, not formalized" and "Argued, not formalized" are not formalized.
