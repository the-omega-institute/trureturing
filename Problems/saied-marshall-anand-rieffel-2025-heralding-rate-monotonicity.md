---
slug: saied-marshall-anand-rieffel-2025-heralding-rate-monotonicity
bibkey: saied2025photondistillation
doi: 10.1103/PhysRevApplied.23.034079
url: https://arxiv.org/abs/2404.14217v4
triage: theorem
motivation_gids:
  - D5/S3/Quantum/FockSpace/IdealHeraldingRateMonotonicity.result
---

# The ideal heralding rate of Fourier photon distillation decreases strictly to 1/4 from n = 5

## Problem

J. Saied, J. Marshall, N. Anand and E. G. Rieffel, *General protocols for the efficient distillation of indistinguishable photons*, Phys. Rev. Applied 23, 034079 (2025), arXiv:2404.14217v4, distill indistinguishable photons with n-photon protocols built from an n × n unitary whose first row is constant (for example the discrete Fourier transform).
- **The ideal heralding rate.** For such a unitary, h_n(0) = (−1/n)^{n−1}(n − 1)! Σ_{t=0}^{n−1} (n − t)(−n)^t/t! for every n > 2 (Theorem III.5, Eq. (III.9)), and lim h_n(0) = 1/4 (Theorem III.5(2)).
- **The conjecture.** After a numerical evaluation for every n from 5 to 10⁵ and selected larger n up to 10⁷ (Figure 4): "Conjecture III.7. For n ≥ 5, the sequence h_n(0) monotonically decreases to 1/4."

The verbatim statements are in [the literature note](../Library/QuantumChannels/saied2025photondistillation.md).

Issue [#16743](https://github.com/the-omega-institute/trureturing/issues/16743) fixes the reading: the conjecture is the statement about the sequence of Eq. (III.9), strict decrease for n ≥ 5 together with the limit 1/4. Its correction comment fixes the transcription of Eq. (III.9) ((n − 1)! multiplies the sum). The conjecture is proved.

## Motivation

The heralding rate sets the resource cost of distillation: about n/h_n(0) photons per distilled photon. Monotone decrease to 1/4 gives the uniform bound n/h_n(0) < 4n for every n ≥ 5, so the cost grows at most linearly, with constant 4.

## Gap

Issue #16743 records the literature check before any Lean:
- arXiv v1–v4; v4, the published version, states Conjecture III.7 (numbered III.6 in v1–v3);
- Semantic Scholar lists 9 citing works, whose full texts were scanned for the conjecture, monotonicity and the quarter limit; none proves the monotonicity;
- OEIS A277458 (the integers n^{n−1}h_n(0)) gives the asymptotic n^{n−1}/4 but no monotonicity;
- web search returns no settlement;
- the repository had no entry for the paper.

`not-found-in-searched-scope`.

## Route

Write p_n for Eq. (III.9).
1. **A finite-interval form.** With A_n = n²∫₀¹ (1 − u)u^{n−1}e^{n(u−1)} du and T_n = 2n!e^{−n}/n^{n−1}, p_n = A_n + (−1)^{n−1}T_n and 0 ≤ T_n ≤ 2n e^{−n}. The moments ∫₀¹ u^m e^{a(u−1)} du come from the pinned Mathlib theorem `LindemannWeierstrass.integral_exp_mul_eval`.
2. **One primitive.** With r(u) = u e^{u−1} and K(u) = 2(2u − 1)/(1 + u)⁴, the explicit primitive G_n(u) = [n(1 − u)/(1 + u) + 2u/(1 + u)³] u^n e^{n(u−1)} gives A_n = 1/4 + ∫₀¹ K r^n and A_n − A_{n+1} = ∫₀¹ K r^n (1 − r).
3. **The gap.** The window [1 − 1/n, 1 − 1/(2n)] contributes at least 1/(512n²), and the negative half [0, 1/2] at least −e^{−n}. So p_n − p_{n+1} ≥ 1/(512n²) − (4n + 3)e^{−n}, which is positive for every n ≥ 16, because 512n²(4n + 3) < e^n by induction from n = 16 (with e > 2.7182818283).
4. **The finite cases.** For 5 ≤ n ≤ 15, the exact rational differences p_n − p_{n+1} are positive.
5. **The limit.** |A_n − 1/4| ≤ 2/(n + 1), so |p_n − 1/4| ≤ 3/n for n ≥ 16.

## Falsifier

The proof would not settle the conjecture if the module's sequence differed from Eq. (III.9), if the decrease were not strict from n = 5, or if the limit were missing. The module's `pRat` is Eq. (III.9) literally in ℚ, `p` is its real cast, and `claim` is (∀ n ≥ 5, p (n + 1) < p n) ∧ p → 1/4.

## Evidence

The canonical source is `D5/S3/Quantum/FockSpace/IdealHeraldingRateMonotonicity.lean` (733 lines).
- It defines `pRat`, `p` and `claim`, and proves `result : claim`.
- It uses pinned Mathlib only: `LindemannWeierstrass.integral_exp_mul_eval` with `Polynomial.sumIDeriv_apply_of_le` for the moments, `intervalIntegral.integral_eq_sub_of_hasDerivAt` for the primitive, `Real.one_add_inv_pow_le_exp`, `Real.exp_one_lt_three` and `Real.exp_one_gt_d9` for the exponential estimates, `Nat.factorial_le_pow`, and `squeeze_zero'` for the limit.
- It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- The escape registration in `Reg/D5/S3/Quantum/FockSpace/IdealHeraldingRateMonotonicity.lean` reads out the limit value 1/4 of the second conjunct of `claim`. Its rejected realization, the limit value 0, fails by uniqueness of limits against `result`. It is `declared_validated`.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/FockSpace/IdealHeraldingRateMonotonicity.lean.json`, statement `sha256:2642796792c41c8b2dc589c397310dbc758012d98c63c102c02eeb369783bea5`.

Declaration statements:
- `result`: `sha256:65a0e3acd93de1f7a18182590fab8b9fa097037f7cfc668d48200e95ffa3efd0`;
- `claim`: `sha256:ad806584fad2c1cb94a04324e3d378de78eecf275b3b236781007ce6c79d31b4`.

## Triage

Tier 1 conjecture of a 2025 paper, preregistered in issue #16743 before any Lean.
`theorem`; resolution `proved`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none: after inlining, the moment formula, the primitive, the window and tail estimates, the exponential induction, the finite comparisons and the squeeze are instantiations of pinned Mathlib results followed by normalization | open-problem-resolution |
| the moment, primitive, kernel, window, tail, exponential and limit helpers (private) | bind-only (consumed on the proof path of `result`) | none | consumed helpers |

Every other declaration is a definition used by a public statement or a compiler-generated proof on the proof path of `result`. The bind-only form is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; no escape witness is claimed. The utility is `none`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every n ≥ 5, h_{n+1}(0) < h_n(0), and h_n(0) → 1/4. Hence h_n(0) > 1/4 and n/h_n(0) < 4n for every n ≥ 5.

**Computed, not formalized** (orchestrator, exact rational arithmetic, 14 October 2026): the decrease holds for every 5 ≤ n ≤ 400 and h_n(0) > 1/4 for every 5 ≤ n ≤ 401, with h₄₀₀(0) − 1/4 = 1.56 × 10⁻⁴; control: h₄(0) = 1/4 < h₅(0) = 33/125, so the decrease starts exactly at n = 5.

**Argued, not formalized.**
- The mechanism is the kernel representation: A_n − A_{n+1} = ∫₀¹ K r^n(1 − r), where K is negative only on [0, 1/2], where r^n is exponentially small, while near u = 1 the integrand is of order 1/n². The alternating tail T_n is exponentially small, so it cannot reverse the sign for large n; for small n the exact values decide.
- The bound |p_n − 1/4| ≤ 3/n is consistent with the source's observed asymptotic h_n(0) − 1/4 ∼ 1/(16n), but this settlement does not prove that asymptotic.

**Open.**
- The asymptotic h_n(0) − 1/4 ∼ 1/(16n) observed in the source.
- The heralding rate under distinguishability errors beyond first order (Theorem III.4 gives h_n(ε) to first order).

**Effect on the paper.** Conjecture III.7 holds, so the uniform resource estimate n/h_n(0) < 4n holds for every n ≥ 5, without the numerical cut-off of Figure 4.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The statements in "Computed, not formalized" and "Argued, not formalized" are not formalized.
