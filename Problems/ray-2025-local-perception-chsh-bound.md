---
slug: ray-2025-local-perception-chsh-bound
bibkey: ray2025localperception
doi: 10.48550/arXiv.2511.00314
url: https://arxiv.org/abs/2511.00314v1
triage: theorem
motivation_gids:
  - D5/S3/QuantumBounds/LocalPerceptionCHSH.result
---

# The termwise local-perception CHSH witness is at most 2 for every measurement setting

## Problem

R. K. Ray, *Local perception operators and classicality: new tools for old tests*, arXiv:2511.00314v1, replaces each correlator C_xy = Tr(ρ A_x ⊗ B_y) of a Bell functional by its "locally perceived" version a_x b_y C_xy. Here a_x = Tr(ρ_A A_x) and b_y = Tr(ρ_B B_y) are the local means of dichotomic observables (Eqs. (10), (11) and (35)). For CHSH (Eq. (19)) this gives the symmetric witness W^s_LPO(ρ) = sup over settings of a₀b₀C₀₀ + a₀b₁C₀₁ + a₁b₀C₁₀ − a₁b₁C₁₁ (Eq. (21)).
- Theorem 4 proves W^s_LPO ≤ 2 when each party's settings are mutually orthogonal Bloch directions (Eq. (31)).
- The author then writes: "we conjecture that for all other conceivable measurement settings, the upper-bound of W^s_LPO(ρ) saturates at 2."

The verbatim statements are in [the literature note](../Library/QuantumBounds/ray2025localperception.md).

Issue [#16628](https://github.com/the-omega-institute/trureturing/issues/16628) fixes the reading.
- The observables are the source's dichotomic observables "(POVM, or projective)": Hermitian A with 1 ± A ⪰ 0.
- The witness is the termwise sum. The first line of Eq. (21), Tr(ρ (B)^A_ρ ⊗ (B)^B_ρ), mixes different settings and is not equal to that sum.

The conjecture is proved: the sum is at most 2 for every two-qubit state and all dichotomic settings, and 2 is attained.

## Motivation

The witness is meant to certify that locally perceived statistics admit a local hidden-variable description. With the settings unrestricted, its CHSH value never exceeds the classical value 2, so the certificate holds whatever settings are used. The orthogonality restriction of Theorem 4 is therefore unnecessary.

## Gap

Issue #16628 records the literature check before any Lean:
- arXiv v1 is the only version;
- Semantic Scholar lists no citing work;
- Crossref, Zenodo and web searches return only the source;
- the repository had no entry for the paper.

`not-found-in-searched-scope`.

## Route

1. **Probabilities.** For ε, η ∈ {1, −1} the effects (1 + εA_x)/2 and (1 + ηB_y)/2 are positive, so P_xy(ε, η) = Tr(ρ (1 + εA_x)/2 ⊗ (1 + ηB_y)/2) = (1 + εa_x + ηb_y + εηC_xy)/4 ≥ 0.
2. **Relabeling.** Replacing A_x by −A_x flips a_x and C_xy and leaves a_x b_y C_xy unchanged; the same holds for B_y. So assume p = a₀, q = a₁, r = b₀ and s = b₁ all lie in [0, 1].
3. **Four inequalities.** C₀₀ ≤ 1, C₀₁ ≤ 1 − p + s, C₁₀ ≤ 1 + q − r and C₁₁ ≥ q + s − 1. With nonnegative coefficients they give S ≤ G = pr + ps(1 − p + s) + qr(1 + q − r) + qs(1 − q − s).
4. **The certificate.** 2 − G = ((1 − p)/2)[r + s² + (1 − s)²] + s(1 − p)² + ((1 − r)/2)[p + q² + (1 − q)²] + q(1 − r)² + (1 − q)(1 − s)(1 + q + s), which is nonnegative on [0, 1]⁴.
5. **Attainment.** For |00⟩ with σ_z everywhere, a_x = b_y = C_xy = 1 and S = 2.

## Falsifier

The proof would not settle the conjecture if:
- the module's settings were narrower than the source's dichotomic observables;
- its functional differed from the source's termwise witness;
- the value 2 were not attained.

The module's `IsDichotomic` admits every Hermitian A with 1 ± A ⪰ 0, which includes all projective ±1 observables, with no orthogonality condition. `lpoCHSH` is Σ α_xy a_x b_y C_xy with the CHSH coefficients of Eq. (19). The second conjunct of `claim` exhibits the value 2.

## Evidence

The canonical source is `D5/S3/QuantumBounds/LocalPerceptionCHSH.lean` (178 lines).
- It defines `IsDichotomic`, `meanA`, `meanB`, `correl`, `chshCoeff`, `lpoCHSH` and `claim`, and proves `result : claim`.
- It uses the frozen `RHLinalg.trace_mul_nonneg_of_posSemidef` of `D5/S3/Weil/ZetaLinear/RankTrace` (the trace of a product of positive semidefinite matrices has nonnegative real part), Mathlib's `Matrix.PosSemidef.kronecker`, and real arithmetic.
- It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- The escape registration in `Reg/D5/S3/QuantumBounds/LocalPerceptionCHSH.lean` reads out the score `lpoCHSH ρ A B` of the universal bound. Its rejected realization, the constant score 3, fails because the attaining state and settings of the second conjunct would give 3 ≤ 2. It is `declared_validated`.

Frozen state: `Golden/Frozen/state/D5/S3/QuantumBounds/LocalPerceptionCHSH.lean.json`, statement `sha256:6c3f82e8a0256464adc805327e8da93e46320edd691f7acfd1b4819904208611`.

Declaration statements:
- `result`: `sha256:f74e16af6d575798b869cde60864bb38e7eb7136b44a6bbb1d665b69ef0727c2`;
- `claim`: `sha256:e3c8afaae9180e5d16aa67db5434d51528c7e0dcc2a86b28b699e5c8b13956a1`.

## Triage

Tier 1 conjecture of a 2025 paper, preregistered in issue #16628 before any Lean.
`theorem`; resolution `proved`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none: after inlining, the positivity of the outcome probabilities, their expansion and the polynomial certificate are instantiations of pinned Mathlib results followed by normalization | open-problem-resolution |
| the expansion, effect, positivity, sign-reduction and polynomial helpers (private) | bind-only (consumed on the proof path of `result`) | none | consumed helpers |

Every other declaration is a definition used by a public statement or a compiler-generated proof on the proof path of `result`. The bind-only form is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; no escape witness is claimed. The utility is `none`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every two-qubit state and all dichotomic observables, a₀b₀C₀₀ + a₀b₁C₀₁ + a₁b₀C₁₀ − a₁b₁C₁₁ ≤ 2, and the value 2 is attained.

**Computed, not formalized** (orchestrator, 14 October 2026; SciPy):
- over 300 local maximizations over random two-qubit states of every rank and four unit Bloch directions, the maximum is 1.99999999999;
- control: the same optimizer reaches 3.99999999999 on the first-line functional Tr(ρ (B)^A_ρ ⊗ (B)^B_ρ) of Eq. (21).

**Argued, not formalized.**
- The mechanism is the compatibility of the local means with the correlators. Steps 2–4 use only the positivity and normalization of a binary probability table whose marginals do not depend on the other party's setting. So the bound 2 holds for every nonsignaling binary table, in any dimension, not only for quantum states.
- Without that compatibility the bound would be 4, the value of the triangle-inequality bound of the source's Theorem 3.

**Open.**
- Symmetric witnesses for other Bell functionals, with the quadratic terms Σβ_x a_x² + Σγ_y b_y². An example is the I3322-type witness of Eq. (43), for which the source states the bound (1 + √3)‖r_A‖‖r_B‖ + ‖r_A‖² (Appendix C); this settlement does not address it.
- The set of states and settings at which the value 2 is attained.

**Effect on the paper.** The conjecture holds, so the CHSH value of the symmetric witness never exceeds the classical bound, for any settings. The first line of Eq. (21) is a different functional and does not satisfy this bound.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The statements in "Computed, not formalized" and "Argued, not formalized" are not formalized.
