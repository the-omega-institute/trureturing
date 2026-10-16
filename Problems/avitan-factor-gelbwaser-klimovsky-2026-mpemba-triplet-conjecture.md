---
slug: avitan-factor-gelbwaser-klimovsky-2026-mpemba-triplet-conjecture
bibkey: avitanfactorgelbwaserklimovsky2026mpembatriplets
doi: null
url: https://arxiv.org/abs/2603.04567v1
triage: theorem
motivation_gids:
  - D5/S3/StatisticalMechanics/MarkovMpembaTripletRefutation.result
---

# A four-level system whose triplets all violate the three-level conditions, yet shows the Markovian Mpemba effect

## Problem

I. Avitan, R. Factor and D. Gelbwaser-Klimovsky, *Necessary conditions for the Markovian Mpemba effect*, arXiv:2603.04567v1, study relaxation under a rate matrix M with detailed balance.
- **Slow-mode criterion.** The Mpemba effect occurs iff the slow-mode coefficient |b_2| of the initial Gibbs state Π(β_in) has a maximum at some β_in ≠ β_b (p. 2).
- **Three-level conditions.** For three levels they derive the necessary condition (3) on the rates.
- **Triplets.** For N levels they apply (3) to every triplet of levels, keeping the original rates.
- **The conjecture** (p. 4): "we conject that if for an N−level system, all its triplets violate conditions (3), then the N−level system does not experience the Mpemba effect."

The follow-up arXiv:2609.09988v1 (§II) restates the conjecture as shown.

The verbatim statements are in [the literature note](../Library/StatisticalMechanics/avitanfactorgelbwaserklimovsky2026mpembatriplets.md).

Issue [#17871](https://github.com/the-omega-institute/trureturing/issues/17871) fixes the reading:
- the slow-mode coefficient is ℓ·Π(β) for a left eigenvector ℓ of the slowest nonzero eigenvalue, assumed simple;
- the effect is two initial temperatures on the same side of β_b, the farther one with the smaller |ℓ·Π(β)|. This implies the source's criterion.

The conjecture is refuted.

## Motivation

The conjecture would reduce the search for the Mpemba effect in N-level systems to checking three-level conditions. The source uses it to rule the effect out in several systems, and to generate negative examples for machine-learning predictors.

## Gap

Issue #17871 records the literature check before any Lean:
- arXiv v1 is the only version;
- the arXiv search "Markovian Mpemba effect" (50 titles through 15 October 2026) and the author search show no settlement; the follow-up arXiv:2609.09988 uses the conjecture as established;
- the search seat reports that the no-Mpemba criteria of Klich–Vucelja (arXiv:1812.11962) and Ohga–Hayakawa–Ito (arXiv:2410.06623) do not apply to this family;
- Naixu-Guo/quantum-open-problems, Zenodo and the repository had no record;
- the citation lists of OpenAlex and Semantic Scholar were not retrieved (HTTP 429).

`not-found-in-searched-scope`.

## Route

1. **Witness.** Four levels with energies (0, 1, 2, 64)·log 16, β_b = 1, and r = 16⁻⁶⁴.
   - Weights: w = (1, 1/16, 1/256, r). Slow-mode vector: g = (0, 1, 2/3, 8/15), with mean μ = w·g/Σw.
   - Downward rates: a₁₂ = 47/48 − μ − 112r/25, a₁₃ = 3/2 − 3μ/2 − 128r/25, a₁₄ = 31/20 − 15μ/8, a₂₃ = 1, a₂₄ = 3/5, a₃₄ = 1/10.
   - Upward rates follow from detailed balance. All rates are positive because 3/50 < μ < 1/16.
2. **Triplets.** In each of the four triplets both inequalities of (3) fail, so every triplet violates (3) whatever the value of k.
3. **Slow mode.** 1ᵀM = 0 and fᵀM = −fᵀ for f = g − μ1.
   - On the common kernel K of 1ᵀ and fᵀ, with basis (1, 2, −3, 0) and (7, 8, 0, −15), M acts by a 2 × 2 matrix F.
   - tr F < −4, 4 + 2 tr F + det F > 0 and 1 + tr F + det F > 0.
   - So every real eigenvalue of M is 0, −1 or below −2, and the left eigenspace of −1 is spanned by f.
4. **The effect.** f·Π(β) = (x + (2/3)x² + (8/15)x⁶⁴)/(1 + x + x² + x⁶⁴) − μ with x = 16^{−β}.
   - At β₁ = log(1024/1023)/log 16 (x = 1023/1024) and β₂ = log(128/127)/log 16 (x = 127/128), both values are positive and the first is smaller.
   - Since 0 < β₁ < β₂ < β_b, the hotter initial state has the smaller slow-mode coefficient.

## Falsifier

The refutation would not settle the conjecture if:
- the module's generator, detailed balance, Gibbs states or condition (3) differed from Eqs. (1)–(3);
- its slow mode were not the slowest nonzero eigenvalue, or not simple;
- its notion of the effect were weaker than the source's criterion.

The module quantifies over:
- every N ≥ 3, strictly increasing energies and β_b > 0;
- rates positive off the diagonal with detailed balance;
- every slow mode (λ < 0, a left eigenvector, every real eigenvalue 0 or ≤ λ, and a one-dimensional left eigenspace).

Its effect requires two temperatures on one side of β_b, which forces an interior maximum of |b_2|.

## Evidence

The canonical source is `D5/S3/StatisticalMechanics/MarkovMpembaTripletRefutation.lean` (416 lines).
- It defines `generator`, `DetailedBalance`, `TripletCondition`, `IsSlowMode`, `MpembaEffect` and `claim`, and proves `result : ¬ claim`.
- It reuses `GlauberRelaxationOrderRefutation.gibbs` for Gibbs states and `LongGapsBetweenPrimes.exp_neg_nat_mul_log` for exp(−n log 16) = 16⁻ⁿ.
- It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- The escape registrations: `result` is the designated refutation result of the `utility` header and is exempt, and the module has no other public theorem.

Frozen state: `Golden/Frozen/state/D5/S3/StatisticalMechanics/MarkovMpembaTripletRefutation.lean.json`, statement `sha256:8340de056204e35d0f59adebf2811fb86ceaa88be553880920a836557e625878`.

Declaration statements:
- `result`: `sha256:11d2195c81338aedc31ce0d26c2ef832027264b264763c84719a7f8653673e86`;
- `claim`: `sha256:7c725f1c90cc202b3b8a2239fb64604b064d970a16e3e11a4489dda8bb41eb5a`.

## Triage

Tier 1 conjecture of a 2026 paper, preregistered in issue #17871 before any Lean.
`theorem`; resolution `refuted`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none: after inlining, the rate, triplet, eigenvector, block and Gibbs identities are rational identities and bounds closed by `norm_num`, `ring` and `linarith` | open-problem-resolution |
| the witness and certificate helpers (private) | bind-only (consumed on the proof path of `result`) | none | consumed helpers |

Every other public declaration is a definition used by a public statement. The bind-only form is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; no escape witness is claimed. The refutation is a certified instance with basis `refutes`. There is no digestion atom.

### What the settlement shows

**Refuted by `result`:** a four-level system with positive detailed-balance rates in which every triplet violates (3), the slowest nonzero eigenvalue −1 is simple, and a hotter initial Gibbs state has a smaller slow-mode coefficient than a colder one.

**Computed, not formalized** (orchestrator, recorded in #17871):
- the four eigenvalues are 0, −1, −2.1355… and −2.4519… (NumPy);
- the triplet margins range from −0.0252 to −0.912 (exact);
- the same construction with n = 42 in place of 64 gives the effect, with the maximum of b_2 near β ≈ 2·10⁻⁴; for n = 100 it is near β ≈ 3.5·10⁻³ (floating point);
- for n = 64 the maximum of b_2 is near β ≈ 2.7·10⁻³ (floating point), and f·Π(β) is 0.4890371 at x = 1023/1024 and 0.4892979 at x = 127/128 (exact rationals).

**Argued, not formalized.**
- *Mechanism.* b_2 is, up to the constant μ, the Gibbs mean of g. As the initial temperature rises, the three lower levels equalize first, and the mean of g approaches (0 + 1 + 2/3)/3 = 5/9. The top level, at energy n log 16 with n ≥ 42, fills only at much higher temperature. Its component 8/15 lies below 5/9, so filling it lowers the mean toward (0 + 1 + 2/3 + 8/15)/4 = 11/20. Hence b_2 rises and then falls, with an interior maximum.
- *Why the triplets miss it.* Condition (3) on a triplet sees only that triplet's rates and energy gaps. The effect here comes from the joint slow mode of all four levels, which no three-level reduction with unmodified rates represents.

**Open.**
- Whether some local condition on triplets, with recomputed effective rates, is necessary for the effect.
- Whether the conjecture holds under additional hypotheses on the energy spectrum, for example bounded level spacing.

**Effect on the paper.** The triplet test cannot rule out the Mpemba effect in N-level systems. The negative examples it generates, and the use of the conjecture in arXiv:2609.09988, need another criterion.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The citation lists of the source were not retrieved. The statements in "Computed, not formalized" and "Argued, not formalized" are not formalized.
