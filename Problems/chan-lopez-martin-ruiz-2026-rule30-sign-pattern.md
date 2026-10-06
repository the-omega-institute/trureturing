---
slug: chan-lopez-martin-ruiz-2026-rule30-sign-pattern
bibkey: chanlopezmartinruiz2026rule30
doi: 10.48550/arXiv.2604.00165
url: https://arxiv.org/abs/2604.00165v3
triage: theorem
motivation_gids:
  - D5/S0/Automata/RuleThirtyTwentyTwoMersenneSignRefutation.result
---

# A non-Mersenne exception to the Rule 30 / Rule 22 sign pattern

## Problem

E. Chan-López and A. Martín-Ruiz, *Symmetric Nonlinear Cellular Automata as Algebraic References for Rule 30*, arXiv:2604.00165v3, Remark 3, states:

> A direct computation for m ≤ 256 shows that ϵ(m) ≤ 0 precisely at the Mersenne indices m = 2^k − 1, with ϵ = 0 for k ≤ 3 and ϵ < 0 for 4 ≤ k ≤ 8.

Section 9 asks:

> Is the sign pattern of Remark 3 exact for all k?

The quantified sign-pattern interpretation is

```text
claim := ∀ m : ℕ, 1 ≤ m → (eps m ≤ 0 ↔ ∃ k : ℕ, 1 ≤ k ∧ m = 2^k − 1).
```

Here `row g 0 r = decide (r = 0)` and `row g (m+1) r = g (row g m (r−1)) (row g m r) (row g m (r+1))` on the full integer lattice. The Boolean algebraic normal forms are `g30 a b c = a xor b xor c xor (b and c)` (Proposition 1) and `g22 a b c = a xor b xor c xor (a and b and c)` (Eq. (1)). Definition 2 counts the full-row set `{r : ℤ | row g m r = true}` with `Set.ncard`. Equation (11) defines `eps m` as the integer difference of these cardinalities. This interprets the word “precisely” as a biconditional for every positive row; it does not identify that biconditional with the separate strict-negativity assertion at every Mersenne row.

## Motivation

Issue #12739 preregisters the external Tier-1 question, the quantified claim, and the witness `m = 767`. The motivation declaration is `D5/S0/Automata/RuleThirtyTwentyTwoMersenneSignRefutation.result`.

## Gap

Remark 3 reports a finite observation through 256; §9 asks for an unbounded extension. The bounded literature checks recorded in #12739 cover arXiv v3, INSPIRE and MathDB; Semantic Scholar was rate-limited. No previous settlement was found in that searched scope. This is not an exhaustive absence or priority claim.

## Route

Quiescence gives a light-cone induction: all sites outside `[-m,m]` are false. A second induction identifies the integer-lattice row with the bits of the iterated natural-number recurrence, with bit position `r+m` and negative positions false. The injective map `i ↦ (i : ℤ)−m` identifies active bits below `2m+1` with the entire support. For Rule 30 the step is `(b <<< 2) xor ((b <<< 1) or b)`; for Rule 22 it is `(b <<< 2) xor (b <<< 1) xor b xor ((b <<< 2) and (b <<< 1) and b)`.

The kernel counts the active bits at row 767: 763 for Rule 30 and 768 for Rule 22. The integer difference is −5. Since `2^9 = 512 < 768 < 1024 = 2^10`, 768 is not a power of two; thus 767 is not Mersenne. The only-if direction fails.

## Falsifier

The refutation requires the full integer support, the single seed, the exact ANF rules, the light-cone bound and the encoding/cardinality bridge. Counting only a half-row or replacing integer subtraction with natural subtraction would change the claim. The theorem is `result : ¬ claim`, with no additional hypotheses.

## Evidence

`D5/S0/Automata/RuleThirtyTwentyTwoMersenneSignRefutation.lean` exposes only `row`, `g30`, `g22`, `supportCard`, `eps`, `claim` and `result`. Its private light-cone, encoding and support-identification lemmas occur on the proof path to `result`; the remaining bit identities are local proof steps. The theorem uses kernel evaluation, with no `native_decide`, and has axiom closure `[propext, Classical.choice, Quot.sound]`. The Scribe result records `Refuted` for this problem.

## Triage

`theorem`; resolution `Refuted`; preregistration #12739. `proof_shape: content` for `result` and the three private theorems; `admission_basis: open-problem-resolution`. Information-escape registration is paused under CLAUDE.md §3.9.

### What the settlement shows

- **Proved in this module:** `eps 767 = −5`, with support cardinalities 763 and 768, although 767 is not a Mersenne index. The “precisely” pattern fails in the k = 10 window, between `2^9−1` and `2^10−1`. The failure is the only-if direction: the symmetric reference has more active sites at a non-Mersenne row. Light-cone finiteness supplies the exact full-row counts; it does not supply a universal comparison of the two rules.
- **Computed:** `python3 /tmp/op-lit/r40/r30check.py` evaluates the exact bitwise recurrences for `1 ≤ m < 8192`. The biconditional fails at exactly one index, 767, with difference −5. This is finite computational evidence, not an unbounded theorem.
- **Computed:** the same command gives `eps(2^k−1) = 0, 0, 0, −2, −9, −18, −60, −115, −242, −500, −1005, −1982, −4036` for `k = 1,…,13`. The finite observation in Remark 3 survives this check, including equality for k ≤ 3 and strict negativity for 4 ≤ k ≤ 8.
- **Open:** strict negativity at every Mersenne index for k ≥ 4 remains unsettled beyond k = 13. The result does not refute this weaker assertion.
- **Open:** whether additional non-Mersenne nonpositive indices recur at or beyond 8192, and the structural relation of the k = 10 exception to the Rule 22 closed form in Corollary 1.
- **Boundary:** the universal “non-positive exactly at the Mersenne indices” description cannot be used as an unconditional premise. This counterexample does not contradict the source’s independent Rule 22 closed form, its finite regression over m ≤ 128, or its observed pattern through 256. Extending the explanation of sign changes solely by Mersenne local maxima requires an additional argument; no such extension is proved here. No refutation of the paper’s other theorems is asserted.

## ASSUMED-UNVERIFIED

The literature search is bounded and does not prove that no later settlement exists. The exact interpretation of §9 is the all-positive-row biconditional preregistered in #12739. The finite sweep is independent computational evidence; its unbounded continuation, the all-Mersenne half and the Corollary 1 mechanism remain open.
