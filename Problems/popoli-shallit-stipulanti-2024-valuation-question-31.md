---
slug: popoli-shallit-stipulanti-2024-valuation-question-31
bibkey: popolishallitstipulanti2024additive
doi: 10.4230/LIPIcs.FSTTCS.2024.32
url: https://arxiv.org/abs/2410.02409v1
triage: theorem
motivation_gids:
  - D5/S1/Words/Complexity/PSSValuationRefutation
---

# Natural valuations cannot preserve every abelian complexity function

## Problem

Popoli, Shallit and Stipulanti, *Additive word complexity and Walnut*,
arXiv:2410.02409v1, Section 5, Question 31, PDF page 15, ask:

> Given an alphabet A, is there a valuation such that the additive complexity
> of a given sequence is equal to its abelian complexity?

The preceding definition is:

> A map v:A→ℕ is called a valuation over an alphabet A.

The identical question is HTML Section 4, Question 30, element
`Thmtheorem30`, and official FSTTCS 2024 Question 31, printed page 32:14,
DOI 10.4230/LIPIcs.FSTTCS.2024.32. The full general assertion was
preregistered in [#23272](https://github.com/the-omega-institute/trureturing/issues/23272).

### Statement echo

| Source clause | Formal counterpart |
| --- | --- |
| Every finite alphabet and each given infinite sequence | Closed `claim`: every `A : Type` with `[Fintype A]` and every `w : ℕ → A`. |
| One-sided infinite word, indexed from zero | The function `w`; the witness `universalWord : ℕ → Fin 3` is defined at every natural index. |
| Ordinary contiguous length-n factors | Reused `MorseHedlund.wordFactor` and `wordFactorSet`, with every natural starting index. |
| Abelian equivalence of original symbols | `parikh` counts every original letter; `parikhSet` takes its finite image. `List.perm_iff_count` identifies equal counts with permutation. |
| A valuation into the natural numbers | `v : A → ℕ`, including zero, equal and repeated weights; the alphabet is retained. |
| Additive equivalence | `sumSet` is the finite image of actual factors under the sum of their letter values. |
| Equality of complexities at all lengths | `∀ n : ℕ, additiveComplexity w v n = abelianComplexity w n`; length zero is included. |
| General existence order | `∀ A, ∀ w, ∃ v, ∀ n`; the witness word is fixed before any valuation is extracted. |
| Negative answer | The only public theorem is literally `result : ¬ claim`. |

No recurrence, automaticity, morphicity or balancedness restriction is
present in the original question. Its neighboring positive results have
their own hypotheses.

## Motivation

A scalar evaluation can identify two different original-symbol Parikh
vectors. A fixed ternary word containing every finite ternary word makes
this obstruction available against every choice of natural weights.
The question concerns the entire complexity function, so one positive
length of strict loss defeats each valuation.

## Gap

The source leaves this general valuation-existence question open. The
bounded source, literature and all-state ownership qualification supplied
with #23272 identified no exact posted settlement or other person's exact
registration in its inspected scope. This is not a worldwide absence or
priority certificate. Issues #22635 and #23244 concern the distinct
Sahasrabudhe universal-input finite-morphism target and are excluded from
this undertaking.

## Route

Concatenate every decoded finite ternary list, appending a zero to each
block. Positive block lengths make the boundaries strictly increasing and
unbounded. A least-boundary construction defines the actual infinite
word, and `Encodable.encodek` proves that each finite list occurs at its
own encoded block boundary.

For an arbitrary valuation write its three weights as `(a,b,c)`. If they
are not all equal, the factors with Parikh vectors `(b,c,a)` and `(c,a,b)`
have the same positive length `a+b+c` and the same weighted sum. Their
vectors are distinct, since equality would force `a=b=c`. Constant
valuations already identify the distinct singleton factors `[0]` and
`[1]`, including the all-zero valuation.

Both complexity sets are finite images of the same actual factor set.
The weighted image of `parikhSet` equals `sumSet`. Noninjectivity on that
finite set therefore gives strictly smaller additive cardinality at the
same positive length.

## Falsifier

A valuation on the fixed `universalWord` preserving its original-symbol
abelian complexity at every length would contradict the result. A missing
occurrence bridge, a valuation-dependent witness word, a collapsed
symbolic alphabet, or a source restriction omitted from `claim` would
invalidate the claimed resolution. The construction and proof address
these clauses directly.

## Evidence

`D5/S1/Words/Complexity/PSSValuationRefutation.result` proves the literal
negation of the closed `claim`. Its live private proof path contains
`universal_occurrence`, `sum_eq_weighted`, `sums_image`, `collision` and
`universal_failure`. The latter proves that every natural valuation of
this same word loses cardinality at some positive length.

The source and proof use the existing finite factor interface from
`D5/S1/Words/Complexity/MorseHedlund`. Direct pinned Mathlib suppliers
include `Encodable.encodek`, `Finset.sum_list_map_count`,
`Finset.sum_subset`, `Finset.card_image_le` and `Finset.card_image_iff`.
The source bridge for permutation is `List.perm_iff_count`.

The proof is conservatively classified `bind-only`; admission is
`open-problem-resolution` for the whole preregistered external question.
Every retained helper is consumed on the result's live proof path. The
only public theorem is the designated literal refutation result and uses
the existing four-slot escape-registration exemption. No Reg mirror or
`declared_validated` registration is asserted.

## Triage

### What the settlement shows

**Proved:** `D5/S1/Words/Complexity/PSSValuationRefutation.result` refutes
the entire general assertion. The private `universal_failure` on its live
proof path establishes one fixed actual ternary word defeating every
natural valuation at some common positive factor length.

**Proved mechanism:** private `collision` supplies two original-symbol
classes with equal evaluation; private `sums_image` and
`universal_failure` turn that loss of injectivity into strict finite
cardinality loss. The obstruction is compatible with zero and repeated
weights and does not use a finite observation window.

**Source results, not new repository theorems:** the source's Theorems 32
and 33 give positive answers for a specified Thue–Morse variant and for
C-balanced words, respectively. The present refutation does not refute
those restricted conclusions. No source theorem depending on an
affirmative solution of Question 31 was identified in the supplied
complete-source review. An inference of an unrestricted affirmative
answer from those special cases is ruled out by `result`.

**Open here:** a characterization of all individual words admitting a
suitable valuation, optimal weights in the source's positive cases, and
additional restricted positive theorems. None is required to negate the
unrestricted existence assertion, and none is added to the settling
module.

## ASSUMED-UNVERIFIED

Literature completeness, external priority and worldwide absence of
other settlements are ASSUMED-UNVERIFIED. The bounded supplied
qualification and separate prefreeze approval are fallible evidence.
Final independent publication review and exact-head required CI are
separate gates; this dossier grants no merge or external-resolution
credit.
