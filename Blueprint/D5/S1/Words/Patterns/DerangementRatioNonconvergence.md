# A Literal Negative Answer to Vatter's Question 4.3

## Abstract

Av(12) has one permutation per length and a nonconvergent derangement ratio.

Question 4.3 of Vincent Vatter's arXiv:2602.16355v2 asks whether the derangement ratio converges for every permutation class. This is a literal counterexample to the question as stated; the author may have had nontrivial (e.g. infinite-growth) classes in mind. The module claims only the refutation of the universally quantified statement. The literature provenance on the two answer nodes identifies the question, not a published negative answer; the counterexample and its proof are derived here.

Perm(n) denotes Equiv.Perm(Fin(n)), with positions numbered from zero. OrderEmbedding denotes an order embedding of positions. The record field mem is the length-indexed family; downset is its displayed closure law. rev(n) denotes Mathlib's Fin.revPerm, sending i to n-1-i. Every cardinality is Fintype.card. The quotient defining ratio is real division after casting both natural cardinalities to the reals. Length zero is included.

**Definition 1.1 (Pattern containment).**

$$\forall k, n: \mathbb{N}, \forall \sigma: \operatorname{Perm}\left(k\right), \forall \pi: \operatorname{Perm}\left(n\right), \operatorname{Contains}\left(\sigma, \pi\right) \Leftrightarrow (\exists f: \operatorname{OrderEmbedding}\left(\operatorname{Fin}\left(k\right), \operatorname{Fin}\left(n\right)\right), \forall i, j: \operatorname{Fin}\left(k\right), (\sigma\left(i\right) < \sigma\left(j\right) \Leftrightarrow \pi\left(f\left(i\right)\right) < \pi\left(f\left(j\right)\right)))$$

*Formalization.* `D5/S1/Words/Patterns/DerangementRatioNonconvergence.Contains` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An order embedding selects positions and preserves the relative order of the selected values in both directions.

**Definition 1.2 (Permutation classes as downsets).**

$$\operatorname{PermClass} = \{C \mid (\operatorname{mem}\left(C\right): (n: \mathbb{N}) \to \operatorname{Set}\left(\operatorname{Perm}\left(n\right)\right)) \land (\operatorname{downset}\left(C\right): \forall k, n: \mathbb{N}, \forall \sigma: \operatorname{Perm}\left(k\right), \forall \pi: \operatorname{Perm}\left(n\right), \pi \in \operatorname{mem}\left(C, n\right) \implies \operatorname{Contains}\left(\sigma, \pi\right) \implies \sigma \in \operatorname{mem}\left(C, k\right))\}$$

*Formalization.* `D5/S1/Words/Patterns/DerangementRatioNonconvergence.PermClass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This record has exactly the family mem and the proof field downset. The displayed record description gives the full type of both fields.

**Definition 1.3 (Fixed-point-free permutations).**

$$\forall n: \mathbb{N}, \forall \pi: \operatorname{Perm}\left(n\right), \operatorname{IsDerangement}\left(\pi\right) \Leftrightarrow (\forall i: \operatorname{Fin}\left(n\right), \pi\left(i\right) \neq i)$$

*Formalization.* `D5/S1/Words/Patterns/DerangementRatioNonconvergence.IsDerangement` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is membership in Mathlib's derangements set, whose definition is the displayed universal inequality.

**Definition 1.4 (The decreasing permutation class).**

$$\begin{aligned}\forall n: \mathbb{N}, \operatorname{mem}\left(\operatorname{Av12}, n\right) = \{\pi: \operatorname{Perm}\left(n\right) \mid (\forall i, j: \operatorname{Fin}\left(n\right), i < j \implies \pi\left(j\right) < \pi\left(i\right))\}\\\operatorname{downset}\left(\operatorname{Av12}\right): \forall k, n: \mathbb{N}, \forall \sigma: \operatorname{Perm}\left(k\right), \forall \pi: \operatorname{Perm}\left(n\right), \pi \in \operatorname{mem}\left(\operatorname{Av12}, n\right) \implies \operatorname{Contains}\left(\sigma, \pi\right) \implies \sigma \in \operatorname{mem}\left(\operatorname{Av12}, k\right)\end{aligned}$$

*Formalization.* `D5/S1/Words/Patterns/DerangementRatioNonconvergence.Av12` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A pattern of a decreasing permutation is decreasing: the position embedding takes i<j to f(i)<f(j), and the value-order equivalence transfers the reversed inequality back to the pattern. This supplies the downset field. Strict decrease is exactly avoidance of the increasing pattern 12.

**Theorem 1.5 (The unique member at every length).**

$$\forall n: \mathbb{N}, \forall \pi: \operatorname{Perm}\left(n\right), \pi \in \operatorname{mem}\left(\operatorname{Av12}, n\right) \Leftrightarrow \pi = \operatorname{rev}\left(n\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Patterns/DerangementRatioNonconvergence.av12_mem_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Composing a decreasing permutation with Fin.rev is strictly increasing. Mathlib's StrictMono.apply_eq on a finite linear order makes that composition the identity; applying reversal again identifies the permutation.

**Theorem 1.6 (The middle-position criterion).**

$$\forall n: \mathbb{N}, \forall i: \operatorname{Fin}\left(n\right), \operatorname{rev}\left(n\right)\left(i\right) = i \Leftrightarrow 2 \times \operatorname{val}\left(i\right) + 1 = n$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Patterns/DerangementRatioNonconvergence.rev_fixed_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The equality of Fin values is n-(i.val+1)=i.val. The bound i.val<n turns this into 2*i.val+1=n, with natural subtraction.

**Theorem 1.7 (Parity decides derangements).**

$$\forall n: \mathbb{N}, \operatorname{IsDerangement}\left(\operatorname{rev}\left(n\right)\right) \Leftrightarrow \operatorname{Even}\left(n\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Patterns/DerangementRatioNonconvergence.rev_isDerangement_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At odd length the proof constructs the position with value n div 2, proves it is in Fin(n), and uses the middle-position criterion to exhibit a fixed point. At even length that criterion is impossible. The empty permutation is a derangement by vacuity.

**Theorem 1.8 (One member at every length).**

$$\forall n: \mathbb{N}, \operatorname{card}\left(\operatorname{mem}\left(\operatorname{Av12}, n\right)\right) = 1$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Patterns/DerangementRatioNonconvergence.card_av12` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The membership characterization identifies each length slice with the singleton containing reversal.

**Theorem 1.9 (Count of derangements).**

$$\forall n: \mathbb{N}, \operatorname{card}\left(\{\pi: \operatorname{mem}\left(\operatorname{Av12}, n\right) \mid \operatorname{IsDerangement}\left(\operatorname{val}\left(\pi\right)\right)\}\right) = \operatorname{if} \operatorname{Even}\left(n\right) \operatorname{then} 1 \operatorname{else} 0$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Patterns/DerangementRatioNonconvergence.card_derangements_av12` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The underlying length slice is a subsingleton. At even length the proof constructs its derangement member; at odd length any alleged member contradicts the parity criterion.

**Definition 1.10 (The derangement ratio).**

$$\forall C: \operatorname{PermClass}, \forall n: \mathbb{N}, \operatorname{ratio}\left(C, n\right) = \frac{\operatorname{real}\left(\operatorname{card}\left(\{\pi: \operatorname{mem}\left(C, n\right) \mid \operatorname{IsDerangement}\left(\operatorname{val}\left(\pi\right)\right)\}\right)\right)}{\operatorname{real}\left(\operatorname{card}\left(\operatorname{mem}\left(C, n\right)\right)\right)}$$

*Formalization.* `D5/S1/Words/Patterns/DerangementRatioNonconvergence.ratio` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The numerator counts the subtype of members that are derangements. The denominator counts the entire length slice. Real division is total; for Av(12) the denominator is always one.

**Theorem 1.11 (The alternating ratio).**

$$\forall n: \mathbb{N}, \operatorname{ratio}\left(\operatorname{Av12}, n\right) = \operatorname{if} \operatorname{Even}\left(n\right) \operatorname{then} 1 \operatorname{else} 0$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Patterns/DerangementRatioNonconvergence.ratio_av12` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Substituting both cardinalities gives one at even length and zero at odd length. Thus the positive-length sequence begins 0,1,0,1.

**Theorem 1.12 (Av(12) has no ratio limit).**

$$\neg (\exists L: \mathbb{R}, \operatorname{Tendsto}\left(\operatorname{ratio}\left(\operatorname{Av12}\right), \operatorname{atTop}, \operatorname{nhds}\left(L\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Patterns/DerangementRatioNonconvergence.vatter_question_4_3_answer_no` (`✓ std3`). ∎

*Resolves.* `Problems/vatter-question-4-3-derangement-ratio` (refuted) by `D5/S1/Words/Patterns/DerangementRatioNonconvergence.vatter_question_4_3_answer_no`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"vatter-question-4-3-derangement-ratio","declaration_gid":"D5/S1/Words/Patterns/DerangementRatioNonconvergence.vatter_question_4_3_answer_no","resolution_kind":"refuted"} -->

*Citation.* Vincent Vatter (2026). *An Assortment of Problems in Permutation Patterns: Unimodality, Equivalence, Derangements, and Sorting*. URL: <https://arxiv.org/abs/2602.16355>.

*Commentary.*

Both index maps k to 2*k and k to 2*k+1 tend to atTop. The corresponding ratio subsequences are constantly one and zero. Uniqueness of real limits would force a putative common limit to equal both, a contradiction.

**Theorem 1.13 (The universal question is false).**

$$\exists C: \operatorname{PermClass}, \neg (\exists L: \mathbb{R}, \operatorname{Tendsto}\left(\operatorname{ratio}\left(C\right), \operatorname{atTop}, \operatorname{nhds}\left(L\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Patterns/DerangementRatioNonconvergence.exists_permClass_ratio_not_convergent` (`✓ std3`). ∎

*Citation.* Vincent Vatter (2026). *An Assortment of Problems in Permutation Patterns: Unimodality, Equivalence, Derangements, and Sorting*. URL: <https://arxiv.org/abs/2602.16355>.

*Commentary.*

Choose the downset Av(12). This refutes the question with no additional growth assumption; it makes no claim about restricted variants.

## References

- Truth anchor: `D5/S1/Words/Patterns/DerangementRatioNonconvergence.Av12`
- Truth anchor: `D5/S1/Words/Patterns/DerangementRatioNonconvergence.Contains`
- Truth anchor: `D5/S1/Words/Patterns/DerangementRatioNonconvergence.IsDerangement`
- Truth anchor: `D5/S1/Words/Patterns/DerangementRatioNonconvergence.PermClass`
- Truth anchor: `D5/S1/Words/Patterns/DerangementRatioNonconvergence.av12_mem_iff`
- Truth anchor: `D5/S1/Words/Patterns/DerangementRatioNonconvergence.card_av12`
- Truth anchor: `D5/S1/Words/Patterns/DerangementRatioNonconvergence.card_derangements_av12`
- Truth anchor: `D5/S1/Words/Patterns/DerangementRatioNonconvergence.exists_permClass_ratio_not_convergent`
- Truth anchor: `D5/S1/Words/Patterns/DerangementRatioNonconvergence.ratio`
- Truth anchor: `D5/S1/Words/Patterns/DerangementRatioNonconvergence.ratio_av12`
- Truth anchor: `D5/S1/Words/Patterns/DerangementRatioNonconvergence.rev_fixed_iff`
- Truth anchor: `D5/S1/Words/Patterns/DerangementRatioNonconvergence.rev_isDerangement_iff`
- Truth anchor: `D5/S1/Words/Patterns/DerangementRatioNonconvergence.vatter_question_4_3_answer_no`
