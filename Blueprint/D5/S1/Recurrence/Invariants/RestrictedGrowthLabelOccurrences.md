# Label Occurrences in Restricted-Growth Words

## Abstract

Restricted-growth words give Mathar's two closed label-occurrence counts.

Words are lists of natural labels stored in reverse chronological order. The first generated label is 1, and each next label lies from 1 through one more than the maximum already present. T(n,p) sums the number of occurrences of label p over all words of length n.

All arithmetic in the two closed forms is natural-number arithmetic. Subtraction is truncated natural subtraction. Each slash denotes the natural-number quotient, not rational division or a displayed fraction.

**Definition 1.1 (Largest label).**

$$\begin{aligned}maxLabel: \operatorname{List}(\mathbb{N}) \to \mathbb{N}\\\forall w \in \operatorname{List}(\mathbb{N}), \operatorname{maxLabel}(w) = \operatorname{foldr}(max,0,w)\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Invariants/RestrictedGrowthLabelOccurrences.maxLabel` (`✓ std3`).

*Citation.* R. J. Mathar (2016). *OEIS A270236, Triangle T(n,p): occurrences of p in the restricted growth functions of length n*. URL: <https://oeis.org/A270236>.

*Commentary.*

Folding maximum from zero returns the largest label, with value zero on the empty word.

**Definition 1.2 (Restricted-growth words).**

$$\begin{aligned}words: \mathbb{N} \to \operatorname{Finset}(\operatorname{List}(\mathbb{N}))\\\operatorname{words}(0) = \{[]\}\\\forall n \in \mathbb{N}, \operatorname{words}(n + 1) = \operatorname{biUnion}(\operatorname{words}(n),\lambda w, \operatorname{image}(\operatorname{Icc}(1,\operatorname{maxLabel}(w) + 1),\lambda x, \operatorname{cons}(x,w)))\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Invariants/RestrictedGrowthLabelOccurrences.words` (`✓ std3`).

*Citation.* R. J. Mathar (2016). *OEIS A270236, Triangle T(n,p): occurrences of p in the restricted growth functions of length n*. URL: <https://oeis.org/A270236>.

*Commentary.*

This reverse-chronological generator starts from the empty word. Each step prepends every label in the inclusive interval from 1 to one above the previous maximum. Its membership is identified with the source predicate by mem_words_iff.

**Definition 1.3 (Chronological restricted-growth predicate).**

$$\begin{aligned}IsRestrictedGrowth: \operatorname{List}(\mathbb{N}) \to Prop\\\forall f \in \operatorname{List}(\mathbb{N}), \operatorname{IsRestrictedGrowth}(f) \Leftrightarrow (f = [] \lor (\operatorname{head}(f) = 1 \land \forall j \in \mathbb{N}, j < \left|f\right| \Rightarrow (1 \le f_{j} \land f_{j} \le 1 + \operatorname{foldr}(max,0,\operatorname{take}(j,f)))))\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Invariants/RestrictedGrowthLabelOccurrences.IsRestrictedGrowth` (`✓ std3`).

*Citation.* R. J. Mathar (2016). *OEIS A270236, Triangle T(n,p): occurrences of p in the restricted growth functions of length n*. URL: <https://oeis.org/A270236>.

*Commentary.*

The empty list is admitted. A nonempty chronological list begins with 1, and every indexed label is positive and at most one plus the maximum of the preceding prefix.

**Theorem 1.4 (Generator membership equals the source predicate).**

$$\forall n \in \mathbb{N}, \forall w \in \operatorname{List}(\mathbb{N}), w \in \operatorname{words}(n) \Leftrightarrow (\left|w\right| = n \land \operatorname{IsRestrictedGrowth}(\operatorname{reverse}(w)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/RestrictedGrowthLabelOccurrences.mem_words_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A word belongs to the reverse-chronological generator at length n exactly when it has length n and its chronological reversal satisfies the restricted-growth predicate.

**Definition 1.5 (Total label occurrences).**

$$\begin{aligned}T: \mathbb{N} \to \mathbb{N} \to \mathbb{N}\\\forall n \in \mathbb{N}, \forall p \in \mathbb{N}, \operatorname{T}(n,p) = \sum_{w \in \operatorname{words}(n)} \operatorname{count}(w,p)\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Invariants/RestrictedGrowthLabelOccurrences.T` (`✓ std3`).

*Citation.* R. J. Mathar (2016). *OEIS A270236, Triangle T(n,p): occurrences of p in the restricted growth functions of length n*. URL: <https://oeis.org/A270236>.

*Commentary.*

For every length and label, this definition sums List.count over the finite set of restricted-growth words.

**Theorem 1.6 (The penultimate-label formula).**

$$\forall n \in \mathbb{N}, 1 < n \implies \operatorname{T}(n,n - 1) = 2 + n \cdot (n - 1) / 2$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/RestrictedGrowthLabelOccurrences.mathar_f1` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a270236-rgf-penultimate-label-count` (proved) by `D5/S1/Recurrence/Invariants/RestrictedGrowthLabelOccurrences.mathar_f1`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a270236-rgf-penultimate-label-count","declaration_gid":"D5/S1/Recurrence/Invariants/RestrictedGrowthLabelOccurrences.mathar_f1","resolution_kind":"proved"} -->

*Citation.* R. J. Mathar (2016). *OEIS A270236, Triangle T(n,p): occurrences of p in the restricted growth functions of length n*. URL: <https://oeis.org/A270236>.

*Commentary.*

The all-distinct word and the one-repeat maximum layer give one base occurrence, one occurrence for each chosen repeat pair, and one extra occurrence when the repeated label is the penultimate label.

**Theorem 1.7 (The antepenultimate-label formula).**

$$\forall n \in \mathbb{N}, 1 < n \implies \operatorname{T}(n + 1,n - 1) = 2 + n \cdot \left(n + 1\right) \cdot (3 \cdot n^{2} - 5 \cdot n + 26) / 24$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/RestrictedGrowthLabelOccurrences.mathar_f2` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a270236-rgf-antepenultimate-label-count` (proved) by `D5/S1/Recurrence/Invariants/RestrictedGrowthLabelOccurrences.mathar_f2`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a270236-rgf-antepenultimate-label-count","declaration_gid":"D5/S1/Recurrence/Invariants/RestrictedGrowthLabelOccurrences.mathar_f2","resolution_kind":"proved"} -->

*Citation.* R. J. Mathar (2016). *OEIS A270236, Triangle T(n,p): occurrences of p in the restricted growth functions of length n*. URL: <https://oeis.org/A270236>.

*Commentary.*

The label-extension sum separates the top three maximum layers. The two-repeat layer consists of one triple block or two paired blocks; the resulting binomial expression normalizes to the quotient by 24.

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/RestrictedGrowthLabelOccurrences.IsRestrictedGrowth`
- Truth anchor: `D5/S1/Recurrence/Invariants/RestrictedGrowthLabelOccurrences.T`
- Truth anchor: `D5/S1/Recurrence/Invariants/RestrictedGrowthLabelOccurrences.mathar_f1`
- Truth anchor: `D5/S1/Recurrence/Invariants/RestrictedGrowthLabelOccurrences.mathar_f2`
- Truth anchor: `D5/S1/Recurrence/Invariants/RestrictedGrowthLabelOccurrences.maxLabel`
- Truth anchor: `D5/S1/Recurrence/Invariants/RestrictedGrowthLabelOccurrences.mem_words_iff`
- Truth anchor: `D5/S1/Recurrence/Invariants/RestrictedGrowthLabelOccurrences.words`
