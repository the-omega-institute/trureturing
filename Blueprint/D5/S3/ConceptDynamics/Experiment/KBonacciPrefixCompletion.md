# KBonacci Prefix Completion

## Abstract

Exact recovery and classification of cumulative products with an unknown nonnegative reader.

**Definition 1.1 (World).**

$$\forall k: \mathbb{N}, \operatorname{World}(k) = \{(c,l): (\operatorname{Fin}(k) \to \mathbb{R}) \times (\operatorname{Fin}(k) \to \mathbb{R}) \Vert (\forall i: \operatorname{Fin}(k), 0 < c_{i}) \land (\forall i: \operatorname{Fin}(k), 0 \leq l_{i}) \land l \neq 0\}$$

*Formalization.* `D5/S3/ConceptDynamics/Experiment/KBonacciPrefixCompletion.World` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two factors are real vectors indexed by Fin k. Every object coordinate is strictly positive; the fixed reader is nonnegative and nonzero. Its support is unknown. No normalization or symmetry is imposed.

**Definition 1.2 (target).**

$$\forall k: \mathbb{N}, \forall w: \operatorname{World}(k), \forall i: \operatorname{Fin}(k), \forall t: \operatorname{Fin}(k), \operatorname{target}(w, i, t) = \operatorname{c}(w)_{i}\operatorname{ell}(w)_{t}$$

*Formalization.* `D5/S3/ConceptDynamics/Experiment/KBonacciPrefixCompletion.target` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The target is the initial outer product. Opposite rescaling of its two factors does not change this target.

**Definition 1.3 (cumulative).**

$$\forall k: \mathbb{N}, \forall c: \operatorname{Fin}(k) \to \mathbb{R}, \forall j: \mathbb{N}, \operatorname{cumulative}(c, j) = \sum_{i: \operatorname{Fin}(k), i < j}c_{i}$$

*Formalization.* `D5/S3/ConceptDynamics/Experiment/KBonacciPrefixCompletion.cumulative` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The cumulative value is the sum over coordinates smaller than the natural prefix length j. It is zero at j = 0 and strictly positive for each nonempty prefix of a positive object.

**Definition 1.4 (initial).**

$$\forall k: \mathbb{N}, \forall w: \operatorname{World}(k), \operatorname{initial}(w) = \sum_{i: \operatorname{Fin}(k)}\operatorname{c}(w)_{i}\operatorname{ell}(w)_{i}$$

*Formalization.* `D5/S3/ConceptDynamics/Experiment/KBonacciPrefixCompletion.initial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the mandatory preparation reading. Every preparation of the same object with the same reader has this value.

**Definition 1.5 (offDiagonal).**

$$\forall k: \mathbb{N}, \operatorname{offDiagonal}(k) = \{(r,t): \operatorname{Fin}(k) \times \operatorname{Fin}(k) \Vert r \neq t\}$$

*Formalization.* `D5/S3/ConceptDynamics/Experiment/KBonacciPrefixCompletion.offDiagonal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Row r denotes source prefix length j = r + 1. The off-diagonal set therefore omits precisely the source positions j = t + 1.

**Definition 1.6 (SameData).**

$$\forall k: \mathbb{N}, \forall S: \operatorname{Finset}(\operatorname{Fin}(k) \times \operatorname{Fin}(k)), \forall w: \operatorname{World}(k), \forall v: \operatorname{World}(k), \operatorname{SameData}(S, w, v) \iff (\operatorname{initial}(w) = \operatorname{initial}(v) \land \forall r: \operatorname{Fin}(k), \forall t: \operatorname{Fin}(k), (r,t) \in S \implies \operatorname{cumulative}(\operatorname{c}(w), r+1)\operatorname{ell}(w)_{t} = \operatorname{cumulative}(\operatorname{c}(v), r+1)\operatorname{ell}(v)_{t})$$

*Formalization.* `D5/S3/ConceptDynamics/Experiment/KBonacciPrefixCompletion.SameData` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Two worlds have the same selected data when their paid initial readings agree and every selected prefix product agrees. Repetitions add no distinct coordinate to this finite set.

**Definition 1.7 (Identifies).**

$$\forall k: \mathbb{N}, \forall S: \operatorname{Finset}(\operatorname{Fin}(k) \times \operatorname{Fin}(k)), \operatorname{Identifies}(S) \iff \forall w: \operatorname{World}(k), \forall v: \operatorname{World}(k), \operatorname{SameData}(S, w, v) \implies \forall i: \operatorname{Fin}(k), \forall t: \operatorname{Fin}(k), \operatorname{target}(w, i, t) = \operatorname{target}(v, i, t)$$

*Formalization.* `D5/S3/ConceptDynamics/Experiment/KBonacciPrefixCompletion.Identifies` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Identifiability means constancy of the initial relation on each selected-data fiber over the whole world domain.

**Definition 1.8 (column).**

$$\forall k: \mathbb{N}, \forall S: \operatorname{Finset}(\operatorname{Fin}(k) \times \operatorname{Fin}(k)), \forall t: \operatorname{Fin}(k), \operatorname{column}(S, t) = \{r: \operatorname{Fin}(k) \Vert (r,t) \in S\}$$

*Formalization.* `D5/S3/ConceptDynamics/Experiment/KBonacciPrefixCompletion.column` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A column contains the distinct selected prefix rows for one reader coordinate.

**Theorem 1.9 (Recovery on every nonempty reader support).**

$$\forall k: \mathbb{N}, 3 \leq k \implies \operatorname{Identifies}(\operatorname{offDiagonal}(k))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Experiment/KBonacciPrefixCompletion.off_diagonal_identifies` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Observed positive-prefix products determine exactly which reader coordinates vanish. With a single active coordinate t, the paid initial reading supplies its missing adjacent prefix increment, including the first and last coordinate boundaries.

With two active columns a and b, a third row is available because k is at least three. Products on that common row determine the relative reader scale. The other active column fills the missing row of column a, and every remaining column is then determined, including zero columns. Differences of adjacent cumulative products yield every initial relation entry.

**Theorem 1.10 (Classification at the distinct-product budget).**

$$\forall k: \mathbb{N}, 3 \leq k \implies \forall S: \operatorname{Finset}(\operatorname{Fin}(k) \times \operatorname{Fin}(k)), \operatorname{card}(S) \leq k(k-1) \implies (\operatorname{Identifies}(S) \iff S = \operatorname{offDiagonal}(k))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Experiment/KBonacciPrefixCompletion.endpoint_pattern_classification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A singleton-support reader forces at least k - 1 distinct prefixes in each column: otherwise the coordinate reading and those prefix sums have a nonzero common kernel direction. The positive objects with coordinates abs(h) + 1 and abs(h) + 1 + h realize a collision in the full world domain.

The budget forces exactly one omitted prefix in each column. A perturbation supported on adjacent object coordinates shows that this omission must lie next to the column index. Starting at the first column, a reader supported on two neighboring columns excludes the remaining incorrect omission. Thus every omitted row equals its column index.

This theorem concerns selected cumulative scalar products. The connection to literal legal words, sequential irreversible actions and ordered compulsory paid records is established separately by the actual-record theorem. No continuity or computational condition on a final decoder is used.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Experiment/KBonacciPrefixCompletion.Identifies`
- Truth anchor: `D5/S3/ConceptDynamics/Experiment/KBonacciPrefixCompletion.SameData`
- Truth anchor: `D5/S3/ConceptDynamics/Experiment/KBonacciPrefixCompletion.World`
- Truth anchor: `D5/S3/ConceptDynamics/Experiment/KBonacciPrefixCompletion.column`
- Truth anchor: `D5/S3/ConceptDynamics/Experiment/KBonacciPrefixCompletion.cumulative`
- Truth anchor: `D5/S3/ConceptDynamics/Experiment/KBonacciPrefixCompletion.endpoint_pattern_classification`
- Truth anchor: `D5/S3/ConceptDynamics/Experiment/KBonacciPrefixCompletion.initial`
- Truth anchor: `D5/S3/ConceptDynamics/Experiment/KBonacciPrefixCompletion.offDiagonal`
- Truth anchor: `D5/S3/ConceptDynamics/Experiment/KBonacciPrefixCompletion.off_diagonal_identifies`
- Truth anchor: `D5/S3/ConceptDynamics/Experiment/KBonacciPrefixCompletion.target`
