# First-zero paths

## Abstract

Literal first-zero lattice paths and row/column insertion.

Coordinates are labelled and steps are ordered. Each step decrements a nonempty subset by one. A path stops when any coordinate first reaches zero; simultaneous first zeros count once. Height zero or dimension zero admits only the empty path. The diagonal of this finite count is OEIS A263160. Write I(d,m,t) for the Lean internal_words count. The terminal-word identity and uniform estimates lead to its exact real-root limit along all natural indices. The proof uses only the cofinite range n at least two and imposes no fixed-dimension hypothesis.

**Definition 1.1 (Nonempty coordinate steps).**

$$\forall d \in \mathbb{N},\; \operatorname{Step}\left(d\right) = \operatorname{Subtype}\left((s: \operatorname{Finset}\left(\operatorname{Fin}\left(d\right)\right) \mapsto \operatorname{Finset}.\operatorname{Nonempty}\left(s\right))\right)$$

*Formalization.* `D5/S1/Words/LatticePaths/KotesovecA263160.Step` (`✓ std3`).

*Citation.* Vaclav Kotesovec; Alois P. Heinz; Vladeta Jovovic (2026). *OEIS A263160: diagonal first-zero lattice paths*. URL: <https://oeis.org/A263160>.

*Commentary.*

The displayed formula specifies the objects and their ordered finite counts.

**Definition 1.2 (Coordinate occurrences).**

$$\forall d \in \mathbb{N},\; \forall w \in \operatorname{List}\left(\operatorname{Step}\left(d\right)\right),\; \forall i \in \operatorname{Fin}\left(d\right),\; \operatorname{decrements}\left(w, i\right) = \operatorname{List}.\operatorname{countP}\left((s: \operatorname{Step}\left(d\right) \mapsto \operatorname{decide}\left(i \in \operatorname{Subtype}.\operatorname{val}\left(s\right)\right)), w\right)$$

*Formalization.* `D5/S1/Words/LatticePaths/KotesovecA263160.decrements` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the objects and their ordered finite counts.

**Definition 1.3 (First-zero termination).**

$$\forall d \in \mathbb{N},\; \forall h \in \mathbb{N},\; \forall w \in \operatorname{List}\left(\operatorname{Step}\left(d\right)\right),\; \operatorname{FirstZero}\left(h, w\right) = \operatorname{ite}\left((h = 0) \lor (d = 0), w = \operatorname{List}.\operatorname{nil}\left(\right), (\forall r \in \mathbb{N},\; (r < \operatorname{List}.\operatorname{length}\left(w\right)) \Rightarrow (\forall i \in \operatorname{Fin}\left(d\right),\; \operatorname{decrements}\left(\operatorname{List}.\operatorname{take}\left(r, w\right), i\right) < h)) \land (\exists i \in \operatorname{Fin}\left(d\right),\; \operatorname{decrements}\left(w, i\right) = h)\right)$$

*Formalization.* `D5/S1/Words/LatticePaths/KotesovecA263160.FirstZero` (`✓ std3`).

*Citation.* Vaclav Kotesovec; Alois P. Heinz; Vladeta Jovovic (2026). *OEIS A263160: diagonal first-zero lattice paths*. URL: <https://oeis.org/A263160>.

*Commentary.*

The displayed formula specifies the objects and their ordered finite counts.

**Definition 1.4 (The literal finite path count).**

$$\forall d \in \mathbb{N},\; \forall h \in \mathbb{N},\; \operatorname{paths}\left(d, h\right) = \sum_{t \in \operatorname{Finset}.\operatorname{range}\left(d \cdot h + 1\right)} \operatorname{Fintype}.\operatorname{card}\left(\operatorname{Subtype}\left((w: \operatorname{Fin}\left(t\right) \to \operatorname{Step}\left(d\right) \mapsto \operatorname{FirstZero}\left(h, \operatorname{List}.\operatorname{ofFn}\left(w\right)\right))\right)\right)$$

*Formalization.* `D5/S1/Words/LatticePaths/KotesovecA263160.paths` (`✓ std3`).

*Citation.* Vaclav Kotesovec; Alois P. Heinz; Vladeta Jovovic (2026). *OEIS A263160: diagonal first-zero lattice paths*. URL: <https://oeis.org/A263160>.

*Commentary.*

The displayed formula specifies the objects and their ordered finite counts.

**Definition 1.5 (The diagonal sequence).**

$$\forall n \in \mathbb{N},\; \operatorname{a}\left(n\right) = \operatorname{paths}\left(n, n\right)$$

*Formalization.* `D5/S1/Words/LatticePaths/KotesovecA263160.a` (`✓ std3`).

*Citation.* Vaclav Kotesovec; Alois P. Heinz; Vladeta Jovovic (2026). *OEIS A263160: diagonal first-zero lattice paths*. URL: <https://oeis.org/A263160>.

*Commentary.*

The displayed formula specifies the objects and their ordered finite counts.

**Definition 1.6 (Internal words with bounded rows).**

$$\forall d \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall t \in \mathbb{N},\; \operatorname{I}\left(d, m, t\right) = \operatorname{Fintype}.\operatorname{card}\left(\operatorname{Subtype}\left((w: \operatorname{Fin}\left(t\right) \to \operatorname{Step}\left(d\right) \mapsto \forall i \in \operatorname{Fin}\left(d\right),\; \operatorname{decrements}\left(\operatorname{List}.\operatorname{ofFn}\left(w\right), i\right) \le m)\right)\right)$$

*Formalization.* `D5/S1/Words/LatticePaths/KotesovecA263160.internal_words` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the objects and their ordered finite counts.

**Theorem 1.7 (A finite path-length budget).**

$$\forall d \in \mathbb{N},\; \forall h \in \mathbb{N},\; \forall w \in \operatorname{List}\left(\operatorname{Step}\left(d\right)\right),\; (\operatorname{FirstZero}\left(h, w\right)) \Rightarrow (\operatorname{List}.\operatorname{length}\left(w\right) \le d \cdot h)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/LatticePaths/KotesovecA263160.first_zero_length_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every step uses at least one coordinate. Before the last step, each coordinate has been used at most one less than the initial height. This bounds the length and makes the displayed finite count exhaustive.

**Theorem 1.8 (Transposing rows and inserting empty columns).**

$$\forall d \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall k \in \mathbb{N},\; (\sum_{r \in \operatorname{Finset}.\operatorname{range}\left(m + 1\right)} \operatorname{Nat}.\operatorname{choose}\left(k, r\right))^{d} = \sum_{t \in \operatorname{Finset}.\operatorname{range}\left(k + 1\right)} \operatorname{Nat}.\operatorname{choose}\left(k, t\right) \cdot \operatorname{I}\left(d, m, t\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/LatticePaths/KotesovecA263160.insertion_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A row chooses at most m positions among k labelled columns. Transposition identifies these independent rows with columns that may be empty. Removing the empty columns gives an internal word; choosing its positions gives the binomial coefficient.

**Theorem 1.9 (A positive geometric series).**

$$\forall d \in \mathbb{N},\; \forall m \in \mathbb{N},\; \operatorname{HasSum}\left((k: \mathbb{N} \mapsto (\frac{1}{2})^{k} \cdot (\operatorname{Nat}.\operatorname{cast}\left(\sum_{r \in \operatorname{Finset}.\operatorname{range}\left(m + 1\right)} \operatorname{Nat}.\operatorname{choose}\left(k, r\right)\right))^{d}), 2 \cdot \sum_{t \in \operatorname{Finset}.\operatorname{range}\left(d \cdot m + 1\right)} \operatorname{Nat}.\operatorname{cast}\left(\operatorname{I}\left(d, m, t\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/LatticePaths/KotesovecA263160.internal_hasSum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the objects and their ordered finite counts.

**Theorem 1.10 (The literal terminal count).**

$$\forall d \in \mathbb{N},\; \forall m \in \mathbb{N},\; (0 < d) \Rightarrow (\operatorname{paths}\left(d, m + 1\right) = 1 + \left((2)^{d} - 2\right) \cdot \sum_{t \in \operatorname{Finset}.\operatorname{range}\left(d \cdot m + 1\right)} \operatorname{I}\left(d, m, t\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/LatticePaths/KotesovecA263160.paths_eq_internal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the objects and their ordered finite counts.

**Theorem 1.11 (A uniform factorial upper bound).**

$$\forall d \in \mathbb{N},\; \forall m \in \mathbb{N},\; 2 \cdot \sum_{t \in \operatorname{Finset}.\operatorname{range}\left(d \cdot m + 1\right)} \operatorname{Nat}.\operatorname{cast}\left(\operatorname{I}\left(d, m, t\right)\right) \le \frac{(2)^{m + 1} \cdot \operatorname{Nat}.\operatorname{cast}\left(\operatorname{Nat}.\operatorname{factorial}\left(m \cdot d\right)\right)}{(\operatorname{Real}.\operatorname{log}\left(2\right))^{m \cdot d + 1} \cdot (\operatorname{Nat}.\operatorname{cast}\left(\operatorname{Nat}.\operatorname{factorial}\left(m\right)\right))^{d}}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/LatticePaths/KotesovecA263160.internal_count_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the objects and their ordered finite counts.

**Theorem 1.12 (A one-term lower bound).**

$$\forall d \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall k \in \mathbb{N},\; \frac{(\frac{1}{2})^{k} \cdot (\operatorname{Nat}.\operatorname{cast}\left(k + 1 - m\right))^{m \cdot d}}{(\operatorname{Nat}.\operatorname{cast}\left(\operatorname{Nat}.\operatorname{factorial}\left(m\right)\right))^{d}} \le 2 \cdot \sum_{t \in \operatorname{Finset}.\operatorname{range}\left(d \cdot m + 1\right)} \operatorname{Nat}.\operatorname{cast}\left(\operatorname{I}\left(d, m, t\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/LatticePaths/KotesovecA263160.internal_count_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the objects and their ordered finite counts.

**Theorem 1.13 (Logarithmic factorial bounds).**

$$\forall d \in \mathbb{N},\; \forall m \in \mathbb{N},\; (0 < d) \Rightarrow ((0 < m) \Rightarrow ((\operatorname{Nat}.\operatorname{cast}\left(m \cdot d\right) \cdot \operatorname{Real}.\operatorname{log}\left(\frac{\operatorname{Nat}.\operatorname{cast}\left(m \cdot d\right)}{\operatorname{Real}.\operatorname{log}\left(2\right)}\right) - \operatorname{Nat}.\operatorname{cast}\left(m \cdot d\right) - \left(\operatorname{Nat}.\operatorname{cast}\left(m\right) + 1\right) \cdot \operatorname{Real}.\operatorname{log}\left(2\right) - \operatorname{Nat}.\operatorname{cast}\left(d\right) \cdot \operatorname{Real}.\operatorname{log}\left(\operatorname{Nat}.\operatorname{cast}\left(\operatorname{Nat}.\operatorname{factorial}\left(m\right)\right)\right) \le \operatorname{Real}.\operatorname{log}\left(2 \cdot \sum_{t \in \operatorname{Finset}.\operatorname{range}\left(d \cdot m + 1\right)} \operatorname{Nat}.\operatorname{cast}\left(\operatorname{I}\left(d, m, t\right)\right)\right)) \land (\operatorname{Real}.\operatorname{log}\left(2 \cdot \sum_{t \in \operatorname{Finset}.\operatorname{range}\left(d \cdot m + 1\right)} \operatorname{Nat}.\operatorname{cast}\left(\operatorname{I}\left(d, m, t\right)\right)\right) \le \left(\operatorname{Nat}.\operatorname{cast}\left(m\right) + 1\right) \cdot \operatorname{Real}.\operatorname{log}\left(2\right) + \operatorname{Real}.\operatorname{log}\left(\operatorname{Nat}.\operatorname{cast}\left(\operatorname{Nat}.\operatorname{factorial}\left(m \cdot d\right)\right)\right) - \left(\operatorname{Nat}.\operatorname{cast}\left(m \cdot d\right) + 1\right) \cdot \operatorname{Real}.\operatorname{log}\left(\operatorname{Real}.\operatorname{log}\left(2\right)\right) - \operatorname{Nat}.\operatorname{cast}\left(d\right) \cdot \operatorname{Real}.\operatorname{log}\left(\operatorname{Nat}.\operatorname{cast}\left(\operatorname{Nat}.\operatorname{factorial}\left(m\right)\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/LatticePaths/KotesovecA263160.internal_log_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the objects and their ordered finite counts.

**Theorem 1.14 (A quantitative diagonal error).**

$$\forall n \in \mathbb{N},\; (2 \le n) \Rightarrow (\left|\operatorname{Real}.\operatorname{log}\left(\operatorname{Nat}.\operatorname{cast}\left(\operatorname{a}\left(n\right)\right)\right) - (\operatorname{Nat}.\operatorname{cast}\left(n\right))^{2} \cdot \left(\operatorname{Real}.\operatorname{log}\left(\operatorname{Nat}.\operatorname{cast}\left(n\right)\right) - \operatorname{Real}.\operatorname{log}\left(\operatorname{Real}.\operatorname{log}\left(2\right)\right)\right)\right| \le \operatorname{Nat}.\operatorname{cast}\left(n\right) \cdot \left(4 \cdot \operatorname{Real}.\operatorname{log}\left(\operatorname{Nat}.\operatorname{cast}\left(n\right)\right) + 6 + 2 \cdot \left|\operatorname{Real}.\operatorname{log}\left(\operatorname{Real}.\operatorname{log}\left(2\right)\right)\right|\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/LatticePaths/KotesovecA263160.diagonal_log_estimate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the objects and their ordered finite counts.

**Theorem 1.15 (The complete diagonal real-root limit).**

$$\operatorname{Tendsto}\left((n: \mathbb{N} \mapsto \frac{\operatorname{Real}.\operatorname{rpow}\left(\operatorname{Nat}.\operatorname{cast}\left(\operatorname{a}\left(n\right)\right), \frac{1}{(\operatorname{Nat}.\operatorname{cast}\left(n\right))^{2}}\right)}{\operatorname{Nat}.\operatorname{cast}\left(n\right)}), atTop, \operatorname{nhds}\left(\frac{1}{\operatorname{Real}.\operatorname{log}\left(2\right)}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/LatticePaths/KotesovecA263160.diagonal_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the objects and their ordered finite counts.

## References

- Truth anchor: `D5/S1/Words/LatticePaths/KotesovecA263160.FirstZero`
- Truth anchor: `D5/S1/Words/LatticePaths/KotesovecA263160.Step`
- Truth anchor: `D5/S1/Words/LatticePaths/KotesovecA263160.a`
- Truth anchor: `D5/S1/Words/LatticePaths/KotesovecA263160.decrements`
- Truth anchor: `D5/S1/Words/LatticePaths/KotesovecA263160.diagonal_limit`
- Truth anchor: `D5/S1/Words/LatticePaths/KotesovecA263160.diagonal_log_estimate`
- Truth anchor: `D5/S1/Words/LatticePaths/KotesovecA263160.first_zero_length_bound`
- Truth anchor: `D5/S1/Words/LatticePaths/KotesovecA263160.insertion_identity`
- Truth anchor: `D5/S1/Words/LatticePaths/KotesovecA263160.internal_count_lower`
- Truth anchor: `D5/S1/Words/LatticePaths/KotesovecA263160.internal_count_upper`
- Truth anchor: `D5/S1/Words/LatticePaths/KotesovecA263160.internal_hasSum`
- Truth anchor: `D5/S1/Words/LatticePaths/KotesovecA263160.internal_log_bounds`
- Truth anchor: `D5/S1/Words/LatticePaths/KotesovecA263160.internal_words`
- Truth anchor: `D5/S1/Words/LatticePaths/KotesovecA263160.paths`
- Truth anchor: `D5/S1/Words/LatticePaths/KotesovecA263160.paths_eq_internal`
- Dependency: [D5/S1/Words/LatticePaths/MatharA379464Counting](MatharA379464Counting.md)
