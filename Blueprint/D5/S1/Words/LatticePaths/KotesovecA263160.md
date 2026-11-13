# First-zero paths

## Abstract

Literal first-zero lattice paths and row/column insertion.

Coordinates are labelled and steps are ordered. Each step decrements a nonempty subset by one. A path stops when any coordinate first reaches zero; simultaneous first zeros count once. Height zero or dimension zero admits only the empty path. The diagonal of this finite count is OEIS A263160. Write I(d,m,t) for the Lean internal_words count. The terminal-word identity and uniform estimates lead to its exact real-root limit along all natural indices. The proof uses only the cofinite range n at least two and imposes no fixed-dimension hypothesis.

The preregistered source is the historical A263160 revision 21 limit, added in history revision 17. Current revision 24, timestamped 2026-11-13 16:51:52 Singapore time, instead asserts a(n) asymptotic to c times n to the power n times (n minus three halves) plus one, divided by Pi to the power n/2 and log(2) to the power n times (n minus one), with c = 10.75366283..., signed Vaclav Kotesovec. History revision 22 deletes the conjecture line, revision 23 adds this stronger assertion and revision 24 approves it. The directly read JSON and history give no proof, exact constant definition or error bound. Public proof coverage remains ASSUMED-UNVERIFIED; editorial approval and cached conjecture snippets do not settle it. The historical target and the Lean limit remain the scope here; no first-proof or numerical-fit claim is made.

The endpoint binomial-moment representation is prior Dima/A126086, Eger arXiv:1511.00622v2 section 5.5 equation (3), page 10, and Bala/A262809. It permits arbitrary finite positive dimension and prescribed endpoints; summing endpoints over a box yields the truncated-binomial moment here. This counting representation is not a new external mathematical solution. The read GHOW1990 author PDF, pages 133–146, DOI 10.1007/BF01787724, has a fixed-k endpoint asymptotic with O_k error. The read Caughman2011 author text, DOI 10.1016/j.disc.2011.04.024, has exact endpoint formulas allowing arbitrary finite dimension. The required uniform first-zero diagonal theorem was not found in that searched scope.

A262810 revision 19 already asserts a height-equals-dimension diagonal asymptotic. Its public history revision 12, March 23, 2016, was read; revision 13 is approval, not a proof. Targeted author-paper, note and history reading found no proof source or first-zero logarithmic transfer in the searched scope. This growing-dimension assertion is not excluded as fixed-dimension work. The existing full Lean proof is retained. Independent review, freeze, supplier repin and delivery remain pending; the source-bound Reg audit is unfinished under issue #29924, and no resolved-problem KPI is claimed. The Library note records current and historical source response identities.

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

$$\forall d \in \mathbb{N},\; \forall h \in \mathbb{N},\; \forall w \in \operatorname{List}\left(\operatorname{Step}\left(d\right)\right),\; (\operatorname{FirstZero}\left(h, w\right)) \Rightarrow (\operatorname{List}.\operatorname{length}\left(w\right) \le d \cdot \left(h - 1\right) + 1)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/LatticePaths/KotesovecA263160.first_zero_length_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every step uses at least one coordinate. Before the last step, each coordinate has been used at most h minus one times, so the length is at most d times (h minus one), plus one. This is the cutoff in the terminal-word sum. Height zero or dimension zero still admits only the empty path; for positive height and dimension the cutoff is at most d times h, making the finite count exhaustive.

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

The length budget truncates the insertion polynomial at d times m. The resulting moment representation is prior endpoint-counting work as attributed above. Each geometric binomial column has sum two. Exchanging the finite sum with the convergent series gives twice the internal-word count.

**Theorem 1.10 (The literal terminal count).**

$$\forall d \in \mathbb{N},\; \forall m \in \mathbb{N},\; (0 < d) \Rightarrow (\operatorname{paths}\left(d, m + 1\right) = 1 + \left((2)^{d} - 2\right) \cdot \sum_{t \in \operatorname{Finset}.\operatorname{range}\left(d \cdot m + 1\right)} \operatorname{I}\left(d, m, t\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/LatticePaths/KotesovecA263160.paths_eq_internal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Appending a nonempty coordinate subset to an internal word either remains internal or reaches its first zero. These cases partition words, including simultaneous first zeros. Summing over lengths cancels the nonempty internal words and retains the unique empty word.

**Theorem 1.11 (A uniform factorial upper bound).**

$$\forall d \in \mathbb{N},\; \forall m \in \mathbb{N},\; 2 \cdot \sum_{t \in \operatorname{Finset}.\operatorname{range}\left(d \cdot m + 1\right)} \operatorname{Nat}.\operatorname{cast}\left(\operatorname{I}\left(d, m, t\right)\right) \le \frac{(2)^{m + 1} \cdot \operatorname{Nat}.\operatorname{cast}\left(\operatorname{Nat}.\operatorname{factorial}\left(m \cdot d\right)\right)}{(\operatorname{Real}.\operatorname{log}\left(2\right))^{m \cdot d + 1} \cdot (\operatorname{Nat}.\operatorname{cast}\left(\operatorname{Nat}.\operatorname{factorial}\left(m\right)\right))^{d}}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/LatticePaths/KotesovecA263160.internal_count_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Vandermonde and the factorial binomial bound dominate each row polynomial by the shifted degree-m monomial divided by m factorial. A shift by m reduces the geometric moment to Mathlib's sum-integral and Gamma estimate. The polynomial and exponential are compared as separate monotone factors.

**Theorem 1.12 (A one-term lower bound).**

$$\forall d \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall k \in \mathbb{N},\; \frac{(\frac{1}{2})^{k} \cdot (\operatorname{Nat}.\operatorname{cast}\left(k + 1 - m\right))^{m \cdot d}}{(\operatorname{Nat}.\operatorname{cast}\left(\operatorname{Nat}.\operatorname{factorial}\left(m\right)\right))^{d}} \le 2 \cdot \sum_{t \in \operatorname{Finset}.\operatorname{range}\left(d \cdot m + 1\right)} \operatorname{Nat}.\operatorname{cast}\left(\operatorname{I}\left(d, m, t\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/LatticePaths/KotesovecA263160.internal_count_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every term of the positive series is at most its sum. The lower factorial bound for the binomial coefficient supplies the displayed term. Subtraction inside the natural-number cast is truncated natural subtraction.

**Theorem 1.13 (Logarithmic factorial bounds).**

$$\forall d \in \mathbb{N},\; \forall m \in \mathbb{N},\; (0 < d) \Rightarrow ((0 < m) \Rightarrow ((\operatorname{Nat}.\operatorname{cast}\left(m \cdot d\right) \cdot \operatorname{Real}.\operatorname{log}\left(\frac{\operatorname{Nat}.\operatorname{cast}\left(m \cdot d\right)}{\operatorname{Real}.\operatorname{log}\left(2\right)}\right) - \operatorname{Nat}.\operatorname{cast}\left(m \cdot d\right) - \left(\operatorname{Nat}.\operatorname{cast}\left(m\right) + 1\right) \cdot \operatorname{Real}.\operatorname{log}\left(2\right) - \operatorname{Nat}.\operatorname{cast}\left(d\right) \cdot \operatorname{Real}.\operatorname{log}\left(\operatorname{Nat}.\operatorname{cast}\left(\operatorname{Nat}.\operatorname{factorial}\left(m\right)\right)\right) \le \operatorname{Real}.\operatorname{log}\left(2 \cdot \sum_{t \in \operatorname{Finset}.\operatorname{range}\left(d \cdot m + 1\right)} \operatorname{Nat}.\operatorname{cast}\left(\operatorname{I}\left(d, m, t\right)\right)\right)) \land (\operatorname{Real}.\operatorname{log}\left(2 \cdot \sum_{t \in \operatorname{Finset}.\operatorname{range}\left(d \cdot m + 1\right)} \operatorname{Nat}.\operatorname{cast}\left(\operatorname{I}\left(d, m, t\right)\right)\right) \le \left(\operatorname{Nat}.\operatorname{cast}\left(m\right) + 1\right) \cdot \operatorname{Real}.\operatorname{log}\left(2\right) + \operatorname{Real}.\operatorname{log}\left(\operatorname{Nat}.\operatorname{cast}\left(\operatorname{Nat}.\operatorname{factorial}\left(m \cdot d\right)\right)\right) - \left(\operatorname{Nat}.\operatorname{cast}\left(m \cdot d\right) + 1\right) \cdot \operatorname{Real}.\operatorname{log}\left(\operatorname{Real}.\operatorname{log}\left(2\right)\right) - \operatorname{Nat}.\operatorname{cast}\left(d\right) \cdot \operatorname{Real}.\operatorname{log}\left(\operatorname{Nat}.\operatorname{cast}\left(\operatorname{Nat}.\operatorname{factorial}\left(m\right)\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/LatticePaths/KotesovecA263160.internal_log_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the lower estimate take k equal to the ceiling of m times d divided by log two, plus m. The ceiling error costs at most one exponential step. Taking logarithms of that term and of the uniform upper bound gives the sandwich.

**Theorem 1.14 (A quantitative diagonal error).**

$$\forall n \in \mathbb{N},\; (2 \le n) \Rightarrow (\left|\operatorname{Real}.\operatorname{log}\left(\operatorname{Nat}.\operatorname{cast}\left(\operatorname{a}\left(n\right)\right)\right) - (\operatorname{Nat}.\operatorname{cast}\left(n\right))^{2} \cdot \left(\operatorname{Real}.\operatorname{log}\left(\operatorname{Nat}.\operatorname{cast}\left(n\right)\right) - \operatorname{Real}.\operatorname{log}\left(\operatorname{Real}.\operatorname{log}\left(2\right)\right)\right)\right| \le \operatorname{Nat}.\operatorname{cast}\left(n\right) \cdot \left(4 \cdot \operatorname{Real}.\operatorname{log}\left(\operatorname{Nat}.\operatorname{cast}\left(n\right)\right) + 6 + 2 \cdot \left|\operatorname{Real}.\operatorname{log}\left(\operatorname{Real}.\operatorname{log}\left(2\right)\right)\right|\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/LatticePaths/KotesovecA263160.diagonal_log_estimate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Set d to n and m to n minus one. Mathlib's factorial-log bounds cancel the main factorial terms. The terminal-count comparison contributes only a linear error; the displayed bound is at most a constant times n log n.

**Theorem 1.15 (The complete diagonal real-root limit).**

$$\operatorname{Tendsto}\left((n: \mathbb{N} \mapsto \frac{\operatorname{Real}.\operatorname{rpow}\left(\operatorname{Nat}.\operatorname{cast}\left(\operatorname{a}\left(n\right)\right), \frac{1}{(\operatorname{Nat}.\operatorname{cast}\left(n\right))^{2}}\right)}{\operatorname{Nat}.\operatorname{cast}\left(n\right)}), atTop, \operatorname{nhds}\left(\frac{1}{\operatorname{Real}.\operatorname{log}\left(2\right)}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/LatticePaths/KotesovecA263160.diagonal_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Divide the quantitative logarithmic error by n squared and use log n divided by n tending to zero. Positivity of the finite count allows conversion of the real power to an exponential. Continuity of the exponential yields one divided by log two along every natural index.

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
