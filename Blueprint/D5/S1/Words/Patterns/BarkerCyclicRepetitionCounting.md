# Cyclic successive repetitions over eight letters

## Abstract

Barker's generating function and radical formula count cyclic repetition words.

Letters lie in Fin 8. Positions in Fin n are zero based. An event is an adjacent equal pair, and overlapping pairs are retained. The source offset is 1,1: its generating series has zero constant coefficient. The count at index zero includes the unique empty word. All occurrences of Nat.mod mean natural-number remainder; real square roots are nonnegative.

**Definition 1.1 (Labels of adjacent equal pairs).**

$$\forall w \in \operatorname{List}\left(\operatorname{Fin}\left(8\right)\right),\; \operatorname{eventLabels}\left(w\right) = \operatorname{List.map}\left(\operatorname{Prod.snd}, \operatorname{List.filter}\left(\lambda (p: \operatorname{Fin}\left(8\right)\times\operatorname{Fin}\left(8\right)) \mapsto \operatorname{Prod.fst}\left(p\right) = \operatorname{Prod.snd}\left(p\right), \operatorname{List.zip}\left(w, \operatorname{List.tail}\left(w\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Words/Patterns/BarkerCyclicRepetitionCounting.eventLabels` (`✓ std3`).

*Citation.* R. H. Hardin; Colin Barker (2019). *OEIS A268943: cyclic successive equality events*. URL: <https://oeis.org/A268943>.

*Commentary.*

OEIS A268943, revision 8, unpaginated NAME (%N): "Number of length-n 0..7 arrays with no repeated value unequal to the previous repeated value plus one mod 7+1." Zipping a list with its tail lists adjacent pairs in order. Filtering equal pairs and taking their second coordinates records exactly the event labels, including both pairs of a triple equal letter.

**Definition 1.2 (Cyclic succession of event labels).**

$$\forall n \in \mathbb{N},\; \forall w \in \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(8\right),\; \operatorname{Admissible}\left(w\right) = \operatorname{List.IsChain}\left(\lambda (a: \operatorname{Fin}\left(8\right)) \mapsto \lambda (b: \operatorname{Fin}\left(8\right)) \mapsto \operatorname{val}\left(b\right) = \operatorname{Nat.mod}\left(\operatorname{val}\left(a\right) + 1, 8\right), \operatorname{eventLabels}\left(\operatorname{List.ofFn}\left(w\right)\right)\right)$$

*Formalization.* `D5/S1/Words/Patterns/BarkerCyclicRepetitionCounting.Admissible` (`✓ std3`).

*Citation.* R. H. Hardin; Colin Barker (2019). *OEIS A268943: cyclic successive equality events*. URL: <https://oeis.org/A268943>.

*Commentary.*

OEIS A268943, revision 8, unpaginated NAME (%N): "Number of length-n 0..7 arrays with no repeated value unequal to the previous repeated value plus one mod 7+1." Source position i corresponds to Lean position i-1. Each two successive event labels differ by one modulo eight. Empty and singleton event lists satisfy List.IsChain. Nonadjacent recurrences are permitted, as in the source example (6,4,6,5,4).

**Definition 1.3 (The literal word count).**

$$\forall n \in \mathbb{N},\; \operatorname{count}\left(n\right) = \operatorname{Nat.card}\left(\{w: \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(8\right) \mid \operatorname{Admissible}\left(w\right)\}\right)$$

*Formalization.* `D5/S1/Words/Patterns/BarkerCyclicRepetitionCounting.count` (`✓ std3`).

*Citation.* R. H. Hardin; Colin Barker (2019). *OEIS A268943: cyclic successive equality events*. URL: <https://oeis.org/A268943>.

*Commentary.*

OEIS A268943, revision 8, unpaginated NAME (%N): "Number of length-n 0..7 arrays with no repeated value unequal to the previous repeated value plus one mod 7+1." Nat.card counts the subtype of functions satisfying Admissible. Words are labeled arrays; no rotation or permutation is identified.

**Definition 1.4 (Coefficients of the source series).**

$$\forall F \in \operatorname{PowerSeries}\left(\mathbb{Q}\right),\; \operatorname{IsSourceSeries}\left(F\right) = ((\operatorname{PowerSeries.coeff}\left(0, F\right) = 0) \land (\forall n \in \mathbb{N},\; 1 \le n \Rightarrow \operatorname{PowerSeries.coeff}\left(n, F\right) = (\operatorname{count}\left(n\right): \mathbb{Q})))$$

*Formalization.* `D5/S1/Words/Patterns/BarkerCyclicRepetitionCounting.IsSourceSeries` (`✓ std3`).

*Citation.* R. H. Hardin; Colin Barker (2019). *OEIS A268943: cyclic successive equality events*. URL: <https://oeis.org/A268943>.

*Commentary.*

OEIS A268943, revision 8, unpaginated FORMULA (%F): "Conjectures from _Colin Barker_, Jan 17 2019: (Start)" "G.f.: 8*x*(1 - 5*x - 7*x^2) / ((1 - 7*x)*(1 - 6*x - 8*x^2))." "a(n) = (-272*7^n + (153-37*sqrt(17))*(3-sqrt(17))^n + (3+sqrt(17))^n*(153+37*sqrt(17))) / 34." "(End)" PowerSeries has rational coefficients. The constant coefficient is zero, and coefficient n is the natural count cast to ℚ for every n ≥ 1.

**Definition 1.5 (Barker's two formulas).**

$$\operatorname{claim} = ((\exists F \in \operatorname{PowerSeries}\left(\mathbb{Q}\right),\; \operatorname{IsSourceSeries}\left(F\right)) \land ((\forall F \in \operatorname{PowerSeries}\left(\mathbb{Q}\right),\; \operatorname{IsSourceSeries}\left(F\right) \Rightarrow F = 8 \cdot \operatorname{PowerSeries.X} \cdot (1 - 5 \cdot \operatorname{PowerSeries.X} - 7 \cdot \operatorname{PowerSeries.X}^{2}) \cdot ((1 - 7 \cdot \operatorname{PowerSeries.X}) \cdot (1 - 6 \cdot \operatorname{PowerSeries.X} - 8 \cdot \operatorname{PowerSeries.X}^{2}))^{-1}) \land (\forall n \in \mathbb{N},\; 1 \le n \Rightarrow (\operatorname{count}\left(n\right): \mathbb{R}) = \frac{-272 \cdot (7: \mathbb{R})^{n} + (153 - 37 \cdot \operatorname{Real.sqrt}\left(17\right)) \cdot (3 - \operatorname{Real.sqrt}\left(17\right))^{n} + (3 + \operatorname{Real.sqrt}\left(17\right))^{n} \cdot (153 + 37 \cdot \operatorname{Real.sqrt}\left(17\right))}{34})))$$

*Formalization.* `D5/S1/Words/Patterns/BarkerCyclicRepetitionCounting.claim` (`✓ std3`).

*Citation.* R. H. Hardin; Colin Barker (2019). *OEIS A268943: cyclic successive equality events*. URL: <https://oeis.org/A268943>.

*Commentary.*

OEIS A268943, revision 8, unpaginated FORMULA (%F): "Conjectures from _Colin Barker_, Jan 17 2019: (Start)" "G.f.: 8*x*(1 - 5*x - 7*x^2) / ((1 - 7*x)*(1 - 6*x - 8*x^2))." "a(n) = (-272*7^n + (153-37*sqrt(17))*(3-sqrt(17))^n + (3+sqrt(17))^n*(153+37*sqrt(17))) / 34." "(End)" The first clause asserts existence of the coefficient series. The second identifies every such series with the rational expression, using the inverse in PowerSeries ℚ. The last clause states the radical identity over ℝ at every positive natural index.

**Theorem 1.6 (The generating function and radical identity).**

$$(\exists F \in \operatorname{PowerSeries}\left(\mathbb{Q}\right),\; \operatorname{IsSourceSeries}\left(F\right)) \land ((\forall F \in \operatorname{PowerSeries}\left(\mathbb{Q}\right),\; \operatorname{IsSourceSeries}\left(F\right) \Rightarrow F = 8 \cdot \operatorname{PowerSeries.X} \cdot (1 - 5 \cdot \operatorname{PowerSeries.X} - 7 \cdot \operatorname{PowerSeries.X}^{2}) \cdot ((1 - 7 \cdot \operatorname{PowerSeries.X}) \cdot (1 - 6 \cdot \operatorname{PowerSeries.X} - 8 \cdot \operatorname{PowerSeries.X}^{2}))^{-1}) \land (\forall n \in \mathbb{N},\; 1 \le n \Rightarrow (\operatorname{count}\left(n\right): \mathbb{R}) = \frac{-272 \cdot (7: \mathbb{R})^{n} + (153 - 37 \cdot \operatorname{Real.sqrt}\left(17\right)) \cdot (3 - \operatorname{Real.sqrt}\left(17\right))^{n} + (3 + \operatorname{Real.sqrt}\left(17\right))^{n} \cdot (153 + 37 \cdot \operatorname{Real.sqrt}\left(17\right))}{34}))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Patterns/BarkerCyclicRepetitionCounting.result` (`✓ std3`). ∎

*Resolves.* `Problems/barker268943` (proved) by `D5/S1/Words/Patterns/BarkerCyclicRepetitionCounting.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"barker268943","declaration_gid":"D5/S1/Words/Patterns/BarkerCyclicRepetitionCounting.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker (2019). *OEIS A268943: cyclic successive equality events*. URL: <https://oeis.org/A268943>.

*Commentary.*

Prepending a letter partitions words into three states: no event; a first event equal to the successor of the first letter; and the remaining words with an event. Their counts start at (8,0,0) and transform as (U,A,B) ↦ (7U,B,U+8A+6B). Coefficientwise identities give the rational series. The total count satisfies the order-three recurrence with coefficients 13,-34,-56. The exponential terms with bases 7, 3-√17, 3+√17 satisfy that recurrence and agree with the counts at indices 1,2,3. Uniqueness of recurrence solutions yields the radical formula.

## References

- Truth anchor: `D5/S1/Words/Patterns/BarkerCyclicRepetitionCounting.Admissible`
- Truth anchor: `D5/S1/Words/Patterns/BarkerCyclicRepetitionCounting.IsSourceSeries`
- Truth anchor: `D5/S1/Words/Patterns/BarkerCyclicRepetitionCounting.claim`
- Truth anchor: `D5/S1/Words/Patterns/BarkerCyclicRepetitionCounting.count`
- Truth anchor: `D5/S1/Words/Patterns/BarkerCyclicRepetitionCounting.eventLabels`
- Truth anchor: `D5/S1/Words/Patterns/BarkerCyclicRepetitionCounting.result`
