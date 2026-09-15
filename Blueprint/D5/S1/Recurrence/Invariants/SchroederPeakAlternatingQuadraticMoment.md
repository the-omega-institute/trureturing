# Schroeder Paths and the Alternating Quadratic Peak Moment

## Abstract

Schulte's alternating quadratic peak moment for large Schroeder paths.

A word over U, D, and H is measured horizontally by giving U and D weight one and H weight two. The generator is defined by its first return, and T counts generated words with a prescribed number of adjacent U,D pairs.

All indices are natural numbers. List.count counts occurrences of a step, take selects a prefix, and Fin (n+1) supplies the finite index range. Integer powers and products in the final identity are evaluated in Z.

**Definition 1.1 (The three-step alphabet).**

$$\operatorname{Step} = \{U, D, H\}$$

*Formalization.* `D5/S1/Recurrence/Invariants/SchroederPeakAlternatingQuadraticMoment.Step` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Step consists of the up, down, and horizontal letters U, D, and H.

**Definition 1.2 (Finite three-step alphabet).**

$$(\operatorname{Fintype}\left(Step\right))$$

*Formalization.* `D5/S1/Recurrence/Invariants/SchroederPeakAlternatingQuadraticMoment.instFintypeStep` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Werner Schulte (2017). *OEIS A060693, Triangle read by rows: T(n, k) is the number of Schröder paths from (0,0) to (2n,0) having k peaks*. URL: <https://oeis.org/A060693>.

*Commentary.*

The anonymous instance command generates this auto-named declaration. The three-letter Step alphabet is finite.

**Definition 1.3 (Decidable equality on steps).**

$$(\operatorname{DecidableEq}\left(Step\right))$$

*Formalization.* `D5/S1/Recurrence/Invariants/SchroederPeakAlternatingQuadraticMoment.instDecidableEqStep` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Werner Schulte (2017). *OEIS A060693, Triangle read by rows: T(n, k) is the number of Schröder paths from (0,0) to (2n,0) having k peaks*. URL: <https://oeis.org/A060693>.

*Commentary.*

The deriving DecidableEq command generates this auto-named declaration. Equality on the three-letter Step alphabet is decidable.

**Definition 1.4 (Horizontal step weights).**

$$\begin{aligned}\operatorname{stepWeight}\left(U\right) = 1\\\operatorname{stepWeight}\left(D\right) = 1\\\operatorname{stepWeight}\left(H\right) = 2\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Invariants/SchroederPeakAlternatingQuadraticMoment.stepWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The up and down letters have horizontal weight one, while the horizontal letter has weight two.

**Definition 1.5 (Word weight).**

$$\forall w \in \operatorname{List}\left(\operatorname{Step}\left(\right)\right), \operatorname{weight}\left(w\right) = \operatorname{sum}\left(\operatorname{map}\left(\operatorname{stepWeight}, w\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Invariants/SchroederPeakAlternatingQuadraticMoment.weight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The weight of a word is the sum of the horizontal weights of its letters.

**Definition 1.6 (Prefix nonnegativity).**

$$\forall w \in \operatorname{List}\left(\operatorname{Step}\left(\right)\right), \operatorname{PrefixNonnegative}\left(w\right) \iff \forall i \in \mathbb{N}, \operatorname{count}\left(D, \operatorname{take}\left(i, w\right)\right) \le \operatorname{count}\left(U, \operatorname{take}\left(i, w\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Invariants/SchroederPeakAlternatingQuadraticMoment.PrefixNonnegative` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every prefix has no more down letters than up letters.

**Definition 1.7 (The first-return Schroeder generator).**

$$\begin{aligned}\operatorname{schroeder}\left(0\right) = \{()\}\\\operatorname{schroeder}\left(n + 1\right) = \operatorname{union}\left(\operatorname{image}\left(H + ., \operatorname{schroeder}\left(n\right)\right), \operatorname{biUnion}\left(i \in \operatorname{Fin}\left(n + 1\right), \operatorname{image}\left((q, p) \mapsto U + q + D + p, \operatorname{product}\left(\operatorname{schroeder}\left(i\right), \operatorname{schroeder}\left(n - i\right)\right)\right)\right)\right)\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Invariants/SchroederPeakAlternatingQuadraticMoment.schroeder` (`✓ std3`).

*Citation.* Werner Schulte (2017). *OEIS A060693, Triangle read by rows: T(n, k) is the number of Schröder paths from (0,0) to (2n,0) having k peaks*. URL: <https://oeis.org/A060693>.

*Commentary.*

The empty word is the zero object. A positive generator word either begins with H and a word of the preceding size, or begins with U, follows a generated inside word, returns with D, and continues with a generated outside word.

**Definition 1.8 (Adjacent up-down peaks).**

$$\begin{aligned}\operatorname{peaks}\left([]\right) = 0\\\operatorname{peaks}\left([a]\right) = 0\\\operatorname{peaks}\left(a + b + r\right) = \operatorname{if}\left(a = U \land b = D, 1, 0\right) + \operatorname{peaks}\left(b + r\right)\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Invariants/SchroederPeakAlternatingQuadraticMoment.peaks` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

peaks counts adjacent occurrences of U followed immediately by D.

**Definition 1.9 (The peak-counted triangle).**

$$\forall n \in \mathbb{N}, \forall k \in \mathbb{N}, \operatorname{T}\left(n, k\right) = \operatorname{card}\left(\operatorname{filter}\left(w \mapsto \operatorname{peaks}\left(w\right) = k, \operatorname{schroeder}\left(n\right)\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Invariants/SchroederPeakAlternatingQuadraticMoment.T` (`✓ std3`).

*Citation.* Werner Schulte (2017). *OEIS A060693, Triangle read by rows: T(n, k) is the number of Schröder paths from (0,0) to (2n,0) having k peaks*. URL: <https://oeis.org/A060693>.

*Commentary.*

T(n,k) is the cardinality of the generated words of semilength n having k peaks.

**Definition 1.10 (A generated Schroeder path).**

$$\forall n \in \mathbb{N}, \operatorname{SchroederPath}\left(n\right) = \operatorname{Subtype}\left(\operatorname{List}\left(\operatorname{Step}\left(\right)\right), w \mapsto w \in \operatorname{schroeder}\left(n\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Invariants/SchroederPeakAlternatingQuadraticMoment.SchroederPath` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A SchroederPath is a word together with a proof that it belongs to the generator at its semilength.

**Definition 1.11 (First-return decomposition).**

$$\forall n \in \mathbb{N}, \operatorname{firstReturnEquiv}\left(n\right) : \operatorname{Equiv}\left(\operatorname{SchroederPath}\left(n + 1\right), \operatorname{Sum}\left(\operatorname{SchroederPath}\left(n\right), \operatorname{Sigma}\left(i \in \operatorname{Fin}\left(n + 1\right), \operatorname{Product}\left(\operatorname{SchroederPath}\left(i\right), \operatorname{SchroederPath}\left(n - i\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Invariants/SchroederPeakAlternatingQuadraticMoment.firstReturnEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The equivalence separates a positive path into its initial H case or its U, inside, D, outside first-return case.

**Theorem 1.12 (Peak preservation under first return).**

$$\forall i \in \mathbb{N}, \forall n \in \mathbb{N}, \forall q \in \operatorname{List}\left(\operatorname{Step}\left(\right)\right), \forall p \in \operatorname{List}\left(\operatorname{Step}\left(\right)\right), q \in \operatorname{schroeder}\left(i\right) \Rightarrow p \in \operatorname{schroeder}\left(n\right) \Rightarrow \operatorname{peaks}\left(U + q + D + p\right) = \operatorname{peaks}\left(q\right) + \operatorname{peaks}\left(p\right) + \operatorname{if}\left(i = 0, 1, 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/SchroederPeakAlternatingQuadraticMoment.first_return_peaks` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The peak count of a first-return word is the sum of the inner and outer peak counts, with one additional peak exactly when the inner word is empty.

**Theorem 1.13 (The generator characterization).**

$$\forall n \in \mathbb{N}, \forall w \in \operatorname{List}\left(\operatorname{Step}\left(\right)\right), \operatorname{mem}\left(w, \operatorname{schroeder}\left(n\right)\right) \iff (\operatorname{weight}\left(w\right) = 2 \cdot n \land \operatorname{count}\left(U, w\right) = \operatorname{count}\left(D, w\right) \land \operatorname{PrefixNonnegative}\left(w\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/SchroederPeakAlternatingQuadraticMoment.mem_schroeder_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This identity connects the recursive generator with the path description: a word is generated exactly when its weight is 2n, its U and D counts agree, and every prefix is nonnegative.

**Theorem 1.14 (The peak recurrence).**

$$\forall n \in \mathbb{N}, \forall k \in \mathbb{N}, \operatorname{T}\left(n + 1, k\right) = \operatorname{T}\left(n, k\right) + \operatorname{if}\left(0 < k, \operatorname{T}\left(n, k - 1\right), 0\right) + \sum_{i \in \operatorname{Fin}\left(n\right)} \sum_{j \in \operatorname{Fin}\left(k + 1\right)} \operatorname{T}\left(i + 1, j\right) \cdot \operatorname{T}\left(n - \left(i + 1\right), k - j\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/SchroederPeakAlternatingQuadraticMoment.T_first_return_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first-return equivalence and finite-fiber counting split T(n+1,k) into the initial H contribution, the empty-inside peak contribution, and the double convolution over nonempty inside indices.

**Theorem 1.15 (Schulte's alternating quadratic moment).**

$$\forall n \in \mathbb{N}, \sum_{k \in \operatorname{Fin}\left(n + 1\right)} (-1)^{k} \cdot \operatorname{T}\left(n, k\right) \cdot (n + 1 - k)^{2} = (n)^{2} + n + 1$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/SchroederPeakAlternatingQuadraticMoment.schulte_a060693` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a060693-schroeder-peak-alternating-quadratic-moment` (proved) by `D5/S1/Recurrence/Invariants/SchroederPeakAlternatingQuadraticMoment.schulte_a060693`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a060693-schroeder-peak-alternating-quadratic-moment","declaration_gid":"D5/S1/Recurrence/Invariants/SchroederPeakAlternatingQuadraticMoment.schulte_a060693","resolution_kind":"proved"} -->

*Citation.* Werner Schulte (2017). *OEIS A060693, Triangle read by rows: T(n, k) is the number of Schröder paths from (0,0) to (2n,0) having k peaks*. URL: <https://oeis.org/A060693>.

*Commentary.*

The zeroth, first, and second falling signed peak moments satisfy the recurrences induced by first return. Their closed forms reduce the alternating quadratic moment to n squared plus n plus one.

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/SchroederPeakAlternatingQuadraticMoment.PrefixNonnegative`
- Truth anchor: `D5/S1/Recurrence/Invariants/SchroederPeakAlternatingQuadraticMoment.SchroederPath`
- Truth anchor: `D5/S1/Recurrence/Invariants/SchroederPeakAlternatingQuadraticMoment.Step`
- Truth anchor: `D5/S1/Recurrence/Invariants/SchroederPeakAlternatingQuadraticMoment.T`
- Truth anchor: `D5/S1/Recurrence/Invariants/SchroederPeakAlternatingQuadraticMoment.T_first_return_recurrence`
- Truth anchor: `D5/S1/Recurrence/Invariants/SchroederPeakAlternatingQuadraticMoment.firstReturnEquiv`
- Truth anchor: `D5/S1/Recurrence/Invariants/SchroederPeakAlternatingQuadraticMoment.first_return_peaks`
- Truth anchor: `D5/S1/Recurrence/Invariants/SchroederPeakAlternatingQuadraticMoment.instDecidableEqStep`
- Truth anchor: `D5/S1/Recurrence/Invariants/SchroederPeakAlternatingQuadraticMoment.instFintypeStep`
- Truth anchor: `D5/S1/Recurrence/Invariants/SchroederPeakAlternatingQuadraticMoment.mem_schroeder_iff`
- Truth anchor: `D5/S1/Recurrence/Invariants/SchroederPeakAlternatingQuadraticMoment.peaks`
- Truth anchor: `D5/S1/Recurrence/Invariants/SchroederPeakAlternatingQuadraticMoment.schroeder`
- Truth anchor: `D5/S1/Recurrence/Invariants/SchroederPeakAlternatingQuadraticMoment.schulte_a060693`
- Truth anchor: `D5/S1/Recurrence/Invariants/SchroederPeakAlternatingQuadraticMoment.stepWeight`
- Truth anchor: `D5/S1/Recurrence/Invariants/SchroederPeakAlternatingQuadraticMoment.weight`
