# An Unbounded Family of Unbordered Factors

## Abstract

Square gaps yield infinitely many nonempty weakly abelian unbordered factors.

**Definition 1.1 (The factor family 12 A to the power m 0).**

$$\forall m \in Nat,\; F\left(m\right) = append\left(append\left([1, 2], flatten\left(replicate\left(m, A\right)\right)\right), [0]\right)$$

*Formalization.* `D5/S1/Words/AbelianBorders/AbelianBorderQuestionFactors.F` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Émilie Charlier, Tero Harju, Svetlana Puzynina, Luca Q. Zamboni (2015). *Abelian bordered factors and periodicity*. DOI: [10.48550/arXiv.1501.07464](https://doi.org/10.48550/arXiv.1501.07464). URL: <https://arxiv.org/abs/1501.07464v1>.

*Commentary.*

The word F(m) is 12 followed by m copies of A and a final 0. Its length is 15m+3, and each letter occurs 5m+1 times.

**Theorem 1.2 (Every word in the family is unbordered).**

$$\forall m \in Nat,\; \neg (WeakAbelianBordered\left(F\left(m\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AbelianBorders/AbelianBorderQuestionFactors.unbordered` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Émilie Charlier, Tero Harju, Svetlana Puzynina, Luca Q. Zamboni (2015). *Abelian bordered factors and periodicity*. DOI: [10.48550/arXiv.1501.07464](https://doi.org/10.48550/arXiv.1501.07464). URL: <https://arxiv.org/abs/1501.07464v1>.

*Commentary.*

Equal prefix and suffix frequencies would force a positive weighted sum of two internal projected cut vectors to be zero. The only possible pair of cut residues forces equal prefix and suffix lengths, but those residues are incompatible with the total length 15m+3. The end cases also exclude a whole-word suffix.

**Theorem 1.3 (Infinitely many unbordered factors).**

$$\neg (Finite\left(\{ u: List\left(Fin\left(3\right)\right) \mid \left(\exists i \in Nat,\; \exists n \in Nat,\; u = factor\left(word, i, n\right)\right) \land \left(u \ne [] \land \left(\neg (WeakAbelianBordered\left(u\right))\right)\right)\} \right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AbelianBorders/AbelianBorderQuestionFactors.infinitely_many_unbordered` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Émilie Charlier, Tero Harju, Svetlana Puzynina, Luca Q. Zamboni (2015). *Abelian bordered factors and periodicity*. DOI: [10.48550/arXiv.1501.07464](https://doi.org/10.48550/arXiv.1501.07464). URL: <https://arxiv.org/abs/1501.07464v1>.

*Commentary.*

Between the square block indices q squared and (q+1) squared there are exactly 2q copies of A. The last two letters of the first B, these copies of A, and the first letter of the next B give F(2q) as a factor. These nonempty unbordered factors have lengths 30q+3, which are unbounded.

## References

- Truth anchor: `D5/S1/Words/AbelianBorders/AbelianBorderQuestionFactors.F`
- Truth anchor: `D5/S1/Words/AbelianBorders/AbelianBorderQuestionFactors.infinitely_many_unbordered`
- Truth anchor: `D5/S1/Words/AbelianBorders/AbelianBorderQuestionFactors.unbordered`
- Dependency: [D5/S1/Words/AbelianBorders/AbelianBorderQuestionWord](AbelianBorderQuestionWord.md)
