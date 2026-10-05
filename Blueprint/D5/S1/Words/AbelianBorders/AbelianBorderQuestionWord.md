# A Ternary Word with Square Markers

## Abstract

Balanced blocks at square indices define an infinite ternary word.

**Definition 1.1 (The balanced excursion A).**

$$A = [1, 1, 0, 0, 2, 2, 2, 2, 2, 0, 0, 0, 1, 1, 1]$$

*Formalization.* `D5/S1/Words/AbelianBorders/AbelianBorderQuestionWord.A` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Émilie Charlier, Tero Harju, Svetlana Puzynina, Luca Q. Zamboni (2015). *Abelian bordered factors and periodicity*. DOI: [10.48550/arXiv.1501.07464](https://doi.org/10.48550/arXiv.1501.07464). URL: <https://arxiv.org/abs/1501.07464v1>.

*Commentary.*

The block A is 110022222000111. Its length is fifteen, and each of the three letters occurs five times.

**Definition 1.2 (The balanced block B).**

$$B = [0, 1, 2]$$

*Formalization.* `D5/S1/Words/AbelianBorders/AbelianBorderQuestionWord.B` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Émilie Charlier, Tero Harju, Svetlana Puzynina, Luca Q. Zamboni (2015). *Abelian bordered factors and periodicity*. DOI: [10.48550/arXiv.1501.07464](https://doi.org/10.48550/arXiv.1501.07464). URL: <https://arxiv.org/abs/1501.07464v1>.

*Commentary.*

The block B is 012. Each of the three letters occurs once.

**Definition 1.3 (Blocks selected by square indices).**

$$\forall j \in Nat,\; block\left(j\right) = ite\left(IsSquare\left(j\right), B, A\right)$$

*Formalization.* `D5/S1/Words/AbelianBorders/AbelianBorderQuestionWord.block` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Émilie Charlier, Tero Harju, Svetlana Puzynina, Luca Q. Zamboni (2015). *Abelian bordered factors and periodicity*. DOI: [10.48550/arXiv.1501.07464](https://doi.org/10.48550/arXiv.1501.07464). URL: <https://arxiv.org/abs/1501.07464v1>.

*Commentary.*

At every square index j the block is B; at all other indices it is A. Zero is a square index.

**Definition 1.4 (Finite initial concatenations).**

$$initial\left(0\right) = [] \land \left(\forall j \in Nat,\; initial\left(j + 1\right) = append\left(initial\left(j\right), block\left(j\right)\right)\right)$$

*Formalization.* `D5/S1/Words/AbelianBorders/AbelianBorderQuestionWord.initial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Émilie Charlier, Tero Harju, Svetlana Puzynina, Luca Q. Zamboni (2015). *Abelian bordered factors and periodicity*. DOI: [10.48550/arXiv.1501.07464](https://doi.org/10.48550/arXiv.1501.07464). URL: <https://arxiv.org/abs/1501.07464v1>.

*Commentary.*

The initial concatenation of zero blocks is empty. Each succeeding concatenation appends the block at the next index.

**Definition 1.5 (The infinite ternary word).**

$$\forall n \in Nat,\; word\left(n\right) = getD\left(initial\left(n + 1\right), n, 0\right)$$

*Formalization.* `D5/S1/Words/AbelianBorders/AbelianBorderQuestionWord.word` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Émilie Charlier, Tero Harju, Svetlana Puzynina, Luca Q. Zamboni (2015). *Abelian bordered factors and periodicity*. DOI: [10.48550/arXiv.1501.07464](https://doi.org/10.48550/arXiv.1501.07464). URL: <https://arxiv.org/abs/1501.07464v1>.

*Commentary.*

The letter at position n is read from initial(n+1), with zero as the default value. Each block has at least three letters, so position n lies within this concatenation. The resulting word is the concatenation of all the blocks.

**Theorem 1.6 (Prefixes and bounded weak abelian periodicity).**

$$\left(\forall j \in Nat,\; \forall r \in Nat,\; r \le length\left(block\left(j\right)\right) \Rightarrow factor\left(word, 0, length\left(initial\left(j\right)\right) + r\right) = append\left(initial\left(j\right), take\left(r, block\left(j\right)\right)\right)\right) \land \left(\left(\forall j \in Nat,\; \forall a \in Fin\left(3\right),\; count\left(initial\left(j\right), a\right) = count\left(initial\left(j\right), 0\right)\right) \land BoundedWeakAbelianPeriodic\left(word\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AbelianBorders/AbelianBorderQuestionWord.word_structure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Émilie Charlier, Tero Harju, Svetlana Puzynina, Luca Q. Zamboni (2015). *Abelian bordered factors and periodicity*. DOI: [10.48550/arXiv.1501.07464](https://doi.org/10.48550/arXiv.1501.07464). URL: <https://arxiv.org/abs/1501.07464v1>.

*Commentary.*

Prefixes agree with the finite block concatenations, and every initial concatenation has equal counts of all three letters. Cuts at the block boundaries give a strictly increasing decomposition with block lengths at most fifteen and common frequencies (1/3,1/3,1/3).

## References

- Truth anchor: `D5/S1/Words/AbelianBorders/AbelianBorderQuestionWord.A`
- Truth anchor: `D5/S1/Words/AbelianBorders/AbelianBorderQuestionWord.B`
- Truth anchor: `D5/S1/Words/AbelianBorders/AbelianBorderQuestionWord.block`
- Truth anchor: `D5/S1/Words/AbelianBorders/AbelianBorderQuestionWord.initial`
- Truth anchor: `D5/S1/Words/AbelianBorders/AbelianBorderQuestionWord.word`
- Truth anchor: `D5/S1/Words/AbelianBorders/AbelianBorderQuestionWord.word_structure`
- Dependency: [D5/S1/Words/AbelianBorders/AbelianBorderQuestionDefs](AbelianBorderQuestionDefs.md)
