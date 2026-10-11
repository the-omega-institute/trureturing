# MatrixBounds

## Abstract

Dyadic coefficient recurrences control the sixfold evil and odious representation counts.

**Definition 1.1 (matrixBound).**

$$\forall (d : \mathbb{N}) (A : \operatorname{Matrix} (\operatorname{Fin} d) (\operatorname{Fin} d) \mathbb{Z}) (B : \mathbb{N}) , \operatorname{matrixBound} A B \iff \forall (i : \operatorname{Fin} d) , \sum_{j : \operatorname{Fin} d} (A i j) . \operatorname{natAbs} \le B$$

*Formalization.* `D5/S1/Words/EvilOdious/MatrixBounds.matrixBound` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Definition 1.2 (vectorBound).**

$$\forall (d : \mathbb{N}) (v : \operatorname{Fin} d \to \mathbb{Z}) (B : \mathbb{N}) , \operatorname{vectorBound} v B \iff \forall (i : \operatorname{Fin} d) , (v i) . \operatorname{natAbs} \le B$$

*Formalization.* `D5/S1/Words/EvilOdious/MatrixBounds.vectorBound` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Theorem 1.3 (matrix apply bound).**

$$\forall (d : \mathbb{N}) , \forall (A : \operatorname{Matrix} (\operatorname{Fin} d) (\operatorname{Fin} d) \mathbb{Z}) , \forall (v : \operatorname{Fin} d \to \mathbb{Z}) , \forall (B K : \mathbb{N}) , (\operatorname{matrixBound} A B) \to (\operatorname{vectorBound} v K) \to \operatorname{vectorBound} (A.\operatorname{mulVec} v) (B \cdot K)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/EvilOdious/MatrixBounds.matrix_apply_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Theorem 1.4 (matrix mul bound).**

$$\forall (d : \mathbb{N}) , \forall (A B : \operatorname{Matrix} (\operatorname{Fin} d) (\operatorname{Fin} d) \mathbb{Z}) , \forall (a b : \mathbb{N}) , (\operatorname{matrixBound} A a) \to (\operatorname{matrixBound} B b) \to \operatorname{matrixBound} (A \cdot B) (a \cdot b)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/EvilOdious/MatrixBounds.matrix_mul_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Definition 1.5 (pz).**

$$\forall (p : \operatorname{List} \mathbb{Z}) , \forall (k : \mathbb{Z}) , \operatorname{pz} p k = \operatorname{if} 0 \le k \operatorname{then} (\operatorname{List}.\operatorname{getD} p k.\operatorname{toNat} 0) \operatorname{else} 0$$

*Formalization.* `D5/S1/Words/EvilOdious/MatrixBounds.pz` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Definition 1.6 (stateMatrix).**

$$\forall (d : \mathbb{N}) (p : \operatorname{List} \mathbb{Z}) (b : \operatorname{Bool}) , \operatorname{stateMatrix} d p b = \operatorname{fun} (i a : \operatorname{Fin} d) \mapsto \operatorname{pz} p (2 \cdot (a : \mathbb{Z}) + (\operatorname{if} b \operatorname{then} 1 \operatorname{else} 0) - (i : \mathbb{Z}))$$

*Formalization.* `D5/S1/Words/EvilOdious/MatrixBounds.stateMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Definition 1.7 (words).**

$$\forall (n : \mathbb{N}) , \operatorname{words} n = (\operatorname{List}.\operatorname{replicate} n [\operatorname{false} , \operatorname{true}]) . \operatorname{sections}$$

*Formalization.* `D5/S1/Words/EvilOdious/MatrixBounds.words` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Definition 1.8 (wordMatrix).**

$$\forall (d : \mathbb{N}) (M : \operatorname{Bool} \to \operatorname{Matrix} (\operatorname{Fin} d) (\operatorname{Fin} d) \mathbb{Z}) (w : \operatorname{List} \operatorname{Bool}) , \operatorname{wordMatrix} M w = (w.\operatorname{map} M) . \operatorname{prod}$$

*Formalization.* `D5/S1/Words/EvilOdious/MatrixBounds.wordMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Theorem 1.9 (h matrix bound).**

$$\operatorname{matrixBound} (\operatorname{stateMatrix} 5 (p 1) \operatorname{false}) 6 \land \operatorname{matrixBound} (\operatorname{stateMatrix} 5 (p 1) \operatorname{true}) 6 \land \operatorname{matrixBound} (\operatorname{stateMatrix} 5 (p 2) \operatorname{false}) 4 \land \operatorname{matrixBound} (\operatorname{stateMatrix} 5 (p 2) \operatorname{true}) 4 \land \operatorname{matrixBound} (\operatorname{stateMatrix} 5 (p 3) \operatorname{false}) 4 \land \operatorname{matrixBound} (\operatorname{stateMatrix} 5 (p 3) \operatorname{true}) 4 \land \operatorname{matrixBound} (\operatorname{stateMatrix} 5 (p 4) \operatorname{false}) 6 \land \operatorname{matrixBound} (\operatorname{stateMatrix} 5 (p 4) \operatorname{true}) 6 \land \operatorname{matrixBound} (\operatorname{stateMatrix} 5 (p 5) \operatorname{false}) 16 \land \operatorname{matrixBound} (\operatorname{stateMatrix} 5 (p 5) \operatorname{true}) 16$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/EvilOdious/MatrixBounds.h_matrix_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Definition 1.10 (wordsCheck).**

$$\forall (\operatorname{len} \operatorname{bound} : \mathbb{N}) , \operatorname{wordsCheck} \operatorname{len} \operatorname{bound} = (\operatorname{words} \operatorname{len}) . \operatorname{all} (\operatorname{fun} w \mapsto \operatorname{decide} (\operatorname{matrixBound} (\operatorname{wordMatrix} (\operatorname{stateMatrix} 6 (p 6)) w) \operatorname{bound}))$$

*Formalization.* `D5/S1/Words/EvilOdious/MatrixBounds.wordsCheck` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Theorem 1.11 (c five checked).**

$$\operatorname{wordsCheck} 5 1019200 = \operatorname{true}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/EvilOdious/MatrixBounds.c_five_checked` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

**Theorem 1.12 (c word bound).**

$$\forall (w : \operatorname{List} \operatorname{Bool}) , \operatorname{matrixBound} (\operatorname{wordMatrix} (\operatorname{stateMatrix} 6 (p 6)) w) (2 \cdot 16 ^{w.\operatorname{length}})$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/EvilOdious/MatrixBounds.c_word_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche and Jeffrey Shallit (2021). *Additive properties of the evil and odious numbers and similar sequences*. DOI: [10.7169/facm/2108](https://doi.org/10.7169/facm/2108). URL: <https://arxiv.org/abs/2112.13627v3>.

*Commentary.*

The formula uses the indicated natural or integer carriers. Natural subtraction is truncated; a slash between natural numbers denotes floor division, Nat.div. Dotted operations and the displayed casts retain their Lean meanings.

## References

- Truth anchor: `D5/S1/Words/EvilOdious/MatrixBounds.c_five_checked`
- Truth anchor: `D5/S1/Words/EvilOdious/MatrixBounds.c_word_bound`
- Truth anchor: `D5/S1/Words/EvilOdious/MatrixBounds.h_matrix_bound`
- Truth anchor: `D5/S1/Words/EvilOdious/MatrixBounds.matrixBound`
- Truth anchor: `D5/S1/Words/EvilOdious/MatrixBounds.matrix_apply_bound`
- Truth anchor: `D5/S1/Words/EvilOdious/MatrixBounds.matrix_mul_bound`
- Truth anchor: `D5/S1/Words/EvilOdious/MatrixBounds.pz`
- Truth anchor: `D5/S1/Words/EvilOdious/MatrixBounds.stateMatrix`
- Truth anchor: `D5/S1/Words/EvilOdious/MatrixBounds.vectorBound`
- Truth anchor: `D5/S1/Words/EvilOdious/MatrixBounds.wordMatrix`
- Truth anchor: `D5/S1/Words/EvilOdious/MatrixBounds.words`
- Truth anchor: `D5/S1/Words/EvilOdious/MatrixBounds.wordsCheck`
- Dependency: [D5/S1/Words/EvilOdious/SequenceCoefficients](SequenceCoefficients.md)
