# Golden Mechanical Word Window

## Abstract

Identify the exact fractional-coordinate window for a golden mechanical letter.

The lower golden mechanical word is defined by consecutive floor differences at slope one over the golden ratio. The theorem below gives an exact local test using the existing golden fractional coordinate.

<a id="describe-golden-mechanical-letter-window"></a>

**Theorem 1.1 (A letter is one exactly on the local window).**

$$\forall n\in\mathbb{N},\ s_n=1\ \Leftrightarrow\ \{n\varphi\}\in[1-\varphi^{-1},1)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/GoldenMechanicalWord.golden_mechanical_letter_eq_one_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural index, the floor-difference letter equals one if and only if the golden fractional coordinate lies in the stated half-open interval. No complexity, substitution, or cut-and-project classification is asserted.

## References

- Truth anchor: `D5/S1/Words/GoldenMechanicalWord.golden_mechanical_letter_eq_one_iff`
