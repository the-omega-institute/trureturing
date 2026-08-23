# Closed Forms for the Two Beta Readings

## Abstract

The two beta readings are the Zeckendorf displacement minus a linear golden-slope term.

**Theorem 1.1 (The expanding beta reading has a golden-conjugate closed form).**

$$\forall v \in \mathbb{N},\quad \beta(v) = \operatorname{displacementDecode}(v) - v \cdot \psi$$

*Proof.* Machine-checked in Lean as `D5/S1/Deficit/BetaBeattyClosedForms.betaReal_eq_displacement_sub_goldenConj` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural input v, the expanding beta reading is the integer obtained by shifting each occupied Zeckendorf index upward, minus v times the golden conjugate. The digit dependence is therefore concentrated in one integer displacement term, with the remaining dependence on v affine.

For canonical Zeckendorf digits, the first coordinate of the associated golden integer is the shifted Fibonacci sum minus the original Fibonacci sum, hence displacementDecode(v) - v. Its second coordinate is v. Embedding these two coordinates and using phi + psi = 1 gives the stated closed form.

**Theorem 1.2 (The contracting beta reading has a golden-ratio closed form).**

$$\forall v \in \mathbb{N},\quad \beta'(v) = \operatorname{displacementDecode}(v) - v \cdot \varphi$$

*Proof.* Machine-checked in Lean as `D5/S1/Deficit/BetaBeattyClosedForms.betaContraction_eq_displacement_sub_goldenRatio` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural input v, the contracting beta reading has the same integer Zeckendorf displacement as the expanding reading, but subtracts v times the golden ratio rather than v times the golden conjugate.

The two beta faces differ by sqrt(5) times v, while the golden ratio and its conjugate differ by sqrt(5). Subtracting this common face spread from the expanding closed form leaves displacementDecode(v) - v phi, which is the contracting closed form.

## References

- Truth anchor: `D5/S1/Deficit/BetaBeattyClosedForms.betaContraction_eq_displacement_sub_goldenRatio`
- Truth anchor: `D5/S1/Deficit/BetaBeattyClosedForms.betaReal_eq_displacement_sub_goldenConj`
- Dependency: [D5/S1/Deficit/DoubleFaceLength](DoubleFaceLength.md)
- Dependency: [D5/S1/Deficit/ZeckendorfDisplacementReading](ZeckendorfDisplacementReading.md)
