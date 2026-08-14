# Convolution-Square Off-Line Orbits

## Abstract

Conjugation and reflection organize off-line convolution-square zero summands into four-point orbits and make every finite off-line cutoff real.

**Theorem 1.1 (Conjugate zero summands are complex conjugates).**

$$\forall Z: \operatorname{ZeroData}, g\in \mathcal{W}, n\in \mathbb{N}, \operatorname{zeroSummand}(Z, \operatorname{convolutionSquare}(g), Z.conjugation(n)) = \overline{\operatorname{zeroSummand}(Z, \operatorname{convolutionSquare}(g), n)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ConvolutionSquareOffLineOrbits.convolution_square_zero_summand_conjugation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Conjugation sends the spectral parameter gamma to minus its complex conjugate and preserves the stored multiplicity. Evenness removes the minus sign, while the convolution square is fixed by the Weil involution. Fourier-Laplace involution covariance then gives the stated complex conjugation identity.

**Theorem 1.2 (An off-line four-point orbit sums to four times one real part).**

$$\forall Z: \operatorname{ZeroData}, g\in \mathcal{W}, n\in \mathbb{N}, Z.conjugation(n) \neq n \land \Re(Z.zero(n)) \neq \operatorname{criticalAbscissa} \Rightarrow \sum_{k\in \{n, Z.reflection(n), Z.conjugation(n), Z.conjugation(Z.reflection(n))\}}\operatorname{zeroSummand}(Z, \operatorname{convolutionSquare}(g), k) = 4 \Re(\operatorname{zeroSummand}(Z, \operatorname{convolutionSquare}(g), n))$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ConvolutionSquareOffLineOrbits.off_line_zero_orbit_sum_eq_four_mul_re` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The frozen zero-orbit cardinality theorem supplies distinctness of the four displayed indices under the explicit nonreal and off-line hypotheses. Reflection leaves each summand unchanged, and conjugation replaces it by its complex conjugate, so the orbit total is twice a number plus twice its conjugate, namely four times its real part. No sign or existence assertion is made.

**Theorem 1.3 (Every finite off-line zero cutoff is real).**

$$\forall Z: \operatorname{ZeroData}, g\in \mathcal{W}, T\in \mathbb{R}, \operatorname{Im}(\operatorname{offlinePart}(Z, g, T)) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ConvolutionSquareOffLineOrbits.off_line_truncated_sum_real` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here offlinePart is the sum over symmetricIndices T filtered by real part unequal to criticalAbscissa, with convolution-square zeroSummand as its term. The filtered finite set is stable under the conjugation permutation. Reindexing by that permutation and applying summand covariance shows the sum equals its complex conjugate, so its imaginary part vanishes. The theorem states reality only, not nonnegativity.

## References

- Truth anchor: `D5/S3/Weil/ZetaBridge/ConvolutionSquareOffLineOrbits.convolution_square_zero_summand_conjugation`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ConvolutionSquareOffLineOrbits.off_line_truncated_sum_real`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ConvolutionSquareOffLineOrbits.off_line_zero_orbit_sum_eq_four_mul_re`
- Dependency: [D5/S3/Weil/ZetaBridge/ConvolutionSquareCriticalLine](ConvolutionSquareCriticalLine.md)
- Dependency: [D5/S3/Zeros/Symmetry/ZeroOrbitCardinality](../../Zeros/Symmetry/ZeroOrbitCardinality.md)
