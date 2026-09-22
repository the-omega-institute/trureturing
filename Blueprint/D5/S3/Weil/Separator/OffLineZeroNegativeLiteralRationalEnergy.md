# Negative Full Energy in the Literal Rational Family

## Abstract

A stored off-line zero produces an exact literal rational smooth-transition test with a negative complete paired zero sum and the same negative full energy.

**Theorem 1.1 (An off-line zero yields a literal negative-energy test).**

$$\forall Z \in ZeroData, n \in \mathbb{N},\; \operatorname{re}\left(\operatorname{zero}\left(Z, n\right)\right) \ne criticalAbscissa \Rightarrow \left(\exists R \in \mathbb{N}, p \in \operatorname{Polynomial}\left(\mathbb{Q}\right), q \in \operatorname{Polynomial}\left(\mathbb{Q}\right), h \in WeilTestFunction,\; 0 < R \land \left(\left(\forall x \in \mathbb{R},\; \operatorname{h}\left(x\right) = \operatorname{ofReal}\left(\operatorname{smoothTransition}\left(2 - \frac{\left|x\right|}{R}\right)\right) \cdot \operatorname{rationalEvenPolynomial}\left(p, q, x\right)\right) \land \left(\operatorname{tsupport}\left(h\right) \subseteq \operatorname{Icc}\left(-\left(2 \cdot R\right), 2 \cdot R\right) \land \left(\operatorname{re}\left(\operatorname{zeroSum}\left(Z, \operatorname{convolutionSquare}\left(h\right), \operatorname{symmetricConvergentOfZeroData}\left(Z, \operatorname{convolutionSquare}\left(h\right)\right)\right)\right) < 0 \land \left(\operatorname{zeroSum}\left(Z, \operatorname{convolutionSquare}\left(h\right), \operatorname{symmetricConvergentOfZeroData}\left(Z, \operatorname{convolutionSquare}\left(h\right)\right)\right) = \operatorname{ofReal}\left(2 \cdot \operatorname{normSq}\left(\int_{\mathbb{R}} \operatorname{exp}\left(\frac{\operatorname{ofReal}\left(x\right)}{2}\right) \cdot h\left(x\right) dx\right) + \operatorname{archimedeanJumpEnergy}\left(h\right) + \operatorname{arithmeticJumpEnergy}\left(2 \cdot R, h\right) - \left(2 \cdot \operatorname{totalPrimeWeight}\left(2 \cdot R\right) - archimedeanConstant\right) \cdot \operatorname{l2Mass}\left(h\right)\right) \land 2 \cdot \operatorname{normSq}\left(\int_{\mathbb{R}} \operatorname{exp}\left(\frac{\operatorname{ofReal}\left(x\right)}{2}\right) \cdot h\left(x\right) dx\right) + \operatorname{archimedeanJumpEnergy}\left(h\right) + \operatorname{arithmeticJumpEnergy}\left(2 \cdot R, h\right) - \left(2 \cdot \operatorname{totalPrimeWeight}\left(2 \cdot R\right) - archimedeanConstant\right) \cdot \operatorname{l2Mass}\left(h\right) < 0\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Separator/OffLineZeroNegativeLiteralRationalEnergy.offLineZero_yields_negative_literal_rational_energy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

ZeroData stores distinct nontrivial zeros with their analytic multiplicities. The hypothesis refers to one actual stored index, whose real part differs from criticalAbscissa. Neither an off-line zero nor ZeroData is asserted to exist.

The natural radius R is strictly positive. The rational polynomials p and q are evaluated by rationalEvenPolynomial, the even complex polynomial pair. The displayed pointwise equality is the function equality in the Lean statement. The support enclosure is [-2R,2R], not an assertion of support equality.

The literal cutoff is smoothTransition(2-|x|/R). Its smoothness uses the explicit inner-product bump base at parameter 2 and argument x/R. Rational approximation of three physical jets on the entire support interval controls the cutoff product error. A full summable fourth moment then bounds the paired transform difference at gamma and conjugate gamma, retaining multiplicities and the strict margin of the original negative test.

The zero-side convergence proof is symmetricConvergent_of_zeroData for convolutionSquare(h). The energy identity also uses archimedeanConvergent_of_weilTestFunction for the same square. The support scale passed to the identity is L=2R, so its arithmetic cutoff is exp(4R). All integrals use Lebesgue measure on the real line.

This is erased analytic existence. It supplies no degree or denominator bound, numerical certificate, executable search, or proof of the Riemann hypothesis.

## References

- Truth anchor: `D5/S3/Weil/Separator/OffLineZeroNegativeLiteralRationalEnergy.offLineZero_yields_negative_literal_rational_energy`
- Dependency: [D5/S3/Weil/Separator/OffLineZeroNegativeWeilSquare](OffLineZeroNegativeWeilSquare.md)
- Dependency: [D5/S3/Weil/Separator/UnconditionalExplicitFormula](UnconditionalExplicitFormula.md)
- Dependency: [D5/S3/Weil/TestFunctions/RationalCutoffApproximation](../TestFunctions/RationalCutoffApproximation.md)
