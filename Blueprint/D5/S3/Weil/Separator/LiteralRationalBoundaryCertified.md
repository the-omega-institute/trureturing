# Certified Literal Rational Pole Boundary

## Abstract

A terminating rational search returns a certified pole-boundary enclosure for one literal same-H witness, with the exact full-line bridge retained.

**Definition 1.1 (A retained first-stop boundary certificate).**

Lean statement: `D5/S3/Weil/Separator/LiteralRationalBoundaryCertified.boundaryCertified`

*Formalization.* `D5/S3/Weil/Separator/LiteralRationalBoundaryCertified.boundaryCertified` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For positive natural radius R, rational polynomials p and q, and precision m, the definition computes the least scalar depth s and least mesh cap kCap meeting their dyadic error budgets. A bounded ordered search retains its actual firstStop payload (k,gr), proves k<=kCap, and records that every earlier scalar or cap candidate fails the corresponding minimality predicate.

The returned grid is exactly the grid built at k. Its checker and stop predicates are true; its completed-square interval is ordered, nonnegative, no wider than (1/2)^m, and retains the exact lower and upper formulas obtained from zero-crossing-aware squaring of the real and imaginary enclosures.

The certificate constructs a WeilTestFunction pointwise equal to the literal H(x)=smoothTransition(2-|x|/R)*rationalEvenPolynomial(p,q,x), supported in [-2R,2R]. It proves full-line integrability and the exact equality between the full-line exponential integral and its reflected half-line same-H integral, then transports the component and twice-norm-square enclosures across that equality.

Two anonymous compile-time consumers exercise the public payload without introducing declarations: one converts the norm-square interval into a poleTerm enclosure for convolutionSquare f; the other combines the same interval with the full-energy identity, under supplied ZeroData convergence and Archimedean convergence, to bound the real zero sum after adding the remaining energy terms. Both recover f from boundaryCertified and keep it pointwise equal to the same literal H.

This unit certifies only the computable rational pole-boundary part. It does not certify the compact contribution or prime and Archimedean intervals, assert that an off-line zero exists, extract a negative witness, or prove the Riemann hypothesis.

## References

- Truth anchor: `D5/S3/Weil/Separator/LiteralRationalBoundaryCertified.boundaryCertified`
- Dependency: [D5/S3/Weil/Separator/LiteralRationalBoundaryFixedGrid](LiteralRationalBoundaryFixedGrid.md)
- Dependency: [D5/S3/Weil/Separator/LiteralRationalBoundaryFixedGridRate](LiteralRationalBoundaryFixedGridRate.md)
- Dependency: [D5/S3/Weil/Separator/LiteralRationalBoundaryGrid](LiteralRationalBoundaryGrid.md)
- Dependency: [D5/S3/Weil/TestFunctions/RationalCutoffApproximation](../TestFunctions/RationalCutoffApproximation.md)
- Dependency: [D5/S3/Weil/ZetaBridge/PrimeArchimedeanEnergyIdentity](../ZetaBridge/PrimeArchimedeanEnergyIdentity.md)
