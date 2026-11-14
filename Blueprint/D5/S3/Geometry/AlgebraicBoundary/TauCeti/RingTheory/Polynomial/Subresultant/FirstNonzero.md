# Pinned real algebraic source: TauCeti.RingTheory.Polynomial.Subresultant.FirstNonzero.

## Abstract

Pinned real algebraic source: TauCeti.RingTheory.Polynomial.Subresultant.FirstNonzero.

This content adaptation retains selected declarations and proof bodies from TauCetiProject/TauCeti revision 1f9b4414105d86e487a4ac4c3d3397076a44d0d2, TauCeti/RingTheory/Polynomial/Subresultant/FirstNonzero.lean. The D5 import paths connect its actual proof dependencies to the original cone boundary consumer. It does not assume a cylindrical decomposition or semialgebraic projection certificate. The original source ownership is retained and no independent escape credit is claimed. Full license and attribution appear in the Lean source and docs/reports/licenses/TauCeti-LICENSE.txt. Each adaptation is retired when the actual pinned mathlib supplies an equivalent statement, replacing consumers by direct applications of that owner.

For the original field and degree bounds, the adjugate coefficient-window construction gives A*q+B*p equal to the subresultant. Each coefficient equation is Matrix.mul_adjugate followed by polynomial coefficient extensionality, and degree bounds close the coefficients outside the window. A low-degree gcd-divisible relation forces A=B=0 by pinned coprimality of the gcd quotients, dvd_of_dvd_mul_right, mul_left_cancel₀ and eq_zero_of_dvd_of_degree_lt. Thus the gcd-index principal coefficient is nonzero. Degree versus divisibility gives vanishing below any common-divisor degree; normalize-associated laws identify the gcd-index subresultant with the normalized gcd. The actual normalized-gcd continuity, common-root gluing and Collins gcd-degree proofs retain these coefficient-window and nonvanishing inputs.

## References

- Dependency: [D5/S3/Geometry/AlgebraicBoundary/TauCeti/RingTheory/Polynomial/Subresultant/Bezout](Bezout.md)
- Dependency: [D5/S3/Geometry/AlgebraicBoundary/TauCeti/RingTheory/Polynomial/Subresultant/GCD](GCD.md)
