# Pinned real algebraic source: TauCeti.Algebra.Polynomial.Thom.

## Abstract

Pinned real algebraic source: TauCeti.Algebra.Polynomial.Thom.

This content adaptation retains selected declarations and proof bodies from TauCetiProject/TauCeti revision 1f9b4414105d86e487a4ac4c3d3397076a44d0d2, TauCeti/Algebra/Polynomial/Thom.lean. The D5 import paths connect its actual proof dependencies to the original cone boundary consumer. It does not assume a cylindrical decomposition or semialgebraic projection certificate. The original source ownership is retained and no independent escape credit is claimed. Full license and attribution appear in the Lean source and docs/reports/licenses/TauCeti-LICENSE.txt. Each adaptation is retired when the actual pinned mathlib supplies an equivalent statement, replacing consumers by direct applications of that owner.

Under Semiring R and LinearOrder R, derivativeSign p x k is sign((derivative^[k] p).eval x), including order zero. The finite Thom encoding on Fin p.natDegree records derivative indices i.val+1. Zero and successor index equations are the pinned Function.iterate equations; they introduce no assumption on nonzero derivatives. Under the original ordered-field and PolynomialRolle hypotheses, the interval-sign proof recursively applies Rolle and derivative monotonicity. It establishes order-connected sign fibers and injective ordered root encodings; zero, constant and repeated-root degeneracies are retained in the original definitions and degree branches.

## References

- Dependency: [D5/S3/Geometry/AlgebraicBoundary/TauCeti/Algebra/Polynomial/Rolle](Rolle.md)
