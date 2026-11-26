# Pinned real algebraic source: TauCeti.Algebra.QuadraticAlgebra.Square.

## Abstract

Pinned real algebraic source: TauCeti.Algebra.QuadraticAlgebra.Square.

This content adaptation retains selected declarations and proof bodies from TauCetiProject/TauCeti revision 1f9b4414105d86e487a4ac4c3d3397076a44d0d2, TauCeti/Algebra/QuadraticAlgebra/Square.lean. The D5 import paths connect its actual proof dependencies to the original cone boundary consumer. It does not assume a cylindrical decomposition or semialgebraic projection certificate. The original source ownership is retained and no independent escape credit is claimed. Full license and attribution appear in the Lean source and docs/reports/licenses/TauCeti-LICENSE.txt. Each adaptation is retired when the actual pinned mathlib supplies an equivalent statement, replacing consumers by direct applications of that owner.

Under the original ordered-field assumptions that every nonnegative element is a square, a quadratic-algebra element is a square by choosing the square root of its norm and then the real and imaginary components. The component equations reduce to the norm identity and completed squares. The zero imaginary component is split explicitly, so no division by that component is assumed. The actual real-closure construction retains its square-root data and extension-field laws.

## References

- Dependency: [D5/S3/Geometry/AlgebraicBoundary/TauCeti/Algebra/Order/Ring/Square](../Order/Ring/Square.md)
