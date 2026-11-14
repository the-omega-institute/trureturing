# Pinned real algebraic source: TauCeti.Algebra.Polynomial.QuadraticDiscriminant.

## Abstract

Pinned real algebraic source: TauCeti.Algebra.Polynomial.QuadraticDiscriminant.

This content adaptation retains selected declarations and proof bodies from TauCetiProject/TauCeti revision 1f9b4414105d86e487a4ac4c3d3397076a44d0d2, TauCeti/Algebra/Polynomial/QuadraticDiscriminant.lean. The D5 import paths connect its actual proof dependencies to the original cone boundary consumer. It does not assume a cylindrical decomposition or semialgebraic projection certificate. The original source ownership is retained and no independent escape credit is claimed. Full license and attribution appear in the Lean source and docs/reports/licenses/TauCeti-LICENSE.txt. Each adaptation is retired when the actual pinned mathlib supplies an equivalent statement, replacing consumers by direct applications of that owner.

For the original field and a≠0, the quadratic aX²+bX+c splits exactly when it has a root, equivalently when b²-4ac is a square under the original characteristic assumptions. Pinned quadratic root/discriminant identities and the degree-two splitting criterion give both directions. In characteristic two the discriminant is b² and the remaining root condition is the stated Artin–Schreier equation, rather than division by two. Differentiation gives 2aX+b and (p′)²-4ap=C(b²-4ac). Hence discriminant zero gives a common root of p and p′ and the singleton root set; nonzero discriminant gives separability. The retained positive/negative quadratic evaluations use their original ordered-field hypotheses and include all zero-coefficient cases permitted by those hypotheses.

## References

- Dependency: [D5/S3/Geometry/AlgebraicBoundary/TauCeti/Algebra/QuadraticDiscriminant](../QuadraticDiscriminant.md)
