# Pinned real algebraic source: TauCeti.Geometry.RealAlgebraic.Projection.Collins.

## Abstract

Pinned real algebraic source: TauCeti.Geometry.RealAlgebraic.Projection.Collins.

This content adaptation retains selected declarations and proof bodies from TauCetiProject/TauCeti revision 1f9b4414105d86e487a4ac4c3d3397076a44d0d2, TauCeti/Geometry/RealAlgebraic/Projection/Collins.lean. The D5 import paths connect its actual proof dependencies to the original cone boundary consumer. It does not assume a cylindrical decomposition or semialgebraic projection certificate. The original source ownership is retained and no independent escape credit is claimed. Full license and attribution appear in the Lean source and docs/reports/licenses/TauCeti-LICENSE.txt. Each adaptation is retired when the actual pinned mathlib supplies an equivalent statement, replacing consumers by direct applications of that owner.

Collins projection is the finite union of the original coefficient, reductum and principal-subresultant families. Its value at the empty family is empty and it is monotone under inclusion by finite union/image membership. Under a coefficient specialization, choose the actual cutoff one above the mapped degree; reductum_map identifies its image and the mapped-degree lemma supplies its degree. Thus the relevant PSC of the two specialized reducta, and the derivative variant, belongs to the image of the same projection family under precisely the original coefficient-ring and HasUniqueDiv hypotheses. No degree-preservation or non-nullification premise is added. The surviving delineability construction uses these actual cutoff witnesses.

## References

- Dependency: [D5/S3/Geometry/AlgebraicBoundary/TauCeti/Algebra/MvPolynomial/Equiv](../../../Algebra/MvPolynomial/Equiv.md)
- Dependency: [D5/S3/Geometry/AlgebraicBoundary/TauCeti/Algebra/Polynomial/Degree/Map](../../../Algebra/Polynomial/Degree/Map.md)
- Dependency: [D5/S3/Geometry/AlgebraicBoundary/TauCeti/Algebra/Polynomial/Derivative](../../../Algebra/Polynomial/Derivative.md)
- Dependency: [D5/S3/Geometry/AlgebraicBoundary/TauCeti/RingTheory/Polynomial/Reductum](../../../RingTheory/Polynomial/Reductum.md)
- Dependency: [D5/S3/Geometry/AlgebraicBoundary/TauCeti/RingTheory/Polynomial/Roots](../../../RingTheory/Polynomial/Roots.md)
- Dependency: [D5/S3/Geometry/AlgebraicBoundary/TauCeti/RingTheory/Polynomial/Subresultant/GCD](../../../RingTheory/Polynomial/Subresultant/GCD.md)
