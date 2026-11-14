# Pinned real algebraic source: TauCeti.Geometry.RealAlgebraic.Stack.Delineation.

## Abstract

Pinned real algebraic source: TauCeti.Geometry.RealAlgebraic.Stack.Delineation.

This content adaptation retains selected declarations and proof bodies from TauCetiProject/TauCeti revision 1f9b4414105d86e487a4ac4c3d3397076a44d0d2, TauCeti/Geometry/RealAlgebraic/Stack/Delineation.lean. The D5 import paths connect its actual proof dependencies to the original cone boundary consumer. It does not assume a cylindrical decomposition or semialgebraic projection certificate. The original source ownership is retained and no independent escape credit is claimed. Full license and attribution appear in the Lean source and docs/reports/licenses/TauCeti-LICENSE.txt. Each adaptation is retired when the actual pinned mathlib supplies an equivalent statement, replacing consumers by direct applications of that owner.

For the original topological base, family of real polynomials and continuous strictly increasing root functions with supplied degree, multiplicity and exhaustive-root data, Delineation.ofRoots uses precisely those functions and multiplicities. On a preconnected base, sections have constant polynomial sign by continuous-image preconnectedness; each sector has a continuous midpoint or exterior graph meeting every order-connected fiber, so the whole sector is preconnected. The local ball construction restricts these data using Metric.eventually_nhds_iff and convex_ball; it adds no global connectedness premise. Restricting a delineation along a continuous map composes its actual functions and preserves all fields.

The useful general CAD path retains root_notMem_uIcc_of_sign_eval_eq and both implications of mk_mem_sectionSet_iff_of_sign_eval_eq. Positive multiplicity chooses a nonzero polynomial; derivative closure supplies every derivative-sign equality. The live Rolle interval argument then excludes a root between the points. General section and sector semialgebraicity uses shared-root membership and rank loci, including nullified polynomials and empty families.

## References

- Dependency: [D5/S3/Geometry/AlgebraicBoundary/TauCeti/Algebra/MvPolynomial/Equiv](../../../Algebra/MvPolynomial/Equiv.md)
- Dependency: [D5/S3/Geometry/AlgebraicBoundary/TauCeti/Algebra/Polynomial/Thom](../../../Algebra/Polynomial/Thom.md)
- Dependency: [D5/S3/Geometry/AlgebraicBoundary/TauCeti/Analysis/Polynomial/RealRoots/Common](../../../Analysis/Polynomial/RealRoots/Common.md)
- Dependency: [D5/S3/Geometry/AlgebraicBoundary/TauCeti/FieldTheory/IsRealClosed/Real](../../../FieldTheory/IsRealClosed/Real.md)
- Dependency: [D5/S3/Geometry/AlgebraicBoundary/TauCeti/FieldTheory/RealClosure/AbstractRolle](../../../FieldTheory/RealClosure/AbstractRolle.md)
- Dependency: [D5/S3/Geometry/AlgebraicBoundary/TauCeti/Geometry/RealAlgebraic/Stack/Sign](Sign.md)
- Dependency: [D5/S3/Geometry/AlgebraicBoundary/TauCeti/RingTheory/Polynomial/Roots](../../../RingTheory/Polynomial/Roots.md)
- Dependency: [D5/S3/Geometry/AlgebraicBoundary/TauCeti/Topology/Algebra/Polynomial/Basic](../../../Topology/Algebra/Polynomial/Basic.md)
