# Pinned real algebraic source: TauCeti.Analysis.Polynomial.ContinuityOfRoots.Basic.

## Abstract

Pinned real algebraic source: TauCeti.Analysis.Polynomial.ContinuityOfRoots.Basic.

This content adaptation retains selected declarations and proof bodies from TauCetiProject/TauCeti revision 1f9b4414105d86e487a4ac4c3d3397076a44d0d2, TauCeti/Analysis/Polynomial/ContinuityOfRoots/Basic.lean. The D5 import paths connect its actual proof dependencies to the original cone boundary consumer. It does not assume a cylindrical decomposition or semialgebraic projection certificate. The original source ownership is retained and no independent escape credit is claimed. Full license and attribution appear in the Lean source and docs/reports/licenses/TauCeti-LICENSE.txt. Each adaptation is retired when the actual pinned mathlib supplies an equivalent statement, replacing consumers by direct applications of that owner.

With the original monic degree and separability/separation hypotheses, nearby root tuples are matched by disjoint balls. The triangle inequality makes the ball-center assignment unique. Occurrence counts are Nat.card of fibers, equal to filter cardinalities for finite indices. Equal fiber cardinalities produce a commuting permutation by pinned Equiv.ofFiberEquiv and Fintype.equivOfCardEq; conversely a commuting permutation preserves each count. Thus the full matching/count equivalence includes both directions. Evaluating the product recovers the polynomial by coefficient mapping. Disc counts equal root multiplicities under the original separated-center hypotheses. For the actual general-family path, normalize by the nonzero leading coefficient, use the continuous coefficient chart for nearby tuples, and multiply back; this retains multiple roots and the original factorization data.

## References

- Dependency: [D5/S3/Geometry/AlgebraicBoundary/TauCeti/Analysis/Polynomial/SymmetricPower](../SymmetricPower.md)
- Dependency: [D5/S3/Geometry/AlgebraicBoundary/TauCeti/Data/Fintype/Fiber](../../../Data/Fintype/Fiber.md)
- Dependency: [D5/S3/Geometry/AlgebraicBoundary/TauCeti/Topology/MetricSpace/SeparatedBalls](../../../Topology/MetricSpace/SeparatedBalls.md)
