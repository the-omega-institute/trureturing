# Pinned real algebraic source: TauCeti.Topology.Sym.Disjoint.

## Abstract

Pinned real algebraic source: TauCeti.Topology.Sym.Disjoint.

This content adaptation retains selected declarations and proof bodies from TauCetiProject/TauCeti revision 1f9b4414105d86e487a4ac4c3d3397076a44d0d2, TauCeti/Topology/Sym/Disjoint.lean. The D5 import paths connect its actual proof dependencies to the original cone boundary consumer. It does not assume a cylindrical decomposition or semialgebraic projection certificate. The original source ownership is retained and no independent escape credit is claimed. Full license and attribution appear in the Lean source and docs/reports/licenses/TauCeti-LICENSE.txt. Each adaptation is retired when the actual pinned mathlib supplies an equivalent statement, replacing consumers by direct applications of that owner.

For the original pairwise disjoint open coordinate sets, the ofFn map on their product is injective by multiset matching and disjointness. Its continuity comes from the quotient map and its openness from the open permutation saturation. These three properties give the claimed open embedding. Empty index families and singleton sets use the same finite quotient argument; no choice of globally ordered roots is made.

## References

- Dependency: [D5/S3/Geometry/AlgebraicBoundary/TauCeti/Data/Sym/Disjoint](../../Data/Sym/Disjoint.md)
- Dependency: [D5/S3/Geometry/AlgebraicBoundary/TauCeti/Topology/Sym/Basic](Basic.md)
