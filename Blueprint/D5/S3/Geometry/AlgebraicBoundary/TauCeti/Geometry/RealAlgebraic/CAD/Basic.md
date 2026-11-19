# Pinned real algebraic source: TauCeti.Geometry.RealAlgebraic.CAD.Basic.

## Abstract

Pinned real algebraic source: TauCeti.Geometry.RealAlgebraic.CAD.Basic.

This content adaptation retains selected declarations and proof bodies from TauCetiProject/TauCeti revision 1f9b4414105d86e487a4ac4c3d3397076a44d0d2, TauCeti/Geometry/RealAlgebraic/CAD/Basic.lean. The D5 import paths connect its actual proof dependencies to the original cone boundary consumer. It does not assume a cylindrical decomposition or semialgebraic projection certificate. The original source ownership is retained and no independent escape credit is claimed. Full license and attribution appear in the Lean source and docs/reports/licenses/TauCeti-LICENSE.txt. Each adaptation is retired when the actual pinned mathlib supplies an equivalent statement, replacing consumers by direct applications of that owner.

For every dimension n, {univ} satisfies the recursive IsCAD predicate. The n=0 case is IsCAD.zero. At the successor choose k(C)=0 on the singleton base and θ:Fin 0→C→ℝ as the empty function. Continuity and section semialgebraicity eliminate Fin 0, strict monotonicity is vacuous, and the unique sector indexed by Fin 1 is all of C×ℝ. Over C=univ its ambient image is univ: y has preimage ((Fin.tail y,mem_univ _),y 0), and pinned Fin.cons_self_tail proves the inverse equation. Thus stackCells is exactly {univ}; IsCAD.succ and induction establish the full-dimensional result.

For polynomial sections θ with the original strict-order hypothesis, continuity is polynomial continuity and section/sector membership is a finite Boolean combination of polynomial equalities and strict inequalities. Constant sections over the zero-dimensional base give the full one-dimensional point-and-interval CAD, including no sections. General adapted CAD existence instead uses Delineation.isSemialgebraicStack, whose section and sector fields come from actual shared-root rank loci. IsCAD.isPartition retains its dimension induction, finite cover and pairwise disjointness; projection, sign samples, connectedness and semialgebraicity use those actual fields. No assumption of CAD existence or semialgebraic projection replaces this construction.

## References

- Dependency: [D5/S3/Geometry/AlgebraicBoundary/TauCeti/Geometry/RealAlgebraic/Semialgebraic/Basic](../Semialgebraic/Basic.md)
- Dependency: [D5/S3/Geometry/AlgebraicBoundary/TauCeti/Geometry/RealAlgebraic/SignInvariant](../SignInvariant.md)
- Dependency: [D5/S3/Geometry/AlgebraicBoundary/TauCeti/Geometry/RealAlgebraic/Stack/Basic](../Stack/Basic.md)
