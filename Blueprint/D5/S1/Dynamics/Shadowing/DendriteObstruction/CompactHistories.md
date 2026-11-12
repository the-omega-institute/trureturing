# DendriteObstruction - Compact histories

## Abstract

Compact histories, maximal fibre multiplicity and the static arc-packing obstruction.

**Theorem 1.1 (Injective iterate arc inside an invariant set).**

Lean statement: `D5/S1/Dynamics/Shadowing/DendriteObstruction/CompactHistories.exists_iterate_injective_arc_invariant`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/DendriteObstruction/CompactHistories.exists_iterate_injective_arc_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let X be a compact metric space satisfying StaticArcHull and the no-circle law, and let Y be any forward-invariant subset containing an actual embedded nondegenerate arc A. A finitely positively expansive continuous self-map has an embedded nondegenerate arc K contained in Y on which every natural iterate is injective. Y need not be connected or compact.

The attained maximum ranges over actual histories whose complete source is contained in Y. The initial small subarc remains in A. The existing doubling construction returns its actual restricted source together with source inclusion, so doubling preserves this constraint. Exact terminal surjectivity and forward invariance place the terminal arc in Y. This reuses the compact double cover and full-prefix extension proofs.

**Theorem 1.2 (An embedded arc with all iterates injective).**

Lean statement: `D5/S1/Dynamics/Shadowing/DendriteObstruction/CompactHistories.exists_iterate_injective_arc`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/DendriteObstruction/CompactHistories.exists_iterate_injective_arc` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let X be a compact metric space containing an actual embedded nondegenerate closed interval. Assume every continuous map from AddCircle (1 : Real) to X fails to be injective. Assume also the purely static arc-hull law: for any distinct endpoints p,y, some embedded arc from p to y lies in every compact connected subset containing both endpoints. If a continuous self-map f is finitely positively expansive, there is an actual embedded nondegenerate arc K such that f^[n] is injective on K for every natural n, including zero.

A compact history consists of a nonempty compact source E, an actual terminal arc K, a time t, strict distance bounds at every time j <= t, exact image f^[t](E)=K, and a uniform lower bound r for every terminal fibre inside E. A small affine subarc initializes r=1. Each attainable r is bounded by the fixed all-time Bowen cardinal bound: a terminal fibre has controlled prefix and exactly coalescing tail. A finite maximum is therefore attained by actual history data.

A noninjective iterate on the attained terminal arc yields an arbitrarily short repeated pair by ShortLoops.short_repeated_pair_finite_prefix. Finite iterate fibres prohibit collapse of the entire loop interval and give a distinct interior image y. The static hull arc from the repeated value p to y lies in both half-path images. Its first half B excludes y. Intersecting the complete left and right source halves with the inverse image of B gives disjoint compact sets P and Q, each with exact image B; these sets are allowed to be disconnected. Restricting E to the complete inverse image of P union Q retains every old fibre. The two distinct intermediate fibres are disjoint and their cardinal lower bounds add, giving 2r at time t+q. Old prefix times follow from source inclusion; all new times t+j follow from the short-loop prefix bound. This contradicts maximality.

This dynamical core uses explicit static assumptions. StandardDendroid derives the arc-hull and no-circle laws from actual arcwise connectedness and hereditary unicoherence. MinimalInvariant reuses the persistence proof and replaces uniform arc packing by small co-connected openings; deriving that classical opening law from the standard carrier remains a separate static theorem. Analytic Pro advice is fallible; no model independence or diversity is asserted.

**Theorem 1.3 (The obstruction from static arc packing).**

Lean statement: `D5/S1/Dynamics/Shadowing/DendriteObstruction/CompactHistories.not_finitelyPositiveExpansive_of_static_arc_packing`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/DendriteObstruction/CompactHistories.not_finitelyPositiveExpansive_of_static_arc_packing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let X be a compact metric space with an actual embedded nondegenerate arc, the static arc-hull law, and the stated no-circle predicate. Assume the static uniform arc-packing law: for every delta > 0 some natural M bounds the size of every pairwise disjoint finite family of embedded subarcs of any one embedded arc, when each subarc has diameter at least delta. Then no continuous self-map f of X is finitely positively expansive. The conclusion uses the strict all-time ForwardBowenBound definition from IntervalObstruction.Basic, with time zero included. No invertibility, surjectivity, finite branching, free arc, local injectivity or dynamical return is assumed.

Uniform persistence is proved rather than assumed. Under a hypothetical Bowen bound with scale epsilon, no iterate collapses a nondegenerate compact continuum: the static hull supplies an infinite arc and finite iterate fibres preserve an infinite image. Every such continuum has an arbitrarily late image with diameter at least epsilon by arbitrarily_late_separation. Set a=epsilon/4. ArcGeometry.compact_continua_ge makes the family of subcontinua of diameter at least a compact. Continuity of each iterated-image diameter and finite subcover give a common finite positive time window within which any member has diameter greater than a. Noncollapse and the same compactness give a common positive lower bound delta for all iterates through this finite window. For an arbitrary later time, take the last preceding time with diameter at least a. The expansion window bounds the remaining time gap, so the finite-window lower bound applies. Thus every arc has diameter at least delta at every sufficiently late iterate.

The maximal-history theorem supplies an arc K whose every iterate is injective. An explicit affine construction gives M+1 pairwise disjoint nondegenerate subarcs in K. At one common late time, all their images have diameter at least delta. Injectivity on the whole K makes these images pairwise disjoint actual embedded subarcs of the actual embedded image of K. The static packing bound then gives M+1 <= M, a contradiction. This proves the packing obstruction under its explicitly stated static assumptions. The general-dendroid route in MinimalInvariant does not use UniformArcPacking, and no claim that this packing law holds for all dendroids is made.

## References

- Truth anchor: `D5/S1/Dynamics/Shadowing/DendriteObstruction/CompactHistories.exists_iterate_injective_arc`
- Truth anchor: `D5/S1/Dynamics/Shadowing/DendriteObstruction/CompactHistories.exists_iterate_injective_arc_invariant`
- Truth anchor: `D5/S1/Dynamics/Shadowing/DendriteObstruction/CompactHistories.not_finitelyPositiveExpansive_of_static_arc_packing`
- Dependency: [D5/S1/Dynamics/Shadowing/DendriteObstruction/ArcGeometry](ArcGeometry.md)
- Dependency: [D5/S1/Dynamics/Shadowing/DendriteObstruction/ShortLoops](ShortLoops.md)
- Dependency: [D5/S1/Dynamics/Shadowing/IntervalObstruction/Basic](../IntervalObstruction/Basic.md)
