# Signed proper countable limit extension

## Abstract

Joint preservation at the literal proper countable coordinate limit, with fixed parity reservoirs and full signed every-choice convergence.

Coord(a) is the set of ordinals below a and Cube(a) is Coord(a) to Bool. Prefix(l) contains a closed nonempty subset of Cube(a) for every a<l, literal restriction compatibility, and surjectivity of all old restrictions. It includes finite initial stages. LimitSpace(H) is the literal subset of Cube(l) whose restriction belongs to every old carrier. The new projection is coordinate restriction. coneIsLimit constructs the universal map: coordinate xi is read at succ(xi)<l, with cone naturality proving all old-stage equations. Compactness follows from closedness in the cube. properMetric selects a compatible metric only under l<omegaOne.

**Theorem 1.1 (Onto literal limit restrictions).**

$$\forall l: Ordinal0, \forall H: \operatorname{Prefix}\left(l\right), \operatorname{IsSuccLimit}\left(l\right) \Rightarrow \forall a: \operatorname{Coord}\left(l\right), \operatorname{Surjective}\left(\operatorname{projection}\left(H, a\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/InverseLimit/SignedProperLimit.projection_surjective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This consumed topology adapter uses compact_projection_image on the actual old diagram. Old onto maps put every old point in the eventual range. The explicitly proved coneIsLimit transports the compatible thread to the literal coordinate subset. Countability is not needed for this statement.

**Theorem 1.2 (Complete proper-stage preservation).**

$$\forall l: Ordinal0, \forall H: \operatorname{Prefix}\left(l\right), \operatorname{IsSuccLimit}\left(l\right) \Rightarrow \operatorname{Lt}\left(l, omegaOne\right) \Rightarrow \operatorname{Lt}\left(omega, l\right) \Rightarrow \forall D: \operatorname{Data}\left(H\right), \operatorname{Laws}\left(H, D\right) \Rightarrow \operatorname{Nonempty}\left(\operatorname{Extension}\left(H, D\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/InverseLimit/SignedProperLimit.exists_joint_proper_limit_extension` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

RegularSigned(K) consists of actual finite signed Borel measures with both Jordan parts regular. Data retains the proper-stage bound, I(r,a), J(r,d,a), fixed N(r,d,e), clopen birth supports V(r,n), and the full signed birth enumeration nu(r,d,n) for every d<omegaOne, including future labels. Mass one is required only at born rows omega<=r. Only omega<=r<a<l is an I domain; J additionally requires d<a. Off-domain total-function values carry no obligations. The assumptions use no positivity or support restriction beyond what is needed here, so every original supported signed class is included. Laws contains A: J subset I; B: the two fixed N pieces are disjoint; C: each J intersect N piece is infinite; DI and DJ: later sets are contained modulo finite sets in every earlier defined set. E quantifies over every coordinate r<=xi<a and every pair in the entire pulled-back support with the same row projection. F quantifies over every global all-Nat regular signed selection of mass one and exact row pushforward. Its conclusion is an actual regular signed represented weak-star limit of mass at most one along atTop intersect principal(J).

Extension supplies new I and J for every omega<=r<l and every d<l, reusing Data.N literally. It contains the proved IsLimit of the actual coordinate cone, onto projections, A through D against every earlier defined domain, whole-support E for every r<=xi<l, nonempty actual norm-preserving lift classes, and represented signed every-choice F in the same filter form. No new-stage E, F, unexplained IsLimit, desired represented limit, or final omegaOne bookkeeping is a premise.

For each row, a monotone cofinal countable sequence above it and a countable label coding instantiate the existing CountableJointFusion theorem with finite active labels and eventual activity. Its cofinite inclusions extend to every old stage by cofinality and old DI/DJ. E transports through one stage above the requested coordinate. NormPreservingLiftExistence gives actual class nonvacuity.

For an arbitrary global new selection and one fixed clopen, Profinite.exists_isClopen_of_cofiltered gives exact descent. Enlarge its stage above row and label. Project the selection for every natural index; the two variation contractions, with mass one at both ends, prove the intermediate projection has mass one. Compact metric regularity supplies both Jordan parts. Apply old F directly to this global projection, then restrict along the new J. The exact clopen preimage identity gives Cauchy evaluations along the increasing enumeration of the infinite new J. ClopenCauchyConvergence supplies an actual represented regular signed weak-star limit, and enumeration transports it to the original filter. Each clopen chooses its own stage; no uniform eventual assertion over all observables is inferred.

This is a local limit-extension unit of the full signed construction. It does not supply successor splitting, CH enumeration, the transfinite recursion, anti-homeomorphism or analytic endpoints, or a solution of Problem 8.2.

## References

- Truth anchor: `D5/S3/Topology/InverseLimit/SignedProperLimit.exists_joint_proper_limit_extension`
- Truth anchor: `D5/S3/Topology/InverseLimit/SignedProperLimit.projection_surjective`
- Dependency: [D5/S1/Dynamics/Shadowing/MittagLefflerInverseLimit](../../../S1/Dynamics/Shadowing/MittagLefflerInverseLimit.md)
- Dependency: [D5/S3/Topology/InverseLimit/CountableJointFusion](CountableJointFusion.md)
- Dependency: [D5/S3/Topology/Measures/ClopenCauchyConvergence](../Measures/ClopenCauchyConvergence.md)
- Dependency: [D5/S3/Topology/Measures/NormPreservingLiftExistence](../Measures/NormPreservingLiftExistence.md)
