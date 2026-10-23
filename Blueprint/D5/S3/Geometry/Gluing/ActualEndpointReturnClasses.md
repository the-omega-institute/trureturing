# Original pure endpoints and actual return classes

## Abstract

The classes of literal pure endpoints in the original point quotient correspond to the four actual fiber return-cycle quotients.

**Definition 1.1 (The original label fiber).**

Lean statement: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.Flag`

*Formalization.* `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.Flag` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A flag is an original ordered dart (omega,j,k) with j different from k and with the original corner label equal to nu. No endpoint sorting, different quotient or orbit enlargement is performed.

**Definition 1.2 (Pure barycentric coordinates).**

Lean statement: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.delta`

*Formalization.* `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.delta` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coordinate at the selected tip is exactly one; all other coordinates are zero.

**Definition 1.3 (The endpoint in the original carrier).**

Lean statement: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.endpoint`

*Formalization.* `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.endpoint` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The original corner and its delta coordinates satisfy the unchanged Carrier: the omitted coordinate is zero, coordinates are nonnegative, their sum is one and their corner label is nu.

**Definition 1.4 (The pure endpoint locus).**

Lean statement: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.Endpoints`

*Formalization.* `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.Endpoints` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the range of the literal endpoint map inside the full original carrier, before any quotient is taken.

**Definition 1.5 (The original point quotient).**

Lean statement: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.PointQuotient`

*Formalization.* `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.PointQuotient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The quotient uses exactly EqvGen of the original guarded Step. It includes every original intermediate in a chain.

**Definition 1.6 (The restricted original dart relation).**

Lean statement: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.flagSetoid`

*Formalization.* `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.flagSetoid` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the pullback of the original DartRelated setoid to Flag. The theorem proves flag and label saturation before identifying it with the generated restricted relation.

**Definition 1.7 (Original endpoint flag classes).**

Lean statement: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.FlagQuotient`

*Formalization.* `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.FlagQuotient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take the quotient of the nu-restricted flags by the full original dart relation.

**Definition 1.8 (The actual map to point classes).**

Lean statement: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.endpointClassMap`

*Formalization.* `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.endpointClassMap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Send each flag class to its literal endpoint class in the unchanged point quotient. Full bidirectional relation correspondence makes this map injective.

**Definition 1.9 (Four distinct root fibers).**

Lean statement: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.Root`

*Formalization.* `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.Root` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

In row order L0,L1,H2,H0, a root sheet has original corner number 0,1,2,0 respectively, and that corner has label nu. These fibers remain distinct until an explicit equivalence transports them.

**Definition 1.10 (Actual return permutations).**

Lean statement: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.returnPerm`

*Formalization.* `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.returnPerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two low rows act by ell = v inverse times u squared; the two high rows by h = v squared times u. These are permutations of the original arbitrary right action.

**Definition 1.11 (Returns in the selected root fibers).**

Lean statement: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.rootReturn`

*Formalization.* `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.rootReturn` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Prove preservation of the original nu label, then restrict the actual return permutation to its Root. The construction allows nonfaithful, nonfree and nontransitive finite actions.

**Definition 1.12 (Actual root-return cycle classes).**

Lean statement: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.RootCycles`

*Formalization.* `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.RootCycles` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The cycle quotient is SameCycle of the actual restricted permutation. Every fixed point is a cycle; period one is included.

**Definition 1.13 (The four row quotients).**

Lean statement: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.ReturnClasses`

*Formalization.* `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.ReturnClasses` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The dependent sum over four rows contains their actual root-return cycle quotients. It counts no other nu component and uses no order of an acting group element.

**Definition 1.14 (Actual phase-zero flags).**

Lean statement: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.rootFlag`

*Formalization.* `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.rootFlag` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Encode a sheet in its original row at phase zero, preserving the original ordered endpoint pair and label.

**Definition 1.15 (The component enumeration consumer).**

Lean statement: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.returnClassMap`

*Formalization.* `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.returnClassMap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Map each actual root-return class through its phase-zero flag to the original flag quotient. Injectivity follows from the full component enumeration and unique row/phase classification. Surjectivity pulls an arbitrary valid dart back by its actual phase offset and uses an occurrence of the same enumeration to reach it from phase zero.

**Definition 1.16 (Faithful return-class correspondence).**

Lean statement: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.returnClassesEquiv`

*Formalization.* `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.returnClassesEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The equivalence uses that actual map and its proved bijectivity. The proof reduces natural returns modulo the least positive pointPeriod supplied by actual_component_enumeration; it does not substitute the order of the return word.

**Definition 1.17 (Marked classes in the original quotient).**

Lean statement: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.EndpointClasses`

*Formalization.* `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.EndpointClasses` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

These are the range of the injective endpointClassMap, an actual subset of the original point quotient.

**Definition 1.18 (Return classes as actual point classes).**

Lean statement: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.endpointClassesEquiv`

*Formalization.* `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.endpointClassesEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Compose the return-class equivalence with the injective original endpoint map onto its range. Its representative formula commutes with the original point quotient map.

**Definition 1.19 (The slot-zero fiber).**

Lean statement: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.ZeroFiber`

*Formalization.* `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.ZeroFiber` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

O_nu contains exactly those original sheets whose corner (omega,0) has label nu.

**Definition 1.20 (Preserving labels under corner normalization).**

Lean statement: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.rootToZero`

*Formalization.* `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.rootToZero` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For row c, act by u to the power of its original root corner number. The public actual_corner_orbit_iff proves this is an equivalence to O_nu with inverse action by the inverse power. The proof keeps arbitrary groups and the same original corner quotient.

**Definition 1.21 (Conjugated actual returns).**

Lean statement: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.zeroReturn`

*Formalization.* `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.zeroReturn` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Conjugate rootReturn by rootToZero. The same-cycle relation is transported in both directions by this equivalence.

**Definition 1.22 (The four words in row order).**

Lean statement: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.normalizedWord`

*Formalization.* `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.normalizedWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The words are inverse s, inverse t, s times k, and k times t, using the original sWord,tWord,kWord. Thus they are c1, inverse c3, c2, inverse c4. Inverting a permutation preserves SameCycle; the conventional final c1,c2,c3,c4 order is the row order 0,2,1,3.

**Definition 1.23 (The conventional boundary order).**

Lean statement: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.rowOrder`

*Formalization.* `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.rowOrder` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The involutive row permutation (0,2,1,3) transports the original L0,L1,H2,H0 order into c1,c2,c3,c4 order.

**Definition 1.24 (Original boundary words).**

Lean statement: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.boundaryWord`

*Formalization.* `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.boundaryWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

In conventional order the words are inverse s, s times k, t, inverse of k times t. They act on the same slot-zero fiber O_nu.

**Definition 1.25 (Actual oriented boundary returns).**

Lean statement: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.boundaryReturn`

*Formalization.* `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.boundaryReturn` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Reorder the proved zeroReturn permutations and invert the last two. The theorem proves that these permutations act by the corresponding original boundaryWord.

**Definition 1.26 (Cycles of the actual boundary returns).**

Lean statement: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.BoundaryCycles`

*Formalization.* `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.BoundaryCycles` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Use SameCycle of boundaryReturn on O_nu, retaining fixed points and repeated point classes.

**Definition 1.27 (Four boundary cycle quotients).**

Lean statement: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.BoundaryClasses`

*Formalization.* `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.BoundaryClasses` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This dependent sum uses the actual returns c1,c2,c3,c4 on the selected original slot-zero fiber.

**Definition 1.28 (Fiber, conjugacy and inverse correspondence).**

Lean statement: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.boundaryClassesEquiv`

*Formalization.* `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.boundaryClassesEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Quotient.congr transports the proved rootToZero equivalences; Mathlib's sameCycle_inv justifies the inverse directions; sigma congruence applies the row permutation. These are actual class equivalences, not count substitutions.

**Definition 1.29 (Boundary cycles as original endpoint classes).**

Lean statement: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.boundaryEndpointEquiv`

*Formalization.* `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.boundaryEndpointEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Compose the actual boundary-class equivalence with the original endpoint-class equivalence. The theorem includes the commuting equality with the unchanged point quotient.

**Theorem 1.30 (Full endpoint restriction and actual return classes).**

Lean statement: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.actual_endpoint_return_classes`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.actual_endpoint_return_classes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every group G, arbitrary right action on a finite Omega, u,v in G and original corner class nu, two literal pure endpoints are Related if and only if their flags are DartRelated. The full original dart chain is equivalent to its nu-restricted flag chain, and the endpoint locus is saturated under every full original point chain. For any two points of the pure endpoint locus, the full original Related relation holds exactly when those points are connected by EqvGen of the original Step restricted to that locus.

The return-class equivalences above identify the actual endpoint classes with the four actual root-fiber cycle quotients and commute with the original point quotient. The theorem retains the existing positive point period and exact tour period three times that period, and proves the slot-zero conjugacy and both directions of same-cycle transport.

Point-relation reflection consumes actual_guarded_point_analysis through the strict neighborhood of the source endpoint. Restriction and saturation keep all transitive intermediates. The cycle correspondence consumes the exhaustion, unique ordered-pair classification and indexed occurrence formula of actual_component_enumeration. No component enumeration or minimal-period theorem is reproved.

Repeated quotient classes, period one, nonregular and nonfaithful actions are allowed. If Omega is empty, the statement quantified over its original nu is vacuous. The two low rows share a return word but have different root fibers; they are identified with slot zero only by the proved corner normalization equivalences.

This source-specific inference is derived from the original corner-pairing suppliers and pinned Mathlib relation and permutation APIs. It makes no literature-priority claim. It is an endpoint and cycle-class correspondence: a faithful polygon adapter, invariance under complete polygon normalization, manifold structure, orientation, Euler characteristic and genus require separate constructions and proofs.

## References

- Truth anchor: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.BoundaryClasses`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.BoundaryCycles`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.EndpointClasses`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.Endpoints`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.Flag`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.FlagQuotient`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.PointQuotient`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.ReturnClasses`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.Root`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.RootCycles`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.ZeroFiber`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.actual_endpoint_return_classes`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.boundaryClassesEquiv`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.boundaryEndpointEquiv`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.boundaryReturn`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.boundaryWord`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.delta`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.endpoint`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.endpointClassMap`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.endpointClassesEquiv`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.flagSetoid`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.normalizedWord`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.returnClassMap`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.returnClassesEquiv`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.returnPerm`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.rootFlag`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.rootReturn`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.rootToZero`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.rowOrder`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualEndpointReturnClasses.zeroReturn`
- Dependency: [D5/S3/Geometry/Gluing/ActualCornerPointPeriods](ActualCornerPointPeriods.md)
