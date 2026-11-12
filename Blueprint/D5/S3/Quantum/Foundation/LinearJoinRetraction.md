# Linear join retractions and effect transport

## Abstract

Positive trace-subunital retractions and full proper-effect transport across a real linear join.

Let A be a finite dimensional real normed vector space with a pointed cone C and a linear unit u. A JoinData record specifies left and right subspaces U and W, their entire overlap S, a topological linear join U sup W = A, and overlap projections that fix S. The side cone is the exact comap of C along the subspace inclusion and the side unit is u restricted along that inclusion. No finite-pure, identity-membership, or selected-effect assumption is part of this interface.

**Definition 1.1 (The cone on a supported side).**

Lean statement: `D5/S3/Quantum/Foundation/LinearJoinRetraction.sideCone`

*Formalization.* `D5/S3/Quantum/Foundation/LinearJoinRetraction.sideCone` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

sideCone C U contains exactly the vectors of U whose ambient inclusion lies in the original cone C.

**Definition 1.2 (The inherited unit).**

Lean statement: `D5/S3/Quantum/Foundation/LinearJoinRetraction.sideUnit`

*Formalization.* `D5/S3/Quantum/Foundation/LinearJoinRetraction.sideUnit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

sideUnit u U is the original linear unit composed with the inclusion of U into A.

**Definition 1.3 (An entire linear join with overlap projections).**

Lean statement: `D5/S3/Quantum/Foundation/LinearJoinRetraction.JoinData`

*Formalization.* `D5/S3/Quantum/Foundation/LinearJoinRetraction.JoinData` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

JoinData records U, W and their equality S=U intersect W, the whole join U sup W=A, and projections W to S and U to S that are the identity on the overlap. The projection equalities make the two glued retractions independent of decompositions.

**Definition 1.4 (The full original proper-effect interval).**

Lean statement: `D5/S3/Quantum/Foundation/LinearJoinRetraction.properEffect`

*Formalization.* `D5/S3/Quantum/Foundation/LinearJoinRetraction.properEffect` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

properEffect packages every real linear functional satisfying 0 <= f(x) <= u(x) for every x in the entire original cone.

**Definition 1.5 (A side proper-effect interval).**

Lean statement: `D5/S3/Quantum/Foundation/LinearJoinRetraction.sideProperEffect`

*Formalization.* `D5/S3/Quantum/Foundation/LinearJoinRetraction.sideProperEffect` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

sideProperEffect is the same full proper interval on the exact side cone and inherited side unit.

**Definition 1.6 (Restrict a full original proper effect).**

Lean statement: `D5/S3/Quantum/Foundation/LinearJoinRetraction.restrictEffect`

*Formalization.* `D5/S3/Quantum/Foundation/LinearJoinRetraction.restrictEffect` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

restrictEffect composes an original proper effect with the side inclusion, retaining the full pointwise bounds on every side-cone element.

**Definition 1.7 (The full proper-effect midpoint law).**

Lean statement: `D5/S3/Quantum/Foundation/LinearJoinRetraction.G2`

*Formalization.* `D5/S3/Quantum/Foundation/LinearJoinRetraction.G2` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

G2 quantifies over every pure reference p and pure q,r. Different full proper confirming effects may witness p perpendicular q and p perpendicular r, while one confirming proper effect must vanish at the midpoint (q+r)/2.

**Definition 1.8 (ROG support certificate for the left side).**

Lean statement: `D5/S3/Quantum/Foundation/LinearJoinRetraction.RetractionCertificate`

*Formalization.* `D5/S3/Quantum/Foundation/LinearJoinRetraction.RetractionCertificate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A RetractionCertificate gives a generator set for the original cone, proves every generator is sent by the left retraction back into C, proves the inherited unit does not increase on generators, and lifts every side pure point to an original pure point with the same ambient vector.

**Definition 1.9 (ROG support certificate for the right side).**

Lean statement: `D5/S3/Quantum/Foundation/LinearJoinRetraction.RightRetractionCertificate`

*Formalization.* `D5/S3/Quantum/Foundation/LinearJoinRetraction.RightRetractionCertificate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

RightRetractionCertificate supplies the symmetric generator, positivity, subunit and pure-lift data for W.

**Definition 1.10 (The left supported cone as a retraction image).**

Lean statement: `D5/S3/Quantum/Foundation/LinearJoinRetraction.supportedConeLeft`

*Formalization.* `D5/S3/Quantum/Foundation/LinearJoinRetraction.supportedConeLeft` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

supportedConeLeft is the image of the original generating hull under the left retraction.

**Definition 1.11 (The right supported cone as a retraction image).**

Lean statement: `D5/S3/Quantum/Foundation/LinearJoinRetraction.supportedConeRight`

*Formalization.* `D5/S3/Quantum/Foundation/LinearJoinRetraction.supportedConeRight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

supportedConeRight is the symmetric image of the original generating hull under the right retraction.

**Theorem 1.12 (Exact left supported-cone equality).**

Lean statement: `D5/S3/Quantum/Foundation/LinearJoinRetraction.supportedConeLeft_eq_sideCone`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/LinearJoinRetraction.supportedConeLeft_eq_sideCone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The image of the full original generating hull under the left retraction equals the exact ambient cone comapped to U. This is the abstract ROG form of the supported PSD intersection.

**Theorem 1.13 (Exact right supported-cone equality).**

Lean statement: `D5/S3/Quantum/Foundation/LinearJoinRetraction.supportedConeRight_eq_sideCone`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/LinearJoinRetraction.supportedConeRight_eq_sideCone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The right retraction image of the full original generating hull equals the exact cone cut down to W.

**Theorem 1.14 (Extend every left proper effect).**

Lean statement: `D5/S3/Quantum/Foundation/LinearJoinRetraction.extend_effect_left`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/LinearJoinRetraction.extend_effect_left` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every proper effect on the complete left side extends by composition with the left retraction to a proper effect on all of C. The proof propagates generator bounds through the conic hull and preserves the inherited unit inequality.

**Theorem 1.15 (Extend every right proper effect).**

Lean statement: `D5/S3/Quantum/Foundation/LinearJoinRetraction.extend_effect_right`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/LinearJoinRetraction.extend_effect_right` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The corresponding composition with the right retraction extends every proper effect on W to the full original interval.

**Theorem 1.16 (Full effect restriction is onto on the left).**

Lean statement: `D5/S3/Quantum/Foundation/LinearJoinRetraction.restrict_surjective_left`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/LinearJoinRetraction.restrict_surjective_left` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Restriction of the entire original proper-effect interval to U is surjective. The extension is the left proper effect composed with the positive retraction and restricts back exactly on U.

**Theorem 1.17 (Full effect restriction is onto on the right).**

Lean statement: `D5/S3/Quantum/Foundation/LinearJoinRetraction.restrict_surjective_right`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/LinearJoinRetraction.restrict_surjective_right` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Restriction of the entire original proper-effect interval to W is likewise surjective, with the right retraction as the extension map.

**Theorem 1.18 (Exact left comparison correspondence).**

Lean statement: `D5/S3/Quantum/Foundation/LinearJoinRetraction.comparison_correspondence_left`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/LinearJoinRetraction.comparison_correspondence_left` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every left pure reference and every left vector, the infimum over the complete side proper-effect interval equals the original comparison at the ambient vectors. Restriction and retraction extension identify the two confirming-effect value sets exactly.

**Theorem 1.19 (Exact right comparison correspondence).**

Lean statement: `D5/S3/Quantum/Foundation/LinearJoinRetraction.comparison_correspondence_right`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/LinearJoinRetraction.comparison_correspondence_right` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same equality of full confirming-effect value sets holds on W for every right pure reference and every right vector.

**Theorem 1.20 (G2 inheritance on the left).**

Lean statement: `D5/S3/Quantum/Foundation/LinearJoinRetraction.inherit_G2_left`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/LinearJoinRetraction.inherit_G2_left` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the original carrier satisfies G2, the left side satisfies G2 using its complete proper-effect interval. Side witnesses extend to original witnesses, the original common midpoint witness is restricted back, and the pure-lift clauses preserve every pure and mixed quantifier.

**Theorem 1.21 (G2 inheritance on the right).**

Lean statement: `D5/S3/Quantum/Foundation/LinearJoinRetraction.inherit_G2_right`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/LinearJoinRetraction.inherit_G2_right` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same argument transports G2 to W with the full right proper-effect interval and the right pure-lift certificate.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/LinearJoinRetraction.G2`
- Truth anchor: `D5/S3/Quantum/Foundation/LinearJoinRetraction.JoinData`
- Truth anchor: `D5/S3/Quantum/Foundation/LinearJoinRetraction.RetractionCertificate`
- Truth anchor: `D5/S3/Quantum/Foundation/LinearJoinRetraction.RightRetractionCertificate`
- Truth anchor: `D5/S3/Quantum/Foundation/LinearJoinRetraction.comparison_correspondence_left`
- Truth anchor: `D5/S3/Quantum/Foundation/LinearJoinRetraction.comparison_correspondence_right`
- Truth anchor: `D5/S3/Quantum/Foundation/LinearJoinRetraction.extend_effect_left`
- Truth anchor: `D5/S3/Quantum/Foundation/LinearJoinRetraction.extend_effect_right`
- Truth anchor: `D5/S3/Quantum/Foundation/LinearJoinRetraction.inherit_G2_left`
- Truth anchor: `D5/S3/Quantum/Foundation/LinearJoinRetraction.inherit_G2_right`
- Truth anchor: `D5/S3/Quantum/Foundation/LinearJoinRetraction.properEffect`
- Truth anchor: `D5/S3/Quantum/Foundation/LinearJoinRetraction.restrictEffect`
- Truth anchor: `D5/S3/Quantum/Foundation/LinearJoinRetraction.restrict_surjective_left`
- Truth anchor: `D5/S3/Quantum/Foundation/LinearJoinRetraction.restrict_surjective_right`
- Truth anchor: `D5/S3/Quantum/Foundation/LinearJoinRetraction.sideCone`
- Truth anchor: `D5/S3/Quantum/Foundation/LinearJoinRetraction.sideProperEffect`
- Truth anchor: `D5/S3/Quantum/Foundation/LinearJoinRetraction.sideUnit`
- Truth anchor: `D5/S3/Quantum/Foundation/LinearJoinRetraction.supportedConeLeft`
- Truth anchor: `D5/S3/Quantum/Foundation/LinearJoinRetraction.supportedConeLeft_eq_sideCone`
- Truth anchor: `D5/S3/Quantum/Foundation/LinearJoinRetraction.supportedConeRight`
- Truth anchor: `D5/S3/Quantum/Foundation/LinearJoinRetraction.supportedConeRight_eq_sideCone`
- Dependency: [D5/S3/Quantum/Foundation/WeightedRelationConfirmation](WeightedRelationConfirmation.md)
