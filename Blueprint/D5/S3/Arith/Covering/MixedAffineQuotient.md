# Phase-preserving mixed affine quotient

## Abstract

Guarded affine congruence systems descend exactly through a binary quotient with unchanged phases.

Fix a positive integer M and common period N equal to twice M. Each event has a fixed phase-compatibility guard and an arbitrary indexed family of rows e dividing a k plus b l minus c. Every modulus is positive and divides N. All coefficients and phases are unrestricted integers. The event and row index types may be empty, and zero normals are permitted.

**Definition 1.1 (Activation and binary carry).**

Lean statement: `D5/S3/Arith/Covering/MixedAffineQuotient.carry`

*Formalization.* `D5/S3/Arith/Covering/MixedAffineQuotient.carry` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each original row put q equal to N divided by e, and F equal to q times the original affine expression. At the lift (k plus M u, l plus M v), the row requires M to divide F and requires F divided by M plus q times (a u plus b v) to be even. The original guard is also required. Activation of all rows need not imply consistency of these equations.

**Definition 1.2 (Original-event witnesses for affine shapes).**

Lean statement: `D5/S3/Arith/Covering/MixedAffineQuotient.Witness`

*Formalization.* `D5/S3/Arith/Covering/MixedAffineQuotient.Witness` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each nonempty binary shape has a prescribed anchor. Its witness requires the original guarded event at the anchor lift. For each binary point, the homogeneous rows q times the normal applied to its displacement from the anchor must be even exactly when the point belongs to the shape. These homogeneous tests depend on the coefficients and period, not on new phases. The full, line and point witnesses feed the six mixed-cover alternatives.

**Definition 1.3 (Conjunctions at a common representative).**

Lean statement: `D5/S3/Arith/Covering/MixedAffineQuotient.ProjectedCriterion`

*Formalization.* `D5/S3/Arith/Covering/MixedAffineQuotient.ProjectedCriterion` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The projected criterion allows an integer representative (k plus M z, l plus M w). Every event selected by one minimal pattern is then tested at its prescribed offset from that same representative. Thus each alternative is a conjunction of original event predicates at shifted representatives, subject to fixed homogeneous shape tests. No phase variable is chosen by projection.

**Theorem 1.4 (Exact mixed descent).**

Lean statement: `D5/S3/Arith/Covering/MixedAffineQuotient.result`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Covering/MixedAffineQuotient.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The theorem proves the carry equation for every integer lift and classifies every event slice as empty, full, line or point. A shape witness is equivalent to a nonempty shape being exactly that slice. For every integer basepoint, coverage of its four binary lifts is equivalent to the six-pattern criterion. That criterion is invariant under arbitrary integer multiples of M in both coordinates, and is equivalent to its projected form.

Coverage of every integer pair, and coverage of the square from zero inclusive to N exclusive, are each equivalent to the criterion holding throughout the square from zero inclusive to M exclusive. All statements concern the same original row phases and guards. They assert no existence of a covering phase assignment.

Three corners in an affine congruence system force the fourth, by the parallelogram identity for every row. Consequently a binary slice has zero, one, two or four points. Subtraction from an anchor row value and cancellation of M identify membership with the homogeneous binary equations. The mixed geometric identity then applies. Reducing integer lift coordinates modulo two and using Euclidean division proves both global equivalences. This direct congruence formulation makes no assertion about a projected lattice basis.

## References

- Truth anchor: `D5/S3/Arith/Covering/MixedAffineQuotient.ProjectedCriterion`
- Truth anchor: `D5/S3/Arith/Covering/MixedAffineQuotient.Witness`
- Truth anchor: `D5/S3/Arith/Covering/MixedAffineQuotient.carry`
- Truth anchor: `D5/S3/Arith/Covering/MixedAffineQuotient.result`
- Dependency: [D5/S3/Arith/Covering/BinaryAffineGeometry](BinaryAffineGeometry.md)
