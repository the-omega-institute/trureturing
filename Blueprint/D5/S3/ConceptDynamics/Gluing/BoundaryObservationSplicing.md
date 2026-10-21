# Boundary Observation Splicing

## Abstract

Compatible dependent raw records have a unique splice with the prescribed union assignment. Two complete-context replacements preserve a retained global output, and arbitrary summaries define a partial observation relation.

A node component A carries a dependent rawJoin record on the union of its local scopes. For disjoint components A and B, overlapScope is the complete variable carrier shared by their scopes. The left and right overlap boundaries are the restrictions of the two records to this same carrier. The splice assignment uses the left value on the left scope and the right value elsewhere; agreement on the overlap makes this independent of the branch.

**Definition 1.1 (Shared component scope).**

Lean statement: `D5/S3/ConceptDynamics/Gluing/BoundaryObservationSplicing.overlapScope`

*Formalization.* `D5/S3/ConceptDynamics/Gluing/BoundaryObservationSplicing.overlapScope` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The shared variable carrier is U_A intersect U_B.

**Definition 1.2 (Left overlap restriction).**

Lean statement: `D5/S3/ConceptDynamics/Gluing/BoundaryObservationSplicing.overlapBoundaryLeft`

*Formalization.* `D5/S3/ConceptDynamics/Gluing/BoundaryObservationSplicing.overlapBoundaryLeft` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A left record is restricted to U_A intersect U_B.

**Definition 1.3 (Right overlap restriction).**

Lean statement: `D5/S3/ConceptDynamics/Gluing/BoundaryObservationSplicing.overlapBoundaryRight`

*Formalization.* `D5/S3/ConceptDynamics/Gluing/BoundaryObservationSplicing.overlapBoundaryRight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A right record is restricted to U_A intersect U_B.

**Definition 1.4 (Pointwise partial splice).**

Lean statement: `D5/S3/ConceptDynamics/Gluing/BoundaryObservationSplicing.spliceAssignment`

*Formalization.* `D5/S3/ConceptDynamics/Gluing/BoundaryObservationSplicing.spliceAssignment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For x in U_{A union B}, use a(x) when x is in U_A and b(x) otherwise. The latter branch is defined because every x in U_{A union B} lies in U_A or U_B.

**Theorem 1.5 (Unique compatible raw join).**

Lean statement: `D5/S3/ConceptDynamics/Gluing/BoundaryObservationSplicing.compatible_splice_unique`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Gluing/BoundaryObservationSplicing.compatible_splice_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For disjoint A and B, if the two complete overlap restrictions agree, the pointwise splice is a rawJoin record on A union B and is the unique rawJoin record with that value function. Empty local scopes and empty local relations remain allowed; the theorem is conditional on the displayed compatible pair.

**Theorem 1.6 (Two complete-context substitutions).**

Lean statement: `D5/S3/ConceptDynamics/Gluing/BoundaryObservationSplicing.two_context_output_eq`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Gluing/BoundaryObservationSplicing.two_context_output_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let A and B be disjoint. Suppose each local summary retains its full boundary and every specified output G against every complete compatible complement. Two global raw records with equal A summaries, equal B summaries, and identical restrictions outside A union B have the same G output. First replace the A record while keeping its complete complement. The intermediate record keeps B unchanged; on the complement of B it agrees with the final record, by combining its A restriction with the common outside restriction. The B replacement then gives the second output equality. BoundaryOutputRetention is an explicit hypothesis; it is not inferred here for arbitrary summaries.

**Definition 1.7 (Partial observation graph).**

Lean statement: `D5/S3/ConceptDynamics/Gluing/BoundaryObservationSplicing.spliceGraph`

*Formalization.* `D5/S3/ConceptDynamics/Gluing/BoundaryObservationSplicing.spliceGraph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The graph contains ((q_A(a),q_B(b)),q_C(a union b)) exactly for pairs whose complete overlap restrictions agree. Its domain is therefore a partial domain of summary pairs.

For local summaries q_A and q_B, assume equality of summaries preserves the corresponding complete overlap restriction. If a and b initially agree on the overlap, and q_A(a)=q_A(a') and q_B(b)=q_B(b'), symmetry and transitivity of equality give agreement of a' and b'. This conditional observation uses the overlap-retention assumptions; it does not derive them from observational equivalence or prove that the two union summaries agree.

The relation above does not assert a well-defined operation on observation quotients. That additionally requires preservation of the full union boundary and a bridge from the specified observation equivalence to the retention hypotheses. Its image is not identified here with every union observation. Restriction and reconstruction of arbitrary union records, finite contraction with independence of order, the unique empty root context, and the descended root map preserving the complete joint output image remain unproved here.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Gluing/BoundaryObservationSplicing.compatible_splice_unique`
- Truth anchor: `D5/S3/ConceptDynamics/Gluing/BoundaryObservationSplicing.overlapBoundaryLeft`
- Truth anchor: `D5/S3/ConceptDynamics/Gluing/BoundaryObservationSplicing.overlapBoundaryRight`
- Truth anchor: `D5/S3/ConceptDynamics/Gluing/BoundaryObservationSplicing.overlapScope`
- Truth anchor: `D5/S3/ConceptDynamics/Gluing/BoundaryObservationSplicing.spliceAssignment`
- Truth anchor: `D5/S3/ConceptDynamics/Gluing/BoundaryObservationSplicing.spliceGraph`
- Truth anchor: `D5/S3/ConceptDynamics/Gluing/BoundaryObservationSplicing.two_context_output_eq`
- Dependency: [D5/S3/ConceptDynamics/Gluing/RunningIntersectionRecords](RunningIntersectionRecords.md)
