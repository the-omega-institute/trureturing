# Counted-edge ray images and intrinsic endpoint multiplicities

## Abstract

Literal counted-edge images and intrinsic endpoint multiplicities at every integer cut.

Let R : CountMat n m and S : CountMat m n. An Edge M contains its source, target and a number in Fin (M source target). countedGraph is exactly the DirectedMultigraph adapter on these edges, so its histories are the existing Path M. integerCounts only casts Nat coefficients to Int. adjacency_counted counts each edge number once; repeated targets do not collapse parallel edges. All endpoint vectors are ROW vectors, and rectangular transport is z vecMul integerCounts R.

The elementary RS-to-SR coding splits x(t)=(r_t,s_t) and outputs (s_t,r_(t+1)). Its inverse uses the preceding output at t-1 and the current output at t. Consequently the opposite forward coding composed after the first coding is x(t+1). The established forward-time convention is preserved: translate a x evaluated at t is x(t+a); writing the forward offset as -k does not reverse the coding.

A ray at signed cut N fixes every edge k <= N and has endpoint target(alpha N). Its literal elementary image is a finite disjoint union of rays at the SAME cut N, indexed by the numbered R edges leaving that endpoint. targetCenter uses target essentiality only to extend the selected legal past to a full target history. Distinct edge numbers make distinct pasts even if endpoints coincide. Thus the image endpoint row is e_endpoint R, with each multiplicity intact. Empty outgoing fibers are never replaced by a nonempty surrogate; a supplied full path may itself rule out a particular empty fiber.

image_atCut and endpointRow_image extend that calculation to every actual finite intrinsic partition, including empty beams. These are the geometric inputs consumed by CountedMatrixBeamColimit and PositiveWordBeamTransport. The original native h is not assumed to preserve cross-graph coordinates: those coordinates are derived here from actual subsets before the existing same-graph group representation is invoked. This narrative records a repository derivation and its application, without a claim of literature novelty.

**Definition 1.1 (Use the literal counted-edge graph on Fin n and Edge M.).**

Lean statement: `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamDiagram.countedGraph`

*Formalization.* `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamDiagram.countedGraph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Use the literal counted-edge graph on Fin n and Edge M.

**Definition 1.2 (Cast every natural edge multiplicity to an integer coefficient.).**

Lean statement: `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamDiagram.integerCounts`

*Formalization.* `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamDiagram.integerCounts` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Cast every natural edge multiplicity to an integer coefficient.

**Theorem 1.3 (Coefficient casting commutes with rectangular matrix multiplication.).**

Lean statement: `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamDiagram.integerCounts_mul`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamDiagram.integerCounts_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Coefficient casting commutes with rectangular matrix multiplication.

**Definition 1.4 (Keep the entire numbered outgoing R fiber at u, with empty fibers allowed.).**

Lean statement: `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamDiagram.NextR`

*Formalization.* `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamDiagram.NextR` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Keep the entire numbered outgoing R fiber at u, with empty fibers allowed.

**Theorem 1.5 (Count each original parallel edge exactly once in the intrinsic adjacency row.).**

Lean statement: `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamDiagram.adjacency_counted`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamDiagram.adjacency_counted` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Count each original parallel edge exactly once in the intrinsic adjacency row.

**Theorem 1.6 (At output time t retain s_t and the next r_(t+1), including both edge numbers.).**

Lean statement: `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamDiagram.elementary_split`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamDiagram.elementary_split` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At output time t retain s_t and the next r_(t+1), including both edge numbers.

**Theorem 1.7 (The inverse uses the second half at t-1 and the first half at t.).**

Lean statement: `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamDiagram.elementary_symm_split`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamDiagram.elementary_symm_split` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The inverse uses the second half at t-1 and the first half at t.

**Definition 1.8 (Append the chosen numbered R edge after the prescribed target past using target essentiality.).**

Lean statement: `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamDiagram.targetCenter`

*Formalization.* `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamDiagram.targetCenter` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Append the chosen numbered R edge after the prescribed target past using target essentiality.

**Theorem 1.9 (The target center ends at the target of that chosen numbered R edge.).**

Lean statement: `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamDiagram.targetCenter_endpoint`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamDiagram.targetCenter_endpoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The target center ends at the target of that chosen numbered R edge.

**Theorem 1.10 (Identify the literal same-cut image as the union indexed by all numbered outgoing R edges.).**

Lean statement: `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamDiagram.image_ray`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamDiagram.image_ray` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Identify the literal same-cut image as the union indexed by all numbered outgoing R edges.

**Theorem 1.11 (Different R edge numbers give disjoint target rays even when their endpoints agree.).**

Lean statement: `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamDiagram.image_ray_disjoint`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamDiagram.image_ray_disjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Different R edge numbers give disjoint target rays even when their endpoints agree.

**Theorem 1.12 (Obtain the finite intrinsic target partition of the actual ray image.).**

Lean statement: `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamDiagram.image_ray_atCut`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamDiagram.image_ray_atCut` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Obtain the finite intrinsic target partition of the actual ray image.

**Theorem 1.13 (The actual ray image has right-row multiplicity e_endpoint R at the original signed cut.).**

Lean statement: `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamDiagram.endpointRow_image_ray`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamDiagram.endpointRow_image_ray` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual ray image has right-row multiplicity e_endpoint R at the original signed cut.

**Theorem 1.14 (Transport the whole intrinsic finite partition of an actual beam at its stated cut.).**

Lean statement: `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamDiagram.image_atCut`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamDiagram.image_atCut` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Transport the whole intrinsic finite partition of an actual beam at its stated cut.

**Definition 1.15 (Bundle the literal elementary Set.image with its proved finite beam partition.).**

Lean statement: `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamDiagram.elementaryImageBeam`

*Formalization.* `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamDiagram.elementaryImageBeam` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Bundle the literal elementary Set.image with its proved finite beam partition.

**Theorem 1.16 (Compute actual image endpoint multiplicities before passage to any row colimit.).**

Lean statement: `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamDiagram.endpointRow_image`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamDiagram.endpointRow_image` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Compute actual image endpoint multiplicities before passage to any row colimit.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamDiagram.NextR`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamDiagram.adjacency_counted`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamDiagram.countedGraph`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamDiagram.elementaryImageBeam`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamDiagram.elementary_split`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamDiagram.elementary_symm_split`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamDiagram.endpointRow_image`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamDiagram.endpointRow_image_ray`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamDiagram.image_atCut`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamDiagram.image_ray`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamDiagram.image_ray_atCut`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamDiagram.image_ray_disjoint`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamDiagram.integerCounts`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamDiagram.integerCounts_mul`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamDiagram.targetCenter`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamDiagram.targetCenter_endpoint`
- Dependency: [D5/S3/ConceptDynamics/Coding/CountedMatrixOverlap](../CountedMatrixOverlap.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/StandardBeamIdentification](../StandardBeamIdentification.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/StandardBeamPushforward](../StandardBeamPushforward.md)
