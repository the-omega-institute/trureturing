# Chronological dynamics of actual outgoing lifts

## Abstract

Actual path reversal transports chronological outgoing observations.

**Definition 1.1 (Reverse each actual outgoing edge).**

Lean statement: `D5/S3/ConceptDynamics/Coding/ResponseGraphs/ActualOutgoingDynamics.rhoLift`

*Formalization.* `D5/S3/ConceptDynamics/Coding/ResponseGraphs/ActualOutgoingDynamics.rhoLift` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any natural n, matrix A : CountMat n n, type Q, onto p : Q → Fin n and maps rho_b from the source fiber of every actual numbered A-edge b to its target fiber, rhoLift p hp rho is an incoming lift of A.transpose. Its projection is the original p. The reversed edge with endpoints b.target,b.source retains b.number and acts by the original rho_b. No finiteness, essentiality or forgetting is assumed.

**Theorem 1.2 (Appending one edge composes actual lifts).**

Lean statement: `D5/S3/ConceptDynamics/Coding/ResponseGraphs/ActualOutgoingDynamics.lift_append`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResponseGraphs/ActualOutgoingDynamics.lift_append` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every incoming lift L, endpoint-indexed path alpha from i to j, actual edge a from j to k and terminal state v above k, lifting appendPath alpha a at v equals lifting alpha at the lifted value of a. This directly reuses concatenate_paths and the original numbered-word injectivity and append-word suppliers; there is no second path-concatenation proof.

**Definition 1.3 (Chronological outgoing path evaluation).**

Lean statement: `D5/S3/ConceptDynamics/Coding/ResponseGraphs/ActualOutgoingDynamics.rhoPath`

*Formalization.* `D5/S3/ConceptDynamics/Coding/ResponseGraphs/ActualOutgoingDynamics.rhoPath` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For the original outgoing data p,hp,rho on A, rhoPath evaluates the empty path by identity. For a first actual edge b followed by a tail, it applies rho_b to the initial state and then evaluates the tail. Consequently a chronological path b1…bd acts by rho_bd composed through rho_b1 on its entire source fiber, with every edge number and both endpoints retained.

**Theorem 1.4 (Reversal computes the original chronological path).**

Lean statement: `D5/S3/ConceptDynamics/Coding/ResponseGraphs/ActualOutgoingDynamics.chronological_rho`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResponseGraphs/ActualOutgoingDynamics.chronological_rho` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original outgoing datum p,hp,rho, natural length d, endpoint-indexed path beta in A from i to j, and state u above i, (rhoLift p hp rho).liftPath (reverseFinitePath beta) u equals rhoPath p hp rho beta u as elements of the original terminal fiber above j. The path induction uses lift_append, so the reversal includes the order of all edges as well as their directions.

**Theorem 1.5 (Reversing an actual finite path twice recovers it).**

Lean statement: `D5/S3/ConceptDynamics/Coding/ResponseGraphs/ActualOutgoingDynamics.reverse_reverse`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResponseGraphs/ActualOutgoingDynamics.reverse_reverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any matrix A, natural d and endpoint-indexed actual path alpha : FinitePath A d i j, reverseFinitePath (reverseFinitePath alpha) equals alpha. The proof reuses reverse_word, the original word_endpoint_injective and the involution of numbered edge reversal. Empty paths are included.

**Theorem 1.6 (Responses are the original chronological observations).**

Lean statement: `D5/S3/ConceptDynamics/Coding/ResponseGraphs/ActualOutgoingDynamics.rho_response_paths`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResponseGraphs/ActualOutgoingDynamics.rho_response_paths` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every p,hp,rho, natural d and states u,v, the d-response of rhoLift p hp rho holds exactly when p u = p v and every actual length-d path beta in the original graph A with that initial vertex gives equal rhoPath values at u and v. The two directions use chronological_rho and double reversal. Thus the response kernel is identified with the outgoing chronological observations on the same original graph, including d=0; a transpose matrix identity is not its premise.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResponseGraphs/ActualOutgoingDynamics.chronological_rho`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResponseGraphs/ActualOutgoingDynamics.lift_append`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResponseGraphs/ActualOutgoingDynamics.reverse_reverse`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResponseGraphs/ActualOutgoingDynamics.rhoLift`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResponseGraphs/ActualOutgoingDynamics.rhoPath`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResponseGraphs/ActualOutgoingDynamics.rho_response_paths`
- Dependency: [D5/S3/ConceptDynamics/Coding/IncomingLiftAmbiguityCriterion](../IncomingLiftAmbiguityCriterion.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/OriginalAlignedBalanced/FiniteWindowWordTransport](../OriginalAlignedBalanced/FiniteWindowWordTransport.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/ResponseGraphs/ActualQuotientDynamics](ActualQuotientDynamics.md)
