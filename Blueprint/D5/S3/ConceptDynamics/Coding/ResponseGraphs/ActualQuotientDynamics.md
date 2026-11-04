# Dynamics of actual response quotients

## Abstract

Actual response quotients preserve the base graph and add response depths.

Let n be a natural number, A a natural n by n matrix, Q any type, and L an IncomingLift A Q. Thus L.project is onto Fin n and each actual numbered A-edge a has a lift from its terminal state fiber to its initial state fiber. Write E(d) for L.response d, whose readout includes the projection and the value of every actual length-d path lift. No finiteness of Q, essentiality or finite forgetting is assumed below.

**Definition 1.1 (Projection of response classes).**

Lean statement: `D5/S3/ConceptDynamics/Coding/ResponseGraphs/ActualQuotientDynamics.projection`

*Formalization.* `D5/S3/ConceptDynamics/Coding/ResponseGraphs/ActualQuotientDynamics.projection` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural d, projection L d maps Quotient (L.response d) to Fin n by sending the class of u to L.project u. Equality of response readouts includes equality of their projected vertices, so this is well defined.

**Theorem 1.2 (A representative has the class projection).**

Lean statement: `D5/S3/ConceptDynamics/Coding/ResponseGraphs/ActualQuotientDynamics.projection_out`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResponseGraphs/ActualQuotientDynamics.projection_out` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every L, d and class F, L.project (Quotient.out F) equals projection L d F. This identity supplies the terminal-fiber condition in the quotient lift.

**Definition 1.3 (The lift on the same base graph).**

Lean statement: `D5/S3/ConceptDynamics/Coding/ResponseGraphs/ActualQuotientDynamics.quotientLift`

*Formalization.* `D5/S3/ConceptDynamics/Coding/ResponseGraphs/ActualQuotientDynamics.quotientLift` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every L and natural d, quotientLift L d is an IncomingLift A (Quotient (L.response d)). Its projection is projection L d and remains onto. For a numbered edge a and a class F projected to a.target, lift a F is the class of the original lift of a at Quotient.out F. The original lift's source-fiber law gives the required projection to a.source. The following representative formula establishes that the resulting class is independent of that choice.

**Theorem 1.4 (Each numbered edge acts on representatives).**

Lean statement: `D5/S3/ConceptDynamics/Coding/ResponseGraphs/ActualQuotientDynamics.lift_mk`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResponseGraphs/ActualQuotientDynamics.lift_mk` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every L, natural d, actual edge a, state u and proof hu of L.project u = a.target, the underlying class of (quotientLift L d).lift a applied to the class of u is the class modulo L.response d of (L.lift a (u,hu)).val. Response monotonicity followed by incoming_response_step gives the needed representative independence. Edge numbers are retained unchanged.

**Theorem 1.5 (Every quotient response is the shifted original response).**

Lean statement: `D5/S3/ConceptDynamics/Coding/ResponseGraphs/ActualQuotientDynamics.response_shift`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResponseGraphs/ActualQuotientDynamics.response_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every L, natural depths d and j, and states u and v, (quotientLift L d).response j on the classes of u and v holds if and only if L.response (d+j) u v. At j = 0, the quotient response is equality of classes, exactly E(d). For the successor step, response_successor_iff compares the common projections and the preceding responses after every actual incoming edge. The representative lift formula and the induction hypothesis identify those responses with the original responses at depth d+j.

Taking d = 1 identifies the actual first-response quotient at every subsequent response depth. This statement is about the constructed incoming lift and its actual paths; equality of aggregate adjacency columns is not used as a substitute for the response relation. It supplies the dynamics needed for forgetting-depth consequences. The separate response-counting and matrix-chain results describe their own matrix and finiteness assumptions.

**Theorem 1.6 (Actual path values under a state equivalence).**

Lean statement: `D5/S3/ConceptDynamics/Coding/ResponseGraphs/ActualQuotientDynamics.path_conjugacy`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResponseGraphs/ActualQuotientDynamics.path_conjugacy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let L : IncomingLift A Q and K : IncomingLift A R have the same actual numbered base graph A. Let e : Q ≃ R preserve the projections and satisfy K.lift a (e u) = e (L.lift a u) for every actual compatible edge a and state u, with the dependent fiber proofs retained. For every natural length, every endpoint-indexed path alpha and every terminal state u, K.liftPath alpha (e u) equals e (L.liftPath alpha u). Induction on the path uses the given single-edge equality on the lifted tail. No finiteness, essentiality or forgetting hypothesis is used.

**Theorem 1.7 (All response depths under the same equivalence).**

Lean statement: `D5/S3/ConceptDynamics/Coding/ResponseGraphs/ActualQuotientDynamics.response_conjugacy`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResponseGraphs/ActualQuotientDynamics.response_conjugacy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under exactly the projection and single-edge hypotheses of path_conjugacy, for every natural d and states u,v, K.response d (e u) (e v) if and only if L.response d u v. At zero this is injectivity of e; at a successor the actual response recursion and the computed edge conjugacy transport each preceding response. The all-depth response conclusion is derived, not supplied as a premise.

**Definition 1.8 (The recursively constructed first quotients).**

Lean statement: `D5/S3/ConceptDynamics/Coding/ResponseGraphs/ActualQuotientDynamics.iteration`

*Formalization.* `D5/S3/ConceptDynamics/Coding/ResponseGraphs/ActualQuotientDynamics.iteration` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any IncomingLift A Q, iteration L 0 is the original pair Q,L. The successor of a stage K is the pair Quotient (K.response 1), quotientLift K 1. Thus each stage is the actual first-response quotient on the same base A, with no finiteness or forgetting assumption in the construction.

**Definition 1.9 (The cumulative map from original states).**

Lean statement: `D5/S3/ConceptDynamics/Coding/ResponseGraphs/ActualQuotientDynamics.iterMap`

*Formalization.* `D5/S3/ConceptDynamics/Coding/ResponseGraphs/ActualQuotientDynamics.iterMap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural k, iterMap L k sends Q to the state set of iteration L k. At zero it is identity; at a successor it takes the actual first-response class of the preceding image.

**Theorem 1.10 (Each actual stage is reached from original states).**

Lean statement: `D5/S3/ConceptDynamics/Coding/ResponseGraphs/ActualQuotientDynamics.iter_onto`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResponseGraphs/ActualQuotientDynamics.iter_onto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every L and natural k, iterMap L k is surjective. The induction chooses a representative of a successor quotient class and applies the preceding surjectivity witness. This covers the zero stage and arbitrary state types.

**Theorem 1.11 (Iteration retains the original base vertex).**

Lean statement: `D5/S3/ConceptDynamics/Coding/ResponseGraphs/ActualQuotientDynamics.iter_project`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResponseGraphs/ActualQuotientDynamics.iter_project` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every L, natural k and original state u, the projection of iterMap L k u under iteration L k is L.project u. The recursive quotient construction keeps the original base graph and its vertex projection at every stage.

**Theorem 1.12 (Iteration retains actual edge lifts).**

Lean statement: `D5/S3/ConceptDynamics/Coding/ResponseGraphs/ActualQuotientDynamics.iter_lift`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResponseGraphs/ActualQuotientDynamics.iter_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every L, natural k, actual numbered edge a, original u and proof that u projects to a.target, lifting a from iterMap L k u in iteration L k gives iterMap L k of the original lift of a from u. The proof inducts over actual quotient rounds and uses the representative formula at each successor.

**Theorem 1.13 (Recursive rounds agree with the original response stages).**

Lean statement: `D5/S3/ConceptDynamics/Coding/ResponseGraphs/ActualQuotientDynamics.iter_response`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResponseGraphs/ActualQuotientDynamics.iter_response` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every L, natural k and j, and original states u,v, the j-response in iteration L k on iterMap L k u and iterMap L k v is equivalent to L.response (k+j) u v. The proof inducts on quotient rounds and uses response_shift at each successor. This identifies the produced actual chain with the original response stages, including k=0 and j=0. It does not assert a minimum matrix SSE distance over arbitrary chains.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResponseGraphs/ActualQuotientDynamics.iterMap`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResponseGraphs/ActualQuotientDynamics.iter_lift`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResponseGraphs/ActualQuotientDynamics.iter_onto`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResponseGraphs/ActualQuotientDynamics.iter_project`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResponseGraphs/ActualQuotientDynamics.iter_response`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResponseGraphs/ActualQuotientDynamics.iteration`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResponseGraphs/ActualQuotientDynamics.lift_mk`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResponseGraphs/ActualQuotientDynamics.path_conjugacy`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResponseGraphs/ActualQuotientDynamics.projection`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResponseGraphs/ActualQuotientDynamics.projection_out`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResponseGraphs/ActualQuotientDynamics.quotientLift`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResponseGraphs/ActualQuotientDynamics.response_conjugacy`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResponseGraphs/ActualQuotientDynamics.response_shift`
- Dependency: [D5/S3/ConceptDynamics/Coding/ResponseKernelRecursion](../ResponseKernelRecursion.md)
