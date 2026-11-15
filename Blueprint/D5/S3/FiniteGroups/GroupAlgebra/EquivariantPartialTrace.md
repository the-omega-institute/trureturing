# Equivariant partial trace without dimension division

## Abstract

Partial trace preserves equivariance and transports trace-zero pairings through an actual tensor product over an arbitrary field.

Let K be any field, G any group, and A, B, C K-vector spaces in independent universes. The linear construction requires A and C finite-dimensional; B is also finite-dimensional in the trace-pairing statements. The right partial trace contracts the C-endomorphism factor in Hom(A tensor C, B tensor C) using its ordinary trace. It is not divided by dim C, so positive characteristic and dimensions vanishing in K are retained.

**Theorem 1.1 (Contract a pure tensor map).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/EquivariantPartialTrace.rightPartialTrace_map`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/EquivariantPartialTrace.rightPartialTrace_map` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For f:A->B and t:C->C, the contraction of f tensor t is trace(t) times f. The implementation uses the actual hom-tensor-hom linear equivalence and the usual linear trace.

**Theorem 1.2 (Transfer the trace pairing).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/EquivariantPartialTrace.trace_comp_map_eq_trace_rightPartialTrace`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/EquivariantPartialTrace.trace_comp_map_eq_trace_rightPartialTrace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For F:A tensor C->B tensor C and d:B->A, trace on B tensor C of F composed with d tensor id_C equals trace on B of the right partial trace of F composed with d. The proof expands the actual tensor of hom spaces and uses the tensor-product trace identity.

**Theorem 1.3 (Move the outer maps through the contraction).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/EquivariantPartialTrace.rightPartialTrace_conjugate`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/EquivariantPartialTrace.rightPartialTrace_conjugate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If c' composed with c is id_C, contracting (b tensor c) composed with F composed with (a tensor c') gives b composed with the contraction of F composed with a. Cyclicity of trace removes the C-maps. Applied to a group element and its inverse, this identity proves that the partial trace of an intertwiner is itself an intertwiner; equivariance is derived rather than assumed.

**Theorem 1.4 (Tensor a map with vanishing trace pairings).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/EquivariantPartialTrace.trace_pairing_zero_rTensor`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/EquivariantPartialTrace.trace_pairing_zero_rTensor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose d:A->B is equivariant and trace(g composed with d)=0 for every equivariant g:B->A. Then, for every equivariant F:B tensor C->A tensor C, trace(F composed with d tensor id_C)=0. Contracting F provides the required equivariant return map. This is the bridge used when the first binary obstruction occurs inside a triple tensor.

The general mechanism is classical: negligible morphisms form a tensor ideal, as in Pavel Etingof and Victor Ostrik, On semisimplification of tensor categories, arXiv:1801.04409, Lemma 2.3, PDF page 4. The concrete Lean proof here constructs the contraction and its equivariance. The same paper, PDF page 6, distinguishes negligible morphisms from maps factoring through negligible objects. Accordingly, vanishing trace pairings are used only for an obstruction; they do not replace the original M-relative factorization ideal in the Elmer--Kadr applications. No novelty claim is made for the partial-trace mechanism.

## References

- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/EquivariantPartialTrace.rightPartialTrace_conjugate`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/EquivariantPartialTrace.rightPartialTrace_map`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/EquivariantPartialTrace.trace_comp_map_eq_trace_rightPartialTrace`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/EquivariantPartialTrace.trace_pairing_zero_rTensor`
