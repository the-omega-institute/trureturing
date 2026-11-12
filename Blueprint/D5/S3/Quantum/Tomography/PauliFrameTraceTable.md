# Pauli frame trace table

## Abstract

The two labelled Pauli frames have the same finite trace table, with a non-real complex-frame witness.

**Definition 1.1 (The labelled Pauli frame projectors).**

$$\forall (c: Bool), (\forall (i: \operatorname{Fin}(3)), (\forall (st: \operatorname{Prod}(\operatorname{Fin}(2), \operatorname{Fin}(2))), (\operatorname{frame}(c, i, st) = \operatorname{if}(\operatorname{Eq}(i, 0), \operatorname{E}(st), \operatorname{if}(\operatorname{Eq}(i, 1), \operatorname{F}(st), \operatorname{if}(c, \operatorname{Gr}(st), \operatorname{Gc}(st)))))))$$

*Formalization.* `D5/S3/Quantum/Tomography/PauliFrameTraceTable.frame` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The Boolean label selects the real third context G^r or the complex third context G^c. The first two contexts are the fixed E and F Pauli pairs, and each context is indexed by the two signs in Fin 2 × Fin 2.

**Theorem 1.2 (Both frames have the same twelve-entry trace table).**

$$\forall (c: Bool), (\forall (i: \operatorname{Fin}(3)), (\forall (j: \operatorname{Fin}(3)), (\forall (st: \operatorname{Prod}(\operatorname{Fin}(2), \operatorname{Fin}(2))), (\forall (uv: \operatorname{Prod}(\operatorname{Fin}(2), \operatorname{Fin}(2))), (\operatorname{trace}(\operatorname{mul}(\operatorname{frame}(c, i, st), \operatorname{frame}(c, j, uv))) = \operatorname{if}(\operatorname{Eq}(i, j), \operatorname{if}(\operatorname{Eq}(st, uv), 1, 0), \frac{1}{4}))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/PauliFrameTraceTable.trace_table` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For either choice of the third context, equal context labels give the Kronecker delta on the two sign pairs, while distinct contexts have trace overlap 1/4. The proof expands the four Pauli terms and applies the frozen two-qubit Pauli trace orthogonality theorem.

**Theorem 1.3 (The complex frame has a non-real matrix entry).**

$$\exists x \in \operatorname{Fin}(2) \to \operatorname{Fin}(2),\; \exists y \in \operatorname{Fin}(2) \to \operatorname{Fin}(2),\; \operatorname{im}(\operatorname{apply}(\operatorname{apply}(\operatorname{wordOp}(\operatorname{yI}()), x), y)) \ne 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/PauliFrameTraceTable.complex_frame_nonreal_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Y ⊗ I Pauli word has an explicitly computed entry with nonzero imaginary part. This is a finite separation witness for the complex frame; the full Jordan-closure dimension claims remain outside this module.

## References

- Truth anchor: `D5/S3/Quantum/Tomography/PauliFrameTraceTable.complex_frame_nonreal_witness`
- Truth anchor: `D5/S3/Quantum/Tomography/PauliFrameTraceTable.frame`
- Truth anchor: `D5/S3/Quantum/Tomography/PauliFrameTraceTable.trace_table`
- Dependency: [D5/S3/Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation](../Measurement/StabilizerPovmMaximalEntanglementRefutation.md)
