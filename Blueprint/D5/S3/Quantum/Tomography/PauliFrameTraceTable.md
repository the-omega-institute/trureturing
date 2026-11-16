# Pauli frames and Jordan generation

## Abstract

The same labelled Pauli overlap table has generated real Jordan carriers of dimensions ten and sixteen.

**Definition 1.1 (The labelled Pauli frame projectors).**

$$\forall (c: Bool), (\forall (i: \operatorname{Fin}(3)), (\forall (st: \operatorname{Prod}(\operatorname{Fin}(2), \operatorname{Fin}(2))), (\operatorname{frame}(c, i, st) = \operatorname{if}(\operatorname{Eq}(i, 0), \operatorname{E}(st), \operatorname{if}(\operatorname{Eq}(i, 1), \operatorname{F}(st), \operatorname{if}(c, \operatorname{Gr}(st), \operatorname{Gc}(st)))))))$$

*Formalization.* `D5/S3/Quantum/Tomography/PauliFrameTraceTable.frame` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The Boolean label selects the real third context G^r or the complex third context G^c. The first two contexts are the fixed E and F Pauli pairs, and each context is indexed by the two signs in Fin 2 × Fin 2. With s,t in {+1,-1}, their four projectors are E_st = (I4+s ZI+t IZ+st ZZ)/4, F_st = (I4+s XI+t IX+st XX)/4, G^r_st = (I4+s XZ+t ZX+st YY)/4, and G^c_st = (I4+s YI+t IY+st YY)/4. All scalar coefficients of generated carriers are real; the Jordan product is (AB+BA)/2.

**Theorem 1.2 (Both triples have the same twelve-by-twelve trace table).**

$$\forall (c: Bool), (\forall (i: \operatorname{Fin}(3)), (\forall (j: \operatorname{Fin}(3)), (\forall (st: \operatorname{Prod}(\operatorname{Fin}(2), \operatorname{Fin}(2))), (\forall (uv: \operatorname{Prod}(\operatorname{Fin}(2), \operatorname{Fin}(2))), (\operatorname{trace}(\operatorname{mul}(\operatorname{frame}(c, i, st), \operatorname{frame}(c, j, uv))) = \operatorname{if}(\operatorname{Eq}(i, j), \operatorname{if}(\operatorname{Eq}(st, uv), 1, 0), \frac{1}{4}))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/PauliFrameTraceTable.trace_table` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For either choice of the third context, equal context labels give the Kronecker delta on the two sign pairs, while distinct contexts have trace overlap 1/4. The proof expands the four Pauli terms and applies the frozen two-qubit Pauli trace orthogonality theorem.

**Theorem 1.3 (The real triple generates all real symmetric matrices).**

$$\operatorname{Eq}(\operatorname{generated}(\operatorname{frame}(true)), realCarrier)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/PauliFrameTraceTable.real_generated` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The carrier is the intersection of all real subspaces containing all twelve original projectors and closed under the matrix Jordan product. Signed sums recover XI, IX, ZI, and IZ. Their Jordan products supply XZ and ZX, whose product supplies YY. These ten Pauli words span every real symmetric matrix, and the original real projectors lie in that Jordan-closed carrier.

**Theorem 1.4 (The complex triple generates all Hermitian matrices).**

$$\operatorname{Eq}(\operatorname{generated}(\operatorname{frame}(false)), complexCarrier)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/PauliFrameTraceTable.complex_generated` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The signed sums of G^c additionally supply YI and IY. Multiplying commuting operators on the two tensor factors gives every two-qubit Pauli word. Pauli expansion with real coefficients then supplies every Hermitian matrix in the original common environment.

**Theorem 1.5 (The generated carriers have different real dimensions).**

$$\operatorname{And}(\operatorname{Eq}(\operatorname{finrank}(Real, \operatorname{generated}(\operatorname{frame}(true))), 10), \operatorname{Eq}(\operatorname{finrank}(Real, \operatorname{generated}(\operatorname{frame}(false))), 16))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/PauliFrameTraceTable.generated_dimensions` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The real carrier has one coordinate for each of the ten Pauli words containing an even number of Y factors. The full complex Hermitian carrier has real dimension sixteen.

**Theorem 1.6 (Every context is a complete rank-one projector frame).**

$$\forall (c: Bool), (\operatorname{Complete}(\operatorname{frame}(c)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/PauliFrameTraceTable.frame_complete` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each context consists of four Hermitian rank-one idempotents. Distinct sign pairs give orthogonal projectors and their sum is the identity. The rank follows from the trace of the corresponding idempotent linear operator.

**Definition 1.7 (Whole-table determination of Jordan dimension).**

$$\exists post \in \left(\operatorname{Fin}(3) \to \left(\operatorname{Fin}(3) \to \left(\operatorname{Prod}(\operatorname{Fin}(2), \operatorname{Fin}(2)) \to \left(\operatorname{Prod}(\operatorname{Fin}(2), \operatorname{Fin}(2)) \to Complex\right)\right)\right)\right) \to Nat,\; \forall (p: \operatorname{Fin}(3) \to \left(\operatorname{Prod}(\operatorname{Fin}(2), \operatorname{Fin}(2)) \to Op\right)), (\operatorname{Implies}(\operatorname{Complete}(p), \operatorname{Eq}(\operatorname{post}(\operatorname{table}(p)), \operatorname{finrank}(Real, \operatorname{generated}(p)))))$$

*Formalization.* `D5/S3/Quantum/Tomography/PauliFrameTraceTable.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The proposed postprocessor is any function from the entire labelled twelve-by-twelve complex overlap table to a natural number. It must recover the real dimension of the smallest Jordan-closed real carrier for every complete triple in the fixed H4(C) environment.

**Theorem 1.8 (No whole-table postprocessor recovers Jordan dimension).**

$$\operatorname{Not}(claim)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/PauliFrameTraceTable.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two original complete triples have the same whole labelled trace table, while their generated real carriers have dimensions ten and sixteen. Any function of that table would have to assign both values to one input. This compares two frame witnesses in the same Hermitian algebra; it makes no assertion about two complete physical models.

## References

- Truth anchor: `D5/S3/Quantum/Tomography/PauliFrameTraceTable.claim`
- Truth anchor: `D5/S3/Quantum/Tomography/PauliFrameTraceTable.complex_generated`
- Truth anchor: `D5/S3/Quantum/Tomography/PauliFrameTraceTable.frame`
- Truth anchor: `D5/S3/Quantum/Tomography/PauliFrameTraceTable.frame_complete`
- Truth anchor: `D5/S3/Quantum/Tomography/PauliFrameTraceTable.generated_dimensions`
- Truth anchor: `D5/S3/Quantum/Tomography/PauliFrameTraceTable.real_generated`
- Truth anchor: `D5/S3/Quantum/Tomography/PauliFrameTraceTable.result`
- Truth anchor: `D5/S3/Quantum/Tomography/PauliFrameTraceTable.trace_table`
- Dependency: [D5/S3/Quantum/Dynamics/ProjectionProbabilityFlow](../Dynamics/ProjectionProbabilityFlow.md)
- Dependency: [D5/S3/Quantum/Entanglement/BipartiteSectorDecomposition](../Entanglement/BipartiteSectorDecomposition.md)
- Dependency: [D5/S3/Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation](../Measurement/StabilizerPovmMaximalEntanglementRefutation.md)
