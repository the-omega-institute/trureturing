# Actual finite graph words give chronological rectangular RS paths and exact scalar-extended endpoint maps

## Abstract

Actual finite graph words give chronological rectangular RS paths and exact scalar-extended endpoint maps.

This dictionary changes representations while preserving the full endpoint map. It works over GyrationDyadic using rectangular ROW factors; the full integer history and the independently constructed beam action remain the objects to be compared downstream.

ActualWordRelabelAssembly supplies dictionary_residue, which word_rebased uses to connect the matrix-path weight to the actual periodic action.

**Theorem 1.1 (Adjacency intertwining from the actual edge bijection).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualWordMatrixPath.relabel_time`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualWordMatrixPath.relabel_time` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For finite vertex types V,W and finite edge types E,J with the stated vertex equality decisions, Relabel G H retains both vertex and edge bijections. relabel_adjacency is obtained from the existing edge-count transport. reindex r.vertex sends a vertex coefficient z to z composed with r.vertex inverse. relabel_time derives its intertwining with the adjacency time maps by reindexing the full vertex sum. No adjacency conjugacy is postulated and parallel-edge identities are retained.

**Definition 1.2 (Rectangular RS factors in chronological row order).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualWordMatrixPath.positiveEdge`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualWordMatrixPath.positiveEdge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For R : CountMat n m and S : CountMat m n, counts extends coefficients to GyrationDyadic and counts_mul preserves multiplication. positiveEdge goes from countedBased(R*S) to countedBased(S*R), with forward map (counts R).toLinearMapRight' and backward map (counts S).toLinearMapRight'. Thus s.comp r is old time and r.comp s is new time. The conventional COLUMN matrix of the forward map is transpose R; its ROW matrix is R. rows(g.comp f)=rows(f)*rows(g), so row factors multiply in chronological order. All zero ranks, zero entries and singular intermediates are allowed.

**Theorem 1.3 (Use precisely the existing history chart basis).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualWordMatrixPath.vertex_matrix`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualWordMatrixPath.vertex_matrix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

presentationBasis F is Pi.basisFun transported by reindex of the vertex bijection of ActualPositiveWordPeriodicCochain.chart F. vertex F stores the actual graph adjacency time in that basis. vertex_matrix derives its ROW matrix as counts of ActualPositiveWordPeriodicCochain.matrix F from relabel_time and faithful rows_transport. It does not assert equality with a fixed signed COLUMN matrix used in the arithmetic character.

**Theorem 1.4 (Every actual positive word has its original endpoint map).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualWordMatrixPath.dictionary_forward`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualWordMatrixPath.dictionary_forward` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

dictionary maps a relabel leaf to one RS edge and a positive leaf to three: relabelEdge old.symm, positiveEdge R S, relabelEdge next. length counts these RS edges, not Word.letters. Composition appends paths over the identical intermediate Based object. Path.append_forward derives forward(v after u)=v.forward.comp u.forward, and dictionary_forward identifies the full path map with endpointMap w. For a positive leaf this is next reindex composed with R acting on old inverse coefficients; both graph chart arrows remain.

**Theorem 1.5 (Compare the actual integer and dyadic maps before colimits).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualWordMatrixPath.endpointMap_cast`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualWordMatrixPath.endpointMap_cast` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary Word F H and every integer vertex coefficient function z : F.V to integers, scalar extension of PositiveWordBeamTransport.endpointMap w z equals endpointMap w applied to the same coefficientwise embedded z, at every actual vertex of H. Induction uses the literal positive factors and constructor order. The preserved original application applies this equality at actual integer basis vectors to identify the finite coefficient matrix of the native endpoint action. It does not infer equality from an injective colimit or from a finite-period action.

The matrix-coordinate identities keep the row convention explicit: the actual endpoint linear map is expressed in the chosen vertex bases before it is compared with periodic weights.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualWordMatrixPath.dictionary_forward`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualWordMatrixPath.endpointMap_cast`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualWordMatrixPath.positiveEdge`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualWordMatrixPath.relabel_time`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualWordMatrixPath.vertex_matrix`
- Dependency: [D5/S3/ConceptDynamics/Coding/BeamColimits/PositiveWordBeamTransport](../BeamColimits/PositiveWordBeamTransport.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/FiniteKernelLadder](../FiniteKernelLadder.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualPositiveWordPeriodicCochain](ActualPositiveWordPeriodicCochain.md)
