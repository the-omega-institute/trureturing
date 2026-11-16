# Centered tests and unitary transport

## Abstract

Center an AB density state at the product of its actual marginals. Hermitian contraction tests attain a maximum and control its trace norm. Coherent local B transport preserves the actual recovered residual and ordinary conditional mutual information.

**Theorem 1.1 (The four actual marginal entropies).**

Lean statement: `D5/S3/Quantum/Recovery/QubitCenteredTransport.qcmi_eq_four_marginals`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/QubitCenteredTransport.qcmi_eq_four_marginals` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Ordinary qcmi of the canonical state converted to MState equals the entropy of its actual AB marginal plus the entropy of its actual BC marginal minus the entropy of its actual B marginal and the entropy of the state itself.

**Theorem 1.2 (A product across A and BC).**

Lean statement: `D5/S3/Quantum/Recovery/QubitCenteredTransport.qcmi_product_left`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/QubitCenteredTransport.qcmi_product_left` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every density state a on A and every density state omega on B times C, the physical product a tensor omega has ordinary conditional mutual information zero. Product entropy additivity applies without a rank condition.

**Definition 1.3 (The centered AB correlation).**

Lean statement: `D5/S3/Quantum/Recovery/QubitCenteredTransport.centered`

*Formalization.* `D5/S3/Quantum/Recovery/QubitCenteredTransport.centered` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Subtract the product of the two actual marginals from the AB density matrix. Both partial traces of this centered matrix vanish.

**Definition 1.4 (Hermitian reference tests).**

Lean statement: `D5/S3/Quantum/Recovery/QubitCenteredTransport.sliceLinear`

*Formalization.* `D5/S3/Quantum/Recovery/QubitCenteredTransport.sliceLinear` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Pair each reference block with a complex-linear test on A. For Hermitian inputs and Hermitian tests the resulting B matrix is Hermitian.

**Theorem 1.5 (Both centered marginals vanish).**

Lean statement: `D5/S3/Quantum/Recovery/QubitCenteredTransport.centered_marginals_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/QubitCenteredTransport.centered_marginals_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Subtracting the product of the two actual marginals from a density matrix gives zero under both partial traces.

**Definition 1.6 (An outer-coordinate block).**

Lean statement: `D5/S3/Quantum/Recovery/QubitCenteredTransport.block`

*Formalization.* `D5/S3/Quantum/Recovery/QubitCenteredTransport.block` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Fixing the two inner coordinates of a bipartite matrix gives its matrix block on the outer coordinate.

**Definition 1.7 (The three Pauli directions).**

Lean statement: `D5/S3/Quantum/Recovery/QubitCenteredTransport.pauli`

*Formalization.* `D5/S3/Quantum/Recovery/QubitCenteredTransport.pauli` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The three Pauli matrices specify the traceless qubit directions used to reconstruct the centered correlation.

**Theorem 1.8 (Hermiticity of centered correlation).**

Lean statement: `D5/S3/Quantum/Recovery/QubitCenteredTransport.centered_hermitian`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/QubitCenteredTransport.centered_hermitian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A density matrix minus the product of its actual marginals is Hermitian.

**Theorem 1.9 (Trace norm of a tensor product).**

Lean statement: `D5/S3/Quantum/Recovery/QubitCenteredTransport.traceNorm_tensor`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/QubitCenteredTransport.traceNorm_tensor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The trace norm of a finite tensor product is the product of the two trace norms.

**Theorem 1.10 (An attained correlation maximum).**

Lean statement: `D5/S3/Quantum/Recovery/QubitCenteredTransport.attained_centered_traceNorm_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/QubitCenteredTransport.attained_centered_traceNorm_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The maximum operator norm of the centered slice over all Hermitian A contractions is attained. Pauli reconstruction and Hermitian trace duality bound the trace norm of the centered AB matrix by six times this maximum.

**Definition 1.11 (Tensor product of two unitaries).**

Lean statement: `D5/S3/Quantum/Recovery/QubitCenteredTransport.tensorUnitary`

*Formalization.* `D5/S3/Quantum/Recovery/QubitCenteredTransport.tensorUnitary` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The tensor product of two unitary matrices is unitary on the product coordinate type.

**Definition 1.12 (Unitary transport of a density state).**

Lean statement: `D5/S3/Quantum/Recovery/QubitCenteredTransport.conjugateState`

*Formalization.* `D5/S3/Quantum/Recovery/QubitCenteredTransport.conjugateState` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Conjugating a canonical density matrix by a unitary gives a density state on the same coordinate type.

**Definition 1.13 (Unitary conjugation as an algebra equivalence).**

Lean statement: `D5/S3/Quantum/Recovery/QubitCenteredTransport.conjugateAlg`

*Formalization.* `D5/S3/Quantum/Recovery/QubitCenteredTransport.conjugateAlg` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Unitary conjugation defines a complex star algebra equivalence of the full finite matrix algebra.

**Theorem 1.14 (Conjugation of each reference block).**

Lean statement: `D5/S3/Quantum/Recovery/QubitCenteredTransport.tensor_conjugate_block`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/QubitCenteredTransport.tensor_conjugate_block` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Conjugation on the second tensor factor acts by the same matrix conjugation on every block indexed by the first factor.

**Definition 1.15 (The coherently transported physical channel).**

Lean statement: `D5/S3/Quantum/Recovery/QubitCenteredTransport.localBChannel`

*Formalization.* `D5/S3/Quantum/Recovery/QubitCenteredTransport.localBChannel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Precompose the canonical recovery channel by the input unitary and postcompose by its inverse on the same output B coordinate. These are canonical completely positive trace preserving channels.

**Theorem 1.16 (Transport of the recovered reference).**

Lean statement: `D5/S3/Quantum/Recovery/QubitCenteredTransport.localBChannel_reference`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/QubitCenteredTransport.localBChannel_reference` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Transport the input and output B coordinates of the actual channel coherently. Recovering the transported AB state then equals local B transport of the original recovered reference state.

**Theorem 1.17 (Unitary invariance of half trace distance).**

Lean statement: `D5/S3/Quantum/Recovery/QubitCenteredTransport.traceDistance_conjugateState`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/QubitCenteredTransport.traceDistance_conjugateState` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Simultaneous unitary conjugation of two density states preserves their half trace distance.

**Definition 1.18 (The same state in a B coordinate).**

Lean statement: `D5/S3/Quantum/Recovery/QubitCenteredTransport.localBState`

*Formalization.* `D5/S3/Quantum/Recovery/QubitCenteredTransport.localBState` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Conjugate the original ABC density state by identity on A, the inverse unitary on B, and identity on C. The system and every rank are retained.

**Theorem 1.19 (The actual AB marginal after transport).**

Lean statement: `D5/S3/Quantum/Recovery/QubitCenteredTransport.localBState_AB`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/QubitCenteredTransport.localBState_AB` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual AB marginal of local B transport equals conjugation of the original AB marginal by the identity on A and the corresponding B unitary.

**Definition 1.20 (The linear recovered action on matrices).**

Lean statement: `D5/S3/Quantum/Recovery/QubitCenteredTransport.referenceRaw`

*Formalization.* `D5/S3/Quantum/Recovery/QubitCenteredTransport.referenceRaw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Apply the canonical channel to the B coordinate of each block of a bipartite matrix, retaining its A coordinate.

**Theorem 1.21 (Recovered states contract distance).**

Lean statement: `D5/S3/Quantum/Recovery/QubitCenteredTransport.referenceState_contract`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/QubitCenteredTransport.referenceState_contract` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Applying the same channel to the B coordinate of two density states does not increase their half trace distance.

**Theorem 1.22 (Recovery of a product input).**

Lean statement: `D5/S3/Quantum/Recovery/QubitCenteredTransport.referenceState_product`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/QubitCenteredTransport.referenceState_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Recovery of a product of an A state and a B state is the product of the A state and the channel output on B.

**Theorem 1.23 (Entries of finite matrix sums).**

Lean statement: `D5/S3/Quantum/Recovery/QubitCenteredTransport.cstar_sum_entry`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/QubitCenteredTransport.cstar_sum_entry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Evaluating an entry of a finite sum of CStar matrices gives the sum of the corresponding entries.

**Theorem 1.24 (Slices commute with subtraction).**

Lean statement: `D5/S3/Quantum/Recovery/QubitCenteredTransport.slice_sub`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/QubitCenteredTransport.slice_sub` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Testing the blocks of a difference of bipartite matrices gives the difference of the two tested slices.

**Theorem 1.25 (Testing commutes with recovery).**

Lean statement: `D5/S3/Quantum/Recovery/QubitCenteredTransport.slice_reference`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/QubitCenteredTransport.slice_reference` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Testing the A coordinate of a recovered matrix equals applying the channel to the tested input slice.

**Theorem 1.26 (Centered slices under B transport).**

Lean statement: `D5/S3/Quantum/Recovery/QubitCenteredTransport.slice_centered_conjugate`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/QubitCenteredTransport.slice_centered_conjugate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Conjugating the B coordinate of a density state conjugates every centered A-test slice by the same B unitary.

**Theorem 1.27 (Coherent transport of the physical recovery data).**

Lean statement: `D5/S3/Quantum/Recovery/QubitCenteredTransport.actual_B_unitary_transport`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/QubitCenteredTransport.actual_B_unitary_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the input unitary U, localBState conjugates rho by its inverse on B. The public conjunction identifies the actual AB marginal, its B marginal, the transported canonical channel and recovered reference state, and conjugation of every centered slice. The proof of ordinary qcmi invariance uses the actual AB, BC and B marginal entropy identities. Half trace distance is unchanged. Applying localBState with star U returns a repair and its qcmi and distance bounds to the original ABC carrier, including singular states.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/QubitCenteredTransport.actual_B_unitary_transport`
- Truth anchor: `D5/S3/Quantum/Recovery/QubitCenteredTransport.attained_centered_traceNorm_bound`
- Truth anchor: `D5/S3/Quantum/Recovery/QubitCenteredTransport.block`
- Truth anchor: `D5/S3/Quantum/Recovery/QubitCenteredTransport.centered`
- Truth anchor: `D5/S3/Quantum/Recovery/QubitCenteredTransport.centered_hermitian`
- Truth anchor: `D5/S3/Quantum/Recovery/QubitCenteredTransport.centered_marginals_zero`
- Truth anchor: `D5/S3/Quantum/Recovery/QubitCenteredTransport.conjugateAlg`
- Truth anchor: `D5/S3/Quantum/Recovery/QubitCenteredTransport.conjugateState`
- Truth anchor: `D5/S3/Quantum/Recovery/QubitCenteredTransport.cstar_sum_entry`
- Truth anchor: `D5/S3/Quantum/Recovery/QubitCenteredTransport.localBChannel`
- Truth anchor: `D5/S3/Quantum/Recovery/QubitCenteredTransport.localBChannel_reference`
- Truth anchor: `D5/S3/Quantum/Recovery/QubitCenteredTransport.localBState`
- Truth anchor: `D5/S3/Quantum/Recovery/QubitCenteredTransport.localBState_AB`
- Truth anchor: `D5/S3/Quantum/Recovery/QubitCenteredTransport.pauli`
- Truth anchor: `D5/S3/Quantum/Recovery/QubitCenteredTransport.qcmi_eq_four_marginals`
- Truth anchor: `D5/S3/Quantum/Recovery/QubitCenteredTransport.qcmi_product_left`
- Truth anchor: `D5/S3/Quantum/Recovery/QubitCenteredTransport.referenceRaw`
- Truth anchor: `D5/S3/Quantum/Recovery/QubitCenteredTransport.referenceState_contract`
- Truth anchor: `D5/S3/Quantum/Recovery/QubitCenteredTransport.referenceState_product`
- Truth anchor: `D5/S3/Quantum/Recovery/QubitCenteredTransport.sliceLinear`
- Truth anchor: `D5/S3/Quantum/Recovery/QubitCenteredTransport.slice_centered_conjugate`
- Truth anchor: `D5/S3/Quantum/Recovery/QubitCenteredTransport.slice_reference`
- Truth anchor: `D5/S3/Quantum/Recovery/QubitCenteredTransport.slice_sub`
- Truth anchor: `D5/S3/Quantum/Recovery/QubitCenteredTransport.tensorUnitary`
- Truth anchor: `D5/S3/Quantum/Recovery/QubitCenteredTransport.tensor_conjugate_block`
- Truth anchor: `D5/S3/Quantum/Recovery/QubitCenteredTransport.traceDistance_conjugateState`
- Truth anchor: `D5/S3/Quantum/Recovery/QubitCenteredTransport.traceNorm_tensor`
- Dependency: [D5/S3/Quantum/Recovery/QubitCoefficientGeometry](QubitCoefficientGeometry.md)
