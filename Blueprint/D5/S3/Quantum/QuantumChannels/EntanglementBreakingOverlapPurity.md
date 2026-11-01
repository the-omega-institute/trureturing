# The overlap-to-purity part of Kopel's equality theorem

## Abstract

For a fixed rank-one Holevo representation with pure outputs, Kopel's affine overlap equation determines the mean-output purity and forces the nonconstant purity range.

**Definition 1.1 (Pure output projectors).**

Lean statement: `D5/S3/Quantum/QuantumChannels/EntanglementBreakingOverlapPurity.projector`

*Formalization.* `D5/S3/Quantum/QuantumChannels/EntanglementBreakingOverlapPurity.projector` (`✓ std3`).

*Citation.* E. Kopel (2026). *A sharp norm inequality for entanglement-breaking channels*. DOI: [10.48550/arXiv.2609.27906](https://doi.org/10.48550/arXiv.2609.27906). URL: <https://arxiv.org/abs/2609.27906v1>.

*Commentary.*

For a vector v in complex Euclidean d-space, projector v is the actual complex matrix with entries v_i times the conjugate of v_j. A unit vector gives a positive semidefinite matrix of trace one.

**Theorem 1.2 (Projector trace products are squared overlaps).**

$$\forall d \in \mathbb{N}, v \in EuclideanSpace\left(\mathbb{C}, Fin\left(d\right)\right), w \in EuclideanSpace\left(\mathbb{C}, Fin\left(d\right)\right),\; trace\left(projector\left(v\right) \cdot projector\left(w\right)\right) = ofReal\left(\left\lVert \langle v, w \rangle_{\mathbb{C}} \right\rVert^{2}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/EntanglementBreakingOverlapPurity.trace_projectors` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary complex Euclidean vectors v and w, the trace of the product of their outer projectors is the complex coercion of the squared norm of their inner product.

**Definition 1.3 (The mean of the prepared states).**

Lean statement: `D5/S3/Quantum/QuantumChannels/EntanglementBreakingOverlapPurity.meanOutput`

*Formalization.* `D5/S3/Quantum/QuantumChannels/EntanglementBreakingOverlapPurity.meanOutput` (`✓ std3`).

*Citation.* E. Kopel (2026). *A sharp norm inequality for entanglement-breaking channels*. DOI: [10.48550/arXiv.2609.27906](https://doi.org/10.48550/arXiv.2609.27906). URL: <https://arxiv.org/abs/2609.27906v1>.

*Commentary.*

For a fixed list of measurement weights alpha and unit output vectors psi, meanOutput is the sum of alpha divided by d times the output projectors. The main theorem proves that this matrix equals the image of I divided by d under the specified Holevo channel.

**Theorem 1.4 (Equation (7) determines the purity).**

Lean statement: `D5/S3/Quantum/QuantumChannels/EntanglementBreakingOverlapPurity.affine_overlap_purity_and_rigidity`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/EntanglementBreakingOverlapPurity.affine_overlap_purity_and_rigidity` (`✓ std3`). ∎

*Citation.* E. Kopel (2026). *A sharp norm inequality for entanglement-breaking channels*. DOI: [10.48550/arXiv.2609.27906](https://doi.org/10.48550/arXiv.2609.27906). URL: <https://arxiv.org/abs/2609.27906v1>.

*Commentary.*

Fix d at least two, a finite outcome type, strictly positive alpha, unit measurement and output vectors, a complete rank-one POVM, and the actual matrix-linear channel in that fixed Holevo representation. Assume the channel is not constant. If the off-diagonal squared overlaps obey equation (7) of Kopel's supplied v2 additions for an initially arbitrary real number P, then the mean output rho is positive semidefinite of trace one, equals Phi(I/d), every output expectation against rho equals P, and trace(rho squared) equals P. The theorem proves 1/d at most P and P strictly less than one. It also identifies every centered output-projector Hilbert-Schmidt pairing with (1-P) times (d times the corresponding squared measurement overlap minus one) divided by d-1.

The diagonal overlap identities extend the hypothesis from distinct pairs to all pairs. Taking the trace of POVM completeness gives the sum of alpha equal to d, and pairing completeness against each measurement direction gives the weighted measurement overlap sum equal to one. Summing equation (7) therefore forces the output expectations to be P. Averaging those expectations proves the purity identity. Positivity of the Hilbert-Schmidt square of rho-I/d gives the lower bound. If P were one, every centered output projector would have Hilbert-Schmidt norm zero, so all prepared states would equal rho and the fixed channel would be constant, contradicting the hypothesis.

This is the matrix-purity and centered-Gram portion of Theorem 5, under its rank-one and pure-output assumptions. It does not prove that equality in the nuclear norm inequality forces those assumptions, does not establish saturation from equation (7), and does not identify the nuclear and translation terms in the Bloch basis. Those obligations remain for the full equality theorem.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/EntanglementBreakingOverlapPurity.affine_overlap_purity_and_rigidity`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/EntanglementBreakingOverlapPurity.meanOutput`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/EntanglementBreakingOverlapPurity.projector`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/EntanglementBreakingOverlapPurity.trace_projectors`
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausChannel](../Foundation/FiniteKrausChannel.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteTraceDistance](../Foundation/FiniteTraceDistance.md)
