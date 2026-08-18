# Complex Reference-Frame Machinery

## Abstract

The finite exchange-channel fidelity, sharp optimum, and paired top eigenspace extend from real to complex reference amplitudes.

**Theorem 1.1 (Complex fidelity is the nearest-neighbour quadratic).**

$$\forall c \in \mathbb{C}^{N},\quad F_{e}(c) = \lvert Jc\rvert_{2}^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/ReferenceFrame/Complexification.complex_entanglement_fidelity_eq_nearest_neighbor_quadratic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite Kraus trace expression is evaluated with complex reference amplitudes. Its two surviving off-diagonal entries give exactly the squared complex norm of zero-boundary nearest-neighbour averaging.

**Theorem 1.2 (The complex optimum equals the real optimum).**

$$1\leq N \longrightarrow \operatorname{max}_{c\in\mathbb{C}^{N}, \lvert c\rvert_{2}=1} F_{e}(c) = \operatorname{cos}(\frac{\pi}{N+1})^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/ReferenceFrame/Complexification.complex_tax_optimum_eq_real_optimum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Writing each amplitude as a real part plus I times an imaginary part splits both the unit norm and the averaging quadratic into two real summands. The frozen real upper bound applies to both summands, and a real sine witness attains the same value in the complex domain.

**Theorem 1.3 (The complex top eigenspace has dimension two).**

$$2\leq N \longrightarrow \operatorname{finrank}_{\mathbb{C}} \operatorname{eigenspace}(J^{2}, \operatorname{cos}(\frac{\pi}{N+1})^{2}) = 2$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/ReferenceFrame/Complexification.complex_top_eigenspace_finrank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Real and imaginary parts of a complex squared-top eigenvector lie in the frozen real paired-mode space. Scalar extension preserves independence of the low and high modes, so the full complex eigenspace has complex dimension two for N at least two.

**Theorem 1.4 (The complex flat vector has the exact tax).**

$$2\leq N \longrightarrow 1 - F_{e}(m \mapsto 1/\sqrt{N}) = \frac{3}{2N}$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/ReferenceFrame/Complexification.flat_tax_complex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The flat complex vector is the real flat vector under the canonical embedding. Its tax is therefore 3/(2N) when N is at least two. The restriction is necessary: the frozen one-level calculation has tax one rather than three halves.

## References

- Truth anchor: `D5/S3/QuantumBounds/ReferenceFrame/Complexification.complex_entanglement_fidelity_eq_nearest_neighbor_quadratic`
- Truth anchor: `D5/S3/QuantumBounds/ReferenceFrame/Complexification.complex_tax_optimum_eq_real_optimum`
- Truth anchor: `D5/S3/QuantumBounds/ReferenceFrame/Complexification.complex_top_eigenspace_finrank`
- Truth anchor: `D5/S3/QuantumBounds/ReferenceFrame/Complexification.flat_tax_complex`
- Dependency: [D5/S3/QuantumBounds/ReferenceFrame/ChannelFidelityBridge](ChannelFidelityBridge.md)
- Dependency: [D5/S3/QuantumBounds/ReferenceFrame/TopEigenspace](TopEigenspace.md)
