# Density span

## Abstract

Density matrices span the real Hermitian matrix space in every finite dimension.

**Definition 1.1 (Density matrices).**

$$\forall d \in \mathbb{N},\; \forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \operatorname{IsDensity}\left(A\right) \Leftrightarrow ((\operatorname{PosSemidef}\left(A\right)) \land (\operatorname{tr}\left(A\right) = 1))$$

*Formalization.* `D5/S3/QuantumStates/DensitySpan.IsDensity` (`✓ std3`).

*Citation.* A. Meunson; T. Deesuwan (2026). *Cumulant-based quantum relative Rényi functional*. DOI: [10.48550/arXiv.2606.31205](https://doi.org/10.48550/arXiv.2606.31205). URL: <https://arxiv.org/abs/2606.31205v1>.

*Commentary.*

A density matrix on C^d is a positive semidefinite complex d by d matrix with trace one, in every natural dimension.

**Definition 1.2 (Tomographic completeness).**

$$\forall d \in \mathbb{N},\; \forall T \in \operatorname{Set}\left(\operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right),\; \operatorname{TomographicallyComplete}\left(T\right) \Leftrightarrow ((\forall rho \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; (rho \in T) \Rightarrow ((\operatorname{PosSemidef}\left(rho\right)) \land (\operatorname{tr}\left(rho\right) = 1))) \land (\operatorname{span}\left(\mathbb{R}, T\right) = \operatorname{HermitianSpace}\left(d\right)))$$

*Formalization.* `D5/S3/QuantumStates/DensitySpan.TomographicallyComplete` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every member of a tomographically complete set is positive semidefinite with trace one, and its real span is the Hermitian matrix space.

**Theorem 1.3 (All density matrices are tomographically complete).**

$$\forall d \in \mathbb{N},\; \operatorname{TomographicallyComplete}\left(\{rho : \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right) | (\operatorname{PosSemidef}\left(rho\right)) \land (\operatorname{tr}\left(rho\right) = 1)\}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumStates/DensitySpan.all_density_tomographically_complete` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In every natural dimension, including dimension zero, the set of positive semidefinite trace-one matrices spans the real Hermitian operator space.

## References

- Truth anchor: `D5/S3/QuantumStates/DensitySpan.IsDensity`
- Truth anchor: `D5/S3/QuantumStates/DensitySpan.TomographicallyComplete`
- Truth anchor: `D5/S3/QuantumStates/DensitySpan.all_density_tomographically_complete`
- Dependency: [D5/S3/Quantum/Measurement/BasisMeasurementProjection](../Quantum/Measurement/BasisMeasurementProjection.md)
