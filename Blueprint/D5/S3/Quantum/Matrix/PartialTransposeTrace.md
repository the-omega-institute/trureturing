# Partial-transpose trace duality

## Abstract

Partial transpose is self-adjoint for trace pairing on arbitrary finite product index types.

**Theorem 1.1 (Quadratic testing and trace pairing).**

$$\forall (A:Type), \forall (B:Type), \forall (instA:Fintype\left(A\right)), \forall (instB:Fintype\left(B\right)), \forall (M:Matrix\left((A\times B), (A\times B), \mathbb{C}\right)), \forall (v:(A\times B)\to \mathbb{C}), dotProduct\left(star\left(v\right), mulVec\left(partialTranspose\left(M\right), v\right)\right)=trace\left(mul\left(M, partialTranspose\left(vecMulVec\left(v, star\left(v\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/PartialTransposeTrace.partial_transpose_trace_duality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let A and B be arbitrary types with their given Fintype instances, M any complex matrix on A × B and v any complex vector on A × B. With second-factor partial transpose Gamma(M)[(a,b),(c,d)]=M[(a,d),(c,b)], star(v) dot (Gamma(M) v) equals tr(M Gamma(v star(v))). The displayed instA and instB binders are the two finite-type instances. The local cardinalities may differ and may be zero. No Hermiticity, positivity, trace-one condition, APPT hypothesis or normalization of v is assumed. Finite trace expansion and interchange of the two second-factor indices prove trace self-adjointness; the standard outer-product trace identity gives the vector formula. This is the standard trace-pairing identity in the repository's product-index convention, rather than a new physical criterion. It is consumed by the uniform rank-four necessary inequality, whose swap test uses a genuine four-by-four local product corner.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/PartialTransposeTrace.partial_transpose_trace_duality`
- Dependency: [D5/S3/Quantum/Dynamics/KickedIsingNegativityRefutation](../Dynamics/KickedIsingNegativityRefutation.md)
