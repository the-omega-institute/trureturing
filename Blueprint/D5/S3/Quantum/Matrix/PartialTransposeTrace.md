# Partial transpose and trace pairing

## Abstract

Finite product-coordinate trace duality for partial transpose.

**Theorem 1.1 (Vector and trace duality).**

$$\forall (A:FiniteType), \forall (B:FiniteType), \forall (M:Matrix\left(Product\left(A, B\right), C\right)), \forall (v:Vector\left(Product\left(A, B\right), C\right)), inner\left(v, apply\left(partialTranspose\left(M\right), v\right)\right)=trace\left(multiply\left(M, partialTranspose\left(outer\left(v, v\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/PartialTransposeTrace.partial_transpose_trace_duality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let A and B be arbitrary finite types, M a complex square matrix indexed by A times B, and v a complex vector on the same product. With Gamma(M)_(a,b),(c,d)=M_(a,d),(c,b), the identity is v* Gamma(M) v = Tr(M Gamma(v v*)). The vector need not be normalized; M need not be Hermitian or positive. Empty carriers and unequal local dimensions are included.

The bilinear identity Tr(Gamma(M) N)=Tr(M Gamma(N)) follows by interchanging the two B indices in the four finite sums. The vector identity then uses the standard matrix outer-product multiplication and trace identities. This supplies the trace bridge for fixed product-corner APPT tests and uses the existing partialTranspose convention.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/PartialTransposeTrace.partial_transpose_trace_duality`
- Dependency: [D5/S3/Quantum/Dynamics/KickedIsingNegativityRefutation](../Dynamics/KickedIsingNegativityRefutation.md)
