# Weighted primitive estimate

## Abstract

A uniform primitive bound controls integration against a smooth real weight.

**Theorem 1.1 (Transferring a primitive bound through a weight).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/WeightedPrimitiveBound.weighted_integral_le_of_primitive_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/WeightedPrimitiveBound.weighted_integral_le_of_primitive_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let A<=B, let f be integrable on [A,B], and let W be continuously differentiable there. Suppose K>=0 and the primitive F(y)=integral from A to y of f has absolute value at most K throughout [A,B]. Then the absolute value of the integral of W*f is at most K times the sum of |W(B)| and the integral of |W'|. The primitive is absolutely continuous and has derivative f almost everywhere. Integration by parts for absolutely continuous functions gives W(B)*F(B) minus the integral of W'*F, since F(A)=0. The primitive bound controls both terms.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/WeightedPrimitiveBound.weighted_integral_le_of_primitive_bound`
