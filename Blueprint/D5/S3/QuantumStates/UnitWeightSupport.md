# Unit Weight Forces Projection Support

## Abstract

A positive trace-one matrix with unit weight on a self-adjoint projection is supported on that projection.

**Theorem 1.1 (Unit projection weight confines the state).**

$$\forall n,\ [\operatorname{Fintype}(n)],\ [\operatorname{DecidableEq}(n)],\ \forall \rho, P \in \operatorname{Matrix}(n, n, \mathbb, {C}),\ \operatorname{PosSemidef}(\rho) \land P^{*} = P \land P^{2} = P \land \operatorname{trace}(\rho) = 1 \land \operatorname{trace}(\rho\,P) = 1 \Rightarrow \rho = P\,\rho\,P.$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumStates/UnitWeightSupport.unit_weight_support_face` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The hypotheses are the source state primitives: positivity and trace-one normalization for rho, together with self-adjointness and idempotence for the projection P.

Unit trace weight on P gives zero trace weight on the complementary projection I minus P. The exact zero-weight support-face theorem then yields rho equals P rho P.

No support condition is assumed in advance; the compression is the public conclusion forced by the source weight test.

## References

- Truth anchor: `D5/S3/QuantumStates/UnitWeightSupport.unit_weight_support_face`
- Dependency: [D5/S3/QuantumStates/ZeroWeightSupportFace](ZeroWeightSupportFace.md)
