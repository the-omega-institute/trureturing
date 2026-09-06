# Finite Synthesis Gram Distance

## Abstract

Finite synthesis into a Hilbert space gives a singular Gram formula for projection and distance.

Universally, k is an RCLike field, E is a finite-dimensional inner-product space, and H is a complete inner-product space over k. Every V below is continuous and k-linear. Set S = range V, G = V* V and b = V* x. P denotes the independently defined orthogonal projection onto S, infDist is the metric infimum over S, and MP is the constructed Moore-Penrose inverse. No injectivity or invertibility is assumed.

**Theorem 1.1 (Operator projection identity).**

$$\forall V:E\to_{k}H, P_{S} = V\operatorname{MP}(G)V^{*}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hilbert/FiniteSynthesisGramDistance.finite_synthesis_gram_projection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The adjoint target lies in the Gram range. The first Penrose law then yields the normal equation, and the residual is orthogonal to the entire synthesis range. Projection uniqueness gives the displayed equality of operators on H.

**Theorem 1.2 (Squared infimum distance).**

$$\forall V:E\to_{k}H, \forall x\in H, \operatorname{infDist}(x,S)^{2} = \Vert x\Vert^{2}-\Re(\langle b, \operatorname{MP}(G)b\rangle)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hilbert/FiniteSynthesisGramDistance.finite_synthesis_gram_distance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Projection minimality identifies infDist with the residual norm; the squared-norm expansion gives the Gram quadratic expression.

**Theorem 1.3 (Reality of the quadratic expression).**

$$\forall V:E\to_{k}H, \forall x\in H, \langle b, \operatorname{MP}(G)b\rangle = \Vert P_{S}x\Vert^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hilbert/FiniteSynthesisGramDistance.finite_synthesis_gram_quadratic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The nonnegative real squared norm on the right is coerced into k. Thus over the complex field this proves reality as well as the value.

**Theorem 1.4 (Identification with the ordinary inverse).**

$$\forall A:E\equiv_{k}E, \operatorname{MP}(A) = A^{-1}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hilbert/FiniteSynthesisGramDistance.moore_penrose_eq_inverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A is any linear equivalence on E. Its ordinary inverse satisfies all four laws, so the imported uniqueness theorem applies.

**Theorem 1.5 (Invertible Gram specialization).**

$$\forall V:E\to_{k}H, \forall x\in H, \forall G:E\equiv_{k}E, G = V^{*}V \Rightarrow \operatorname{infDist}(x,S)^{2} = \Vert x\Vert^{2}-\Re(\langle b, G^{-1}b\rangle)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hilbert/FiniteSynthesisGramDistance.finite_synthesis_gram_distance_inverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Only this specialization assumes that the Gram operator is a linear equivalence. The singular case remains covered by the preceding identities.

## References

- Truth anchor: `D5/S3/Observer/Hilbert/FiniteSynthesisGramDistance.finite_synthesis_gram_distance`
- Truth anchor: `D5/S3/Observer/Hilbert/FiniteSynthesisGramDistance.finite_synthesis_gram_distance_inverse`
- Truth anchor: `D5/S3/Observer/Hilbert/FiniteSynthesisGramDistance.finite_synthesis_gram_projection`
- Truth anchor: `D5/S3/Observer/Hilbert/FiniteSynthesisGramDistance.finite_synthesis_gram_quadratic`
- Truth anchor: `D5/S3/Observer/Hilbert/FiniteSynthesisGramDistance.moore_penrose_eq_inverse`
- Dependency: [D5/S3/Observer/Hilbert/FiniteMoorePenroseInverse](FiniteMoorePenroseInverse.md)
