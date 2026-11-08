# Finite product moment bounds

## Abstract

Fourth moments control products of at most four factors and their replacement errors.

**Theorem 1.1 (Integrability of finite products).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/FiniteProductMomentBounds.product_integrable`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/FiniteProductMomentBounds.product_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive k on any measure space, if each of k real functions belongs to Lk, their product is integrable. The reciprocal Holder exponents sum to one.

**Theorem 1.2 (Products controlled by fourth moments).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/FiniteProductMomentBounds.product_fourth_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/FiniteProductMomentBounds.product_fourth_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On any probability space, let 1<=k<=4 and let f_i belong to L4. If the fourth moment of f_i is at most C_i>=0, then the integral of the absolute product is at most the product of C_i^(1/4). Holder at exponent k and monotonicity of probability-space Lp norms give the estimate, including when a bound vanishes.

**Theorem 1.3 (Fourth moment control of replacement errors).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/FiniteProductMomentBounds.product_fourth_difference_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/FiniteProductMomentBounds.product_fourth_difference_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On a probability space with 1<=k<=4, suppose both families have fourth moments at most K>=0 and their differences have fourth moments at most D>=0. The L1 distance between the products is at most k*D^(1/4)*K^((k-1)/4). The proof permits K=0 and D=0 and uses the real-power convention K^0=1 when k=1.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/FiniteProductMomentBounds.product_fourth_bound`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/FiniteProductMomentBounds.product_fourth_difference_bound`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/FiniteProductMomentBounds.product_integrable`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/MomentTransfer](MomentTransfer.md)
