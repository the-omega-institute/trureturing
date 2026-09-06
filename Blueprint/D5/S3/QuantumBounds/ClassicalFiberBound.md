# Exact Classical Local-Fiber CHSH Bound

## Abstract

Finite deterministic local-fiber models have exact absolute CHSH bound two.

**Theorem 1.1 (Every probability-weighted local model satisfies the bound).**

$$\forall m,\ \Vert S_{\mathrm{cl}}(\mu,m)\Vert\leq2$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/ClassicalFiberBound.classical_chsh_abs_le_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite fiber, let mu be nonnegative weights summing to one. Every deterministic local answer model m then has weighted CHSH value between minus two and two.

**Theorem 1.2 (Constant positive answers attain two).**

$$\exists m,\ S_{\mathrm{cl}}(\mu,m)=2$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/ClassicalFiberBound.classical_chsh_eq_two_exists` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any finite real weight table mu summing to one, the deterministic model with all four answer tables constantly true attains CHSH value two. This existence statement needs normalization alone, without nonnegativity of the weights.

**Theorem 1.3 (The classical local-fiber CHSH bound is exactly two).**

$$\max_{\mathrm{local}} \Vert S_{\mathrm{cl}}(\mu)\Vert=2.$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/ClassicalFiberBound.classical_chsh_bound_is_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Fiber be finite. A deterministic local model assigns Boolean answer tables a0 and a1 to Alice and b0 and b1 to Bob, all depending only on the same hidden fiber address. Reading false and true as minus one and plus one, respectively, the pointwise CHSH value is a0*b0 + a0*b1 + a1*b0 - a1*b1. For nonnegative weights mu summing to one, classicalCHSH is the finite sum of mu times this pointwise value.

The declaration classical_chsh_abs_le_two proves that every such weighted model has absolute value at most two. Its pointwise upper bound invokes mathlib's CHSH_inequality_of_comm on the four real answer values. Flipping both Alice answers and invoking the same theorem supplies the lower bound; finite convexity then transports both inequalities through the weights.

The companion declaration classical_chsh_eq_two_exists takes all four answer tables constantly true and obtains value two from weight normalization. The stated IsGreatest certificate combines that witness with the absolute upper bound. Thus, when the hidden address is read as the shared local variable, the classical fiber bound is exactly 2.0.

For contrast only, CHSHWitness.bell_chsh_value is the already frozen finite quantum witness with value two times square root two. This module does not reprove that value or a quantum upper bound, and it introduces no infinite fiber, measure-theoretic generalization, or general theory of Bell inequalities.

## References

- Truth anchor: `D5/S3/QuantumBounds/ClassicalFiberBound.classical_chsh_abs_le_two`
- Truth anchor: `D5/S3/QuantumBounds/ClassicalFiberBound.classical_chsh_bound_is_exact`
- Truth anchor: `D5/S3/QuantumBounds/ClassicalFiberBound.classical_chsh_eq_two_exists`
- Dependency: [D5/S3/QuantumBounds/CHSHWitness](CHSHWitness.md)
