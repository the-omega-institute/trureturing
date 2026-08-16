# Collision Conservation from a Two-Design Identity

## Abstract

A finite projective two-design component identity contracts to exact collision conservation.

**Theorem 1.1 (Two-design contraction gives collision conservation).**

$$\operatorname{trace}(\rho) = 1,\\\forall a, b, c, d, \sum_{x} P_{x}(a,b)P_{x}(c,d) = \delta_{ab}\delta_{cd}+\delta_{ad}\delta_{cb} \Rightarrow\\\sum_{x} \operatorname{trace}(\rho P_{x})^{2} = 1+\operatorname{trace}(\rho^{2})$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/Designs/CollisionConservation.collision_sum_eq_one_add_purity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let rho be a real finite square matrix of trace one and let P_x be a finite family of real square matrices. If the summed products of their entries obey the displayed projective two-design component identity, then the sum of the squared trace pairings trace(rho P_x) is exactly one plus trace(rho squared).

The proof expands both traces, interchanges finite sums, applies the component identity, and contracts its two Kronecker-delta terms. The first term is the square of trace(rho), while the second is trace(rho squared).

This theorem proves only the algebraic implication from the supplied two-design identity to collision conservation. It does not construct mutually unbiased bases or prove that any such family satisfies the two-design identity.

## References

- Truth anchor: `D5/S3/QuantumBounds/Designs/CollisionConservation.collision_sum_eq_one_add_purity`
