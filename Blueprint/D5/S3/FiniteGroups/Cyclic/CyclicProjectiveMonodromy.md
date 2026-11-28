# Cyclic Projective Monodromy

## Abstract

The projective centralizer action on the generator determines the cyclic product of its associator.

**Theorem 1.1 (The cyclic product from the projective power).**

Lean statement: `D5/S3/FiniteGroups/Cyclic/CyclicProjectiveMonodromy.pow_orderOf_eq_cyclicProduct_smul`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/Cyclic/CyclicProjectiveMonodromy.pow_orderOf_eq_cyclicProduct_smul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The slant multiplier at powers x of g and y = g is α(g,x,g), because α(x,y,g) and α(x,g,y) then coincide. Repeated multiplication by T(g) accumulates these scalars. The last operator is T(1), which is the identity.

**Theorem 1.2 (Detection on a nonzero eigenvector).**

Lean statement: `D5/S3/FiniteGroups/Cyclic/CyclicProjectiveMonodromy.cyclicProduct_coe_eq_eigenvalue_pow`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/Cyclic/CyclicProjectiveMonodromy.cyclicProduct_coe_eq_eigenvalue_pow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On a nonzero eigenvector of T(g), the same operator power acts by the eigenvalue raised to the order of g. Comparing the two scalar actions determines the cyclic product.

**Theorem 1.3 (Cubic conformal monodromy obstructs a subgroup restriction).**

Lean statement: `D5/S3/FiniteGroups/Cyclic/CyclicProjectiveMonodromy.not_mem_of_order_three_monodromy`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/Cyclic/CyclicProjectiveMonodromy.not_mem_of_order_three_monodromy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At order three with conformal weight 16/9 + n/3, the cube of the monodromy eigenphase is exp(2πi/3). Every element of a subgroup trivializing the same associator has cyclic product one. The cubic generator therefore lies outside that subgroup.

Application to a lattice vertex operator algebra requires the projective law for the ambient associator and the phase identification on the actual twisted module. The conformal phase uses the generator-flux convention of Evans–Gannon, arXiv:1804.11145, equation (2.14).

## References

- Truth anchor: `D5/S3/FiniteGroups/Cyclic/CyclicProjectiveMonodromy.cyclicProduct_coe_eq_eigenvalue_pow`
- Truth anchor: `D5/S3/FiniteGroups/Cyclic/CyclicProjectiveMonodromy.not_mem_of_order_three_monodromy`
- Truth anchor: `D5/S3/FiniteGroups/Cyclic/CyclicProjectiveMonodromy.pow_orderOf_eq_cyclicProduct_smul`
- Dependency: [D5/S3/FiniteGroups/Cyclic/CyclicAssociatorObstruction](CyclicAssociatorObstruction.md)
