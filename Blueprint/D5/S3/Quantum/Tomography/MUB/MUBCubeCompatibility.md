# MUB Cube Compatibility

## Abstract

Factorized cubes have cross-Gram identities; local Zauner factors have a swap symmetry.

**Definition 1.1 (Flattened cube matrix).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/MUBCubeCompatibility.factorizedCubeMatrix`

*Formalization.* `D5/S3/Quantum/Tomography/MUB/MUBCubeCompatibility.factorizedCubeMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For complex matrices H, X and Y, the matrix indexed by (i,j) and k has entry H(i,j) X(j,k) Y(i,k).

**Theorem 1.2 (Entrywise cross-Gram identity).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/MUBCubeCompatibility.factorizedCube_crossGram_apply`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/MUB/MUBCubeCompatibility.factorizedCube_crossGram_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For finite row types and an entrywise unit H, the (k,l) cross-Gram entry of the cubes formed from X,Y and Xprime,Yprime equals the product of the corresponding entries of X-adjoint times Xprime and Y-adjoint times Yprime.

**Theorem 1.3 (Matrix cross-Gram identity).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/MUBCubeCompatibility.factorizedCube_crossGram`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/MUB/MUBCubeCompatibility.factorizedCube_crossGram` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With finite row types and entrywise unit H, the cross-Gram matrix of two factorized cubes equals the entrywise product of the two factor cross-Gram matrices.

**Definition 1.4 (Polynomial local factors).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/MUBCubeCompatibility.ZaunerTwoByTwoFactor`

*Formalization.* `D5/S3/Quantum/Tomography/MUB/MUBCubeCompatibility.ZaunerTwoByTwoFactor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A factor for complex entries a,b,c,d consists of u,v,x,y with u+v=2a, y(u-v)=2b, u-v=2cx and y(u+v)=2dx.

**Theorem 1.5 (Upper-right entry recovery).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/MUBCubeCompatibility.zaunerTwoByTwo_b_eq_y_mul_c_mul_x`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/MUB/MUBCubeCompatibility.zaunerTwoByTwo_b_eq_y_mul_c_mul_x` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every local factor satisfies b=y c x.

**Theorem 1.6 (Quadratic constraint on x).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/MUBCubeCompatibility.zaunerTwoByTwo_x_quadratic`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/MUB/MUBCubeCompatibility.zaunerTwoByTwo_x_quadratic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every local factor satisfies c d x squared = a b.

**Theorem 1.7 (Quadratic constraint on y).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/MUBCubeCompatibility.zaunerTwoByTwo_y_quadratic`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/MUB/MUBCubeCompatibility.zaunerTwoByTwo_y_quadratic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every local factor satisfies a c y squared = b d.

**Theorem 1.8 (Binary ambiguity of x).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/MUBCubeCompatibility.zaunerTwoByTwo_x_eq_or_eq_neg`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/MUB/MUBCubeCompatibility.zaunerTwoByTwo_x_eq_or_eq_neg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If c d is nonzero, two local factors for the same entries have equal or opposite x coordinates.

**Theorem 1.9 (Binary ambiguity of y).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/MUBCubeCompatibility.zaunerTwoByTwo_y_eq_or_eq_neg`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/MUB/MUBCubeCompatibility.zaunerTwoByTwo_y_eq_or_eq_neg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If a c is nonzero, two local factors for the same entries have equal or opposite y coordinates.

**Theorem 1.10 (Rigidity up to swap).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/MUBCubeCompatibility.zaunerTwoByTwo_same_or_swap`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/MUB/MUBCubeCompatibility.zaunerTwoByTwo_same_or_swap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For factors z and w of the same entries, if c d and z.x are nonzero, then w equals z or z.swap.

**Theorem 1.11 (Pointwise vanishing permits mixed orientation).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/MUBCubeCompatibility.pointwise_product_zero_does_not_force_global_orientation`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/MUB/MUBCubeCompatibility.pointwise_product_zero_does_not_force_global_orientation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There exist two nonnegative real families on Fin 2 with every pointwise product zero but with a nonzero product of their sums. The proof uses the families (1,0) and (0,1).

**Theorem 1.12 (Global vanishing implies pointwise vanishing).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/MUBCubeCompatibility.pointwise_product_zero_of_global_sum_product_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/MUB/MUBCubeCompatibility.pointwise_product_zero_of_global_sum_product_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For two nonnegative real families on a finite type, a zero product of their sums implies that every pointwise product is zero.

## References

- Truth anchor: `D5/S3/Quantum/Tomography/MUB/MUBCubeCompatibility.ZaunerTwoByTwoFactor`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/MUBCubeCompatibility.factorizedCubeMatrix`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/MUBCubeCompatibility.factorizedCube_crossGram`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/MUBCubeCompatibility.factorizedCube_crossGram_apply`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/MUBCubeCompatibility.pointwise_product_zero_does_not_force_global_orientation`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/MUBCubeCompatibility.pointwise_product_zero_of_global_sum_product_zero`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/MUBCubeCompatibility.zaunerTwoByTwo_b_eq_y_mul_c_mul_x`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/MUBCubeCompatibility.zaunerTwoByTwo_same_or_swap`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/MUBCubeCompatibility.zaunerTwoByTwo_x_eq_or_eq_neg`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/MUBCubeCompatibility.zaunerTwoByTwo_x_quadratic`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/MUBCubeCompatibility.zaunerTwoByTwo_y_eq_or_eq_neg`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/MUBCubeCompatibility.zaunerTwoByTwo_y_quadratic`
- Dependency: [D5/S3/Quantum/Tomography/MUB/MUBHadamardCompatibility](MUBHadamardCompatibility.md)
