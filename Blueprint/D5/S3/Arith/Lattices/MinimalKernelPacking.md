# MinimalKernelPacking

## Abstract

Rounded partial weights encode a minimal nonnegative kernel vector in a finite cube.

**Theorem 1.1 (minimal kernel rank deficient bound).**

$$\forall \{r k m : \mathbb{N}\}, \forall (M : \operatorname{Matrix} (\operatorname{Fin} (r + 1)) (\operatorname{Fin} k) \mathbb{Z}), (\forall i j , | M i j | \le m) \to (\neg \operatorname{Function} . \operatorname{Injective} (\operatorname{fun} z : \operatorname{Fin} (r + 1) \to \mathbb{Z} \mapsto M . \operatorname{transpose} *_{v} z)) \to \forall (x : \operatorname{Fin} k \to \mathbb{N}), (0 < \sum j , x j) \to (M *_{v} (\operatorname{fun} j \mapsto (x j : \mathbb{Z})) = 0) \to (\forall y : \operatorname{Fin} k \to \mathbb{N} , y \le x \to M *_{v} (\operatorname{fun} j \mapsto (y j : \mathbb{Z})) = 0 \to y = 0 \lor y = x) \to \sum j , x j \le  (2 * k * m + 1)^{r} * k$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/MinimalKernelPacking.minimal_kernel_rank_deficient_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Rounded partial weights encode a minimal nonnegative kernel vector in a finite cube.

**Theorem 1.2 (transpose injective of augmented det).**

$$\forall \{d : \mathbb{N}\}, \forall (M : \operatorname{Matrix} (\operatorname{Fin} d) (\operatorname{Fin} (d + 1)) \mathbb{Z}), ((\operatorname{augment} M) . \operatorname{det} \neq 0) \to \operatorname{Function} . \operatorname{Injective} (\operatorname{fun} z : \operatorname{Fin} d \to \mathbb{Z} \mapsto M . \operatorname{transpose} *_{v} z)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/MinimalKernelPacking.transpose_injective_of_augmented_det` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Rounded partial weights encode a minimal nonnegative kernel vector in a finite cube.

**Theorem 1.3 (augmented det ne zero of full rank positive).**

$$\forall \{d : \mathbb{N}\}, \forall (M : \operatorname{Matrix} (\operatorname{Fin} d) (\operatorname{Fin} (d + 1)) \mathbb{Z}), (\operatorname{Function} . \operatorname{Injective} (\operatorname{fun} z : \operatorname{Fin} d \to \mathbb{Z} \mapsto M . \operatorname{transpose} *_{v} z)) \to \forall (x : \operatorname{Fin} (d + 1) \to \mathbb{Z}), (M *_{v} x = 0) \to (\sum j , x j \neq 0) \to (\operatorname{augment} M) . \operatorname{det} \neq 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/MinimalKernelPacking.augmented_det_ne_zero_of_full_rank_positive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Rounded partial weights encode a minimal nonnegative kernel vector in a finite cube.

## References

- Truth anchor: `D5/S3/Arith/Lattices/MinimalKernelPacking.augmented_det_ne_zero_of_full_rank_positive`
- Truth anchor: `D5/S3/Arith/Lattices/MinimalKernelPacking.minimal_kernel_rank_deficient_bound`
- Truth anchor: `D5/S3/Arith/Lattices/MinimalKernelPacking.transpose_injective_of_augmented_det`
- Dependency: [D5/S3/Arith/Lattices/CofactorKernel](CofactorKernel.md)
