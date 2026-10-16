# CofactorKernel

## Abstract

Primitive positive integer kernels give the multiplicities and lengths of minimal zero-sum sequences.

**Definition 1.1 (IsMinimalZeroSum).**

$$\forall \{d : \mathbb{N}\}, \forall (f : (\operatorname{Fin} d \to \mathbb{Z}) \to_{0} \mathbb{N}), \operatorname{IsMinimalZeroSum} f = (f \neq 0 \land (\operatorname{fun} f : (\operatorname{Fin} d \to \mathbb{Z}) \to_{0} \mathbb{N} \mapsto f . \operatorname{sum} (\operatorname{fun} v n \mapsto (n : \mathbb{Z}) \cdot v)) f = 0 \land \forall g : (\operatorname{Fin} d \to \mathbb{Z}) \to_{0} \mathbb{N} , g \le f \to g \neq 0 \to g \neq f \to (\operatorname{fun} f : (\operatorname{Fin} d \to \mathbb{Z}) \to_{0} \mathbb{N} \mapsto f . \operatorname{sum} (\operatorname{fun} v n \mapsto (n : \mathbb{Z}) \cdot v)) g \neq 0)$$

*Formalization.* `D5/S3/Arith/Lattices/CofactorKernel.IsMinimalZeroSum` (`✓ std3`).

*Citation.* Benjamin Girard and Alain Plagne (2026). *The Davenport constant of low-dimensional boxes*. DOI: [10.48550/arXiv.2610.16562](https://doi.org/10.48550/arXiv.2610.16562). URL: <https://arxiv.org/abs/2610.16562v1>.

*Commentary.*

Section 1, printed page 1: "Moreover, if S is a zero-sum sequence such that ∑ᵢ∈ᴵ xᵢ ≠ 0 for every ∅ ≠ I ⊊ ⟦1, ℓ⟧, it will be called a minimal zero-sum sequence." A multiplicity function is nonzero, has zero total, and has no nonempty proper zero-sum subfunction.

**Definition 1.2 (lengths).**

$$\forall (d m k : \mathbb{N}), \operatorname{lengths} d m k = (\{L | \exists f : (\operatorname{Fin} d \to \mathbb{Z}) \to_{0} \mathbb{N} , \operatorname{IsMinimalZeroSum} f \land (\operatorname{CoeTC}.\operatorname{coe} f . \operatorname{support} : \operatorname{Set} (\operatorname{Fin} d \to \mathbb{Z})) \subseteq (\operatorname{fun} d m \mapsto \{v : \operatorname{Fin} d \to \mathbb{Z} | \forall i , | v i | \le (m : \mathbb{N})\}) d m \land f . \operatorname{support} . \operatorname{card} = k \land (f . \operatorname{sum} \operatorname{fun} _ n \mapsto n) = L\})$$

*Formalization.* `D5/S3/Arith/Lattices/CofactorKernel.lengths` (`✓ std3`).

*Citation.* Benjamin Girard and Alain Plagne (2026). *The Davenport constant of low-dimensional boxes*. DOI: [10.48550/arXiv.2610.16562](https://doi.org/10.48550/arXiv.2610.16562). URL: <https://arxiv.org/abs/2610.16562v1>.

*Commentary.*

Section 2, printed page 2: "we study the quantity D^(d+1)(⟦−m, m⟧^d) which is defined as the maximal length of a minimal zero-sum sequence over ⟦−m, m⟧^d having a support of size d + 1." Multiplicity functions use pointwise subsequence order; support cardinality counts distinct vectors.

**Definition 1.3 (augment).**

$$\forall \{R : \operatorname{Type}\}, [\operatorname{One} R] \forall \{d : \mathbb{N}\}, \forall (M : \operatorname{Matrix} (\operatorname{Fin} d) (\operatorname{Fin} (d + 1)) R), \operatorname{augment} M = (\operatorname{Fin} . \operatorname{cases} (\operatorname{fun} _ \mapsto 1) M)$$

*Formalization.* `D5/S3/Arith/Lattices/CofactorKernel.augment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Primitive positive integer kernels give the multiplicities and lengths of minimal zero-sum sequences.

**Theorem 1.4 (augment zero).**

$$\forall \{R : \operatorname{Type}\}, [\operatorname{One} R] \forall \{d : \mathbb{N}\}, \forall (M : \operatorname{Matrix} (\operatorname{Fin} d) (\operatorname{Fin} (d + 1)) R), \forall (j : \operatorname{Fin} (d + 1)), \operatorname{augment} M 0 j = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/CofactorKernel.augment_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Primitive positive integer kernels give the multiplicities and lengths of minimal zero-sum sequences.

**Theorem 1.5 (augment succ).**

$$\forall \{R : \operatorname{Type}\}, [\operatorname{One} R] \forall \{d : \mathbb{N}\}, \forall (M : \operatorname{Matrix} (\operatorname{Fin} d) (\operatorname{Fin} (d + 1)) R), \forall (i : \operatorname{Fin} d), \forall (j : \operatorname{Fin} (d + 1)), \operatorname{augment} M i . \operatorname{succ} j = M i j$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/CofactorKernel.augment_succ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Primitive positive integer kernels give the multiplicities and lengths of minimal zero-sum sequences.

**Definition 1.6 (cofactor).**

$$\forall \{R : \operatorname{Type}\}, [\operatorname{CommRing} R] \forall \{d : \mathbb{N}\}, \forall (M : \operatorname{Matrix} (\operatorname{Fin} d) (\operatorname{Fin} (d + 1)) R), \forall (j : \operatorname{Fin} (d + 1)), \operatorname{cofactor} M j = ((- 1)^{j . \operatorname{val}} * (M . \operatorname{submatrix} \operatorname{id} j . \operatorname{succAbove}) . \operatorname{det})$$

*Formalization.* `D5/S3/Arith/Lattices/CofactorKernel.cofactor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Primitive positive integer kernels give the multiplicities and lengths of minimal zero-sum sequences.

**Theorem 1.7 (cofactor eq adjugate).**

$$\forall \{R : \operatorname{Type}\}, [\operatorname{CommRing} R] \forall \{d : \mathbb{N}\}, \forall (M : \operatorname{Matrix} (\operatorname{Fin} d) (\operatorname{Fin} (d + 1)) R), \forall (j : \operatorname{Fin} (d + 1)), \operatorname{cofactor} M j = (\operatorname{augment} M) . \operatorname{adjugate} j 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/CofactorKernel.cofactor_eq_adjugate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Primitive positive integer kernels give the multiplicities and lengths of minimal zero-sum sequences.

**Theorem 1.8 (cofactor mulVec eq zero).**

$$\forall \{R : \operatorname{Type}\}, [\operatorname{CommRing} R] \forall \{d : \mathbb{N}\}, \forall (M : \operatorname{Matrix} (\operatorname{Fin} d) (\operatorname{Fin} (d + 1)) R), M *_{v} \operatorname{cofactor} M = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/CofactorKernel.cofactor_mulVec_eq_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Primitive positive integer kernels give the multiplicities and lengths of minimal zero-sum sequences.

**Theorem 1.9 (sum cofactor eq det).**

$$\forall \{R : \operatorname{Type}\}, [\operatorname{CommRing} R] \forall \{d : \mathbb{N}\}, \forall (M : \operatorname{Matrix} (\operatorname{Fin} d) (\operatorname{Fin} (d + 1)) R), \sum j , \operatorname{cofactor} M j = (\operatorname{augment} M) . \operatorname{det}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/CofactorKernel.sum_cofactor_eq_det` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Primitive positive integer kernels give the multiplicities and lengths of minimal zero-sum sequences.

**Theorem 1.10 (Cofactor cross identity for a kernel vector).**

$$(\operatorname{augment} M).\operatorname{det} \cdot xi = (\sum j xj) \cdot \operatorname{cofactor} M i$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/CofactorKernel.kernel_cross_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact compiled declaration retains an arbitrary commutative ring R, d, the full d by d+1 matrix M, vector x, original kernel equation hx, and coordinate i. For a d by d+1 matrix over any commutative ring and a vector in its kernel, the determinant of the matrix augmented by a first row of ones times coordinate i equals the sum of the vector coordinates times signed cofactor i. The sign is (-1) to the column index and the minor deletes that column by succAbove. This is the classical adjugate/cofactor expansion identity used by the integer-kernel results. Over the reals, a strictly positive kernel vector and one nonzero cofactor force a nonzero augmented determinant and positive proportionality after choosing an orientation. The nonnegative-kernel cofactor completeness theorem consumes this identity; selected-row kernel membership alone does not establish the original row equations.

**Definition 1.11 (fromWeights).**

$$\forall \{d k : \mathbb{N}\}, \forall (v : \operatorname{Function} . \operatorname{Embedding} (\operatorname{Fin} k) (\operatorname{Fin} d \to \mathbb{Z})), \forall (x : \operatorname{Fin} k \to \mathbb{N}), \operatorname{fromWeights} v x = (\operatorname{Finsupp} . \operatorname{embDomain} v (\operatorname{Finsupp} . \operatorname{equivFunOnFinite} . \operatorname{symm} x))$$

*Formalization.* `D5/S3/Arith/Lattices/CofactorKernel.fromWeights` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Primitive positive integer kernels give the multiplicities and lengths of minimal zero-sum sequences.

**Theorem 1.12 (fromWeights apply).**

$$\forall \{d k : \mathbb{N}\}, \forall (v : \operatorname{Function} . \operatorname{Embedding} (\operatorname{Fin} k) (\operatorname{Fin} d \to \mathbb{Z})), \forall (x : \operatorname{Fin} k \to \mathbb{N}), \forall (i : \operatorname{Fin} k), \operatorname{fromWeights} v x (v i) = x i$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/CofactorKernel.fromWeights_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Primitive positive integer kernels give the multiplicities and lengths of minimal zero-sum sequences.

**Theorem 1.13 (fromWeights support subset).**

$$\forall \{d k : \mathbb{N}\}, \forall (v : \operatorname{Function} . \operatorname{Embedding} (\operatorname{Fin} k) (\operatorname{Fin} d \to \mathbb{Z})), \forall (x : \operatorname{Fin} k \to \mathbb{N}), (\operatorname{CoeTC}.\operatorname{coe} (\operatorname{fromWeights} v x) . \operatorname{support} : \operatorname{Set} (\operatorname{Fin} d \to \mathbb{Z})) \subseteq \operatorname{Set} . \operatorname{range} v$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/CofactorKernel.fromWeights_support_subset` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Primitive positive integer kernels give the multiplicities and lengths of minimal zero-sum sequences.

**Theorem 1.14 (fromWeights restrict).**

$$\forall \{d k : \mathbb{N}\}, \forall (v : \operatorname{Function} . \operatorname{Embedding} (\operatorname{Fin} k) (\operatorname{Fin} d \to \mathbb{Z})), \forall (f : (\operatorname{Fin} d \to \mathbb{Z}) \to_{0} \mathbb{N}), ((\operatorname{CoeTC}.\operatorname{coe} f . \operatorname{support} : \operatorname{Set} (\operatorname{Fin} d \to \mathbb{Z})) \subseteq \operatorname{Set} . \operatorname{range} v) \to \operatorname{fromWeights} v (\operatorname{fun} i \mapsto f (v i)) = f$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/CofactorKernel.fromWeights_restrict` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Primitive positive integer kernels give the multiplicities and lengths of minimal zero-sum sequences.

**Theorem 1.15 (length fromWeights).**

$$\forall \{d k : \mathbb{N}\}, \forall (v : \operatorname{Function} . \operatorname{Embedding} (\operatorname{Fin} k) (\operatorname{Fin} d \to \mathbb{Z})), \forall (x : \operatorname{Fin} k \to \mathbb{N}), \operatorname{Finsupp} . \operatorname{degree} (\operatorname{fromWeights} v x) = \sum j , x j$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/CofactorKernel.length_fromWeights` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Primitive positive integer kernels give the multiplicities and lengths of minimal zero-sum sequences.

**Theorem 1.16 (fromWeights minimal of primitive).**

$$\forall \{d : \mathbb{N}\}, \forall (v : \operatorname{Function} . \operatorname{Embedding} (\operatorname{Fin} (d + 1)) (\operatorname{Fin} d \to \mathbb{Z})), ((\operatorname{augment} ((\operatorname{Matrix} . \operatorname{of} (v : \operatorname{Fin} (d + 1) \to \operatorname{Fin} d \to \mathbb{Z})) . \operatorname{transpose})) . \operatorname{det} \neq 0) \to \forall (x : \operatorname{Fin} (d + 1) \to \mathbb{Z}), ((\operatorname{Matrix} . \operatorname{of} (v : \operatorname{Fin} (d + 1) \to \operatorname{Fin} d \to \mathbb{Z})) . \operatorname{transpose} *_{v} x = 0) \to (\forall i , 0 < x i) \to (\operatorname{Finset} . \operatorname{univ} . \operatorname{gcd} x = 1) \to \operatorname{IsMinimalZeroSum} (\operatorname{fromWeights} v (\operatorname{fun} i \mapsto (x i) . \operatorname{toNat}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/CofactorKernel.fromWeights_minimal_of_primitive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Primitive positive integer kernels give the multiplicities and lengths of minimal zero-sum sequences.

**Theorem 1.17 (total fromWeights eq mulVec).**

$$\forall \{d k : \mathbb{N}\}, \forall (v : \operatorname{Function} . \operatorname{Embedding} (\operatorname{Fin} k) (\operatorname{Fin} d \to \mathbb{Z})), \forall (x : \operatorname{Fin} k \to \mathbb{N}), (\operatorname{fun} f : (\operatorname{Fin} d \to \mathbb{Z}) \to_{0} \mathbb{N} \mapsto f . \operatorname{sum} (\operatorname{fun} v n \mapsto (n : \mathbb{Z}) \cdot v)) (\operatorname{fromWeights} v x) = (\operatorname{Matrix} . \operatorname{of} (v : \operatorname{Fin} k \to \operatorname{Fin} d \to \mathbb{Z})) . \operatorname{transpose} *_{v} (\operatorname{fun} j \mapsto (x j : \mathbb{Z}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/CofactorKernel.total_fromWeights_eq_mulVec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Primitive positive integer kernels give the multiplicities and lengths of minimal zero-sum sequences.

**Theorem 1.18 (fromWeights minimal to vector).**

$$\forall \{d k : \mathbb{N}\}, \forall (v : \operatorname{Function} . \operatorname{Embedding} (\operatorname{Fin} k) (\operatorname{Fin} d \to \mathbb{Z})), \forall (x : \operatorname{Fin} k \to \mathbb{N}), (\operatorname{IsMinimalZeroSum} (\operatorname{fromWeights} v x)) \to \forall (y : \operatorname{Fin} k \to \mathbb{N}), (y \le x) \to ((\operatorname{Matrix} . \operatorname{of} (v : \operatorname{Fin} k \to \operatorname{Fin} d \to \mathbb{Z})) . \operatorname{transpose} *_{v} (\operatorname{fun} j \mapsto (y j : \mathbb{Z})) = 0) \to y = 0 \lor y = x$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/CofactorKernel.fromWeights_minimal_to_vector` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Primitive positive integer kernels give the multiplicities and lengths of minimal zero-sum sequences.

**Theorem 1.19 (sequence cofactor length).**

$$\forall \{d : \mathbb{N}\}, \forall (v : \operatorname{Function} . \operatorname{Embedding} (\operatorname{Fin} (d + 1)) (\operatorname{Fin} d \to \mathbb{Z})), \forall (x : \operatorname{Fin} (d + 1) \to \mathbb{N}), (\forall i , 0 < x i) \to (\operatorname{IsMinimalZeroSum} (\operatorname{fromWeights} v x)) \to ((\operatorname{augment} ((\operatorname{Matrix} . \operatorname{of} (v : \operatorname{Fin} (d + 1) \to \operatorname{Fin} d \to \mathbb{Z})) . \operatorname{transpose})) . \operatorname{det} \neq 0) \to | (\operatorname{augment} ((\operatorname{Matrix} . \operatorname{of} (v : \operatorname{Fin} (d + 1) \to \operatorname{Fin} d \to \mathbb{Z})) . \operatorname{transpose})) . \operatorname{det} | = (\operatorname{Finsupp} . \operatorname{degree} (\operatorname{fromWeights} v x) : \mathbb{Z}) * \operatorname{Finset} . \operatorname{univ} . \operatorname{gcd} (\operatorname{cofactor} ((\operatorname{Matrix} . \operatorname{of} (v : \operatorname{Fin} (d + 1) \to \operatorname{Fin} d \to \mathbb{Z})) . \operatorname{transpose}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/CofactorKernel.sequence_cofactor_length` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Primitive positive integer kernels give the multiplicities and lengths of minimal zero-sum sequences.

**Theorem 1.20 (sequence cofactor multiplicities).**

$$\forall \{d : \mathbb{N}\}, \forall (v : \operatorname{Function} . \operatorname{Embedding} (\operatorname{Fin} (d + 1)) (\operatorname{Fin} d \to \mathbb{Z})), \forall (x : \operatorname{Fin} (d + 1) \to \mathbb{N}), (\forall i , 0 < x i) \to (\operatorname{IsMinimalZeroSum} (\operatorname{fromWeights} v x)) \to ((\operatorname{augment} ((\operatorname{Matrix} . \operatorname{of} (v : \operatorname{Fin} (d + 1) \to \operatorname{Fin} d \to \mathbb{Z})) . \operatorname{transpose})) . \operatorname{det} \neq 0) \to (\forall i , (x i : \mathbb{Z}) = | \operatorname{cofactor} ((\operatorname{Matrix} . \operatorname{of} (v : \operatorname{Fin} (d + 1) \to \operatorname{Fin} d \to \mathbb{Z})) . \operatorname{transpose}) i | / \operatorname{Finset} . \operatorname{univ} . \operatorname{gcd} (\operatorname{cofactor} ((\operatorname{Matrix} . \operatorname{of} (v : \operatorname{Fin} (d + 1) \to \operatorname{Fin} d \to \mathbb{Z})) . \operatorname{transpose}))) \land (\operatorname{Finsupp} . \operatorname{degree} (\operatorname{fromWeights} v x) : \mathbb{Z}) = | (\operatorname{augment} ((\operatorname{Matrix} . \operatorname{of} (v : \operatorname{Fin} (d + 1) \to \operatorname{Fin} d \to \mathbb{Z})) . \operatorname{transpose})) . \operatorname{det} | / \operatorname{Finset} . \operatorname{univ} . \operatorname{gcd} (\operatorname{cofactor} ((\operatorname{Matrix} . \operatorname{of} (v : \operatorname{Fin} (d + 1) \to \operatorname{Fin} d \to \mathbb{Z})) . \operatorname{transpose}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/CofactorKernel.sequence_cofactor_multiplicities` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Primitive positive integer kernels give the multiplicities and lengths of minimal zero-sum sequences.

**Theorem 1.21 (positive kernel orientation).**

$$\forall \{d : \mathbb{N}\}, \forall (A : \operatorname{Matrix} (\operatorname{Fin} d) (\operatorname{Fin} (d + 1)) \mathbb{Z}), ((\operatorname{augment} A) . \operatorname{det} \neq 0) \to \forall (x : \operatorname{Fin} (d + 1) \to \mathbb{Z}), (\forall j , 0 < x j) \to (A *_{v} x = 0) \to \exists s : \mathbb{Z} , (s = 1 \lor s = - 1) \land \forall j , 0 < s * \operatorname{cofactor} A j$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/CofactorKernel.positive_kernel_orientation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Primitive positive integer kernels give the multiplicities and lengths of minimal zero-sum sequences.

**Theorem 1.22 (augmented det ne zero of oriented cofactors).**

$$\forall \{d : \mathbb{N}\}, \forall (A : \operatorname{Matrix} (\operatorname{Fin} d) (\operatorname{Fin} (d + 1)) \mathbb{Z}), \forall (s : \mathbb{Z}), (\forall j , 0 < s * \operatorname{cofactor} A j) \to (\operatorname{augment} A) . \operatorname{det} \neq 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/CofactorKernel.augmented_det_ne_zero_of_oriented_cofactors` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Primitive positive integer kernels give the multiplicities and lengths of minimal zero-sum sequences.

**Theorem 1.23 (cofactor gcd one mul right).**

$$\forall \{d : \mathbb{N}\}, \forall (M : \operatorname{Matrix} (\operatorname{Fin} d) (\operatorname{Fin} (d + 1)) \mathbb{Z}), \forall (W : \operatorname{Matrix} (\operatorname{Fin} (d + 1)) (\operatorname{Fin} (d + 1)) \mathbb{Z}), (\operatorname{IsUnit} W . \operatorname{det}) \to (\operatorname{Finset} . \operatorname{univ} . \operatorname{gcd} (\operatorname{cofactor} M) = 1) \to \operatorname{Finset} . \operatorname{univ} . \operatorname{gcd} (\operatorname{cofactor} (M * W)) = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/CofactorKernel.cofactor_gcd_one_mul_right` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Primitive positive integer kernels give the multiplicities and lengths of minimal zero-sum sequences.

**Theorem 1.24 (cofactor gcd one mul left).**

$$\forall \{d : \mathbb{N}\}, \forall (U : \operatorname{Matrix} (\operatorname{Fin} d) (\operatorname{Fin} d) \mathbb{Z}), \forall (M : \operatorname{Matrix} (\operatorname{Fin} d) (\operatorname{Fin} (d + 1)) \mathbb{Z}), (\operatorname{IsUnit} U . \operatorname{det}) \to (\operatorname{Finset} . \operatorname{univ} . \operatorname{gcd} (\operatorname{cofactor} M) = 1) \to \operatorname{Finset} . \operatorname{univ} . \operatorname{gcd} (\operatorname{cofactor} (U * M)) = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/CofactorKernel.cofactor_gcd_one_mul_left` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Primitive positive integer kernels give the multiplicities and lengths of minimal zero-sum sequences.

## References

- Truth anchor: `D5/S3/Arith/Lattices/CofactorKernel.IsMinimalZeroSum`
- Truth anchor: `D5/S3/Arith/Lattices/CofactorKernel.augment`
- Truth anchor: `D5/S3/Arith/Lattices/CofactorKernel.augment_succ`
- Truth anchor: `D5/S3/Arith/Lattices/CofactorKernel.augment_zero`
- Truth anchor: `D5/S3/Arith/Lattices/CofactorKernel.augmented_det_ne_zero_of_oriented_cofactors`
- Truth anchor: `D5/S3/Arith/Lattices/CofactorKernel.cofactor`
- Truth anchor: `D5/S3/Arith/Lattices/CofactorKernel.cofactor_eq_adjugate`
- Truth anchor: `D5/S3/Arith/Lattices/CofactorKernel.cofactor_gcd_one_mul_left`
- Truth anchor: `D5/S3/Arith/Lattices/CofactorKernel.cofactor_gcd_one_mul_right`
- Truth anchor: `D5/S3/Arith/Lattices/CofactorKernel.cofactor_mulVec_eq_zero`
- Truth anchor: `D5/S3/Arith/Lattices/CofactorKernel.fromWeights`
- Truth anchor: `D5/S3/Arith/Lattices/CofactorKernel.fromWeights_apply`
- Truth anchor: `D5/S3/Arith/Lattices/CofactorKernel.fromWeights_minimal_of_primitive`
- Truth anchor: `D5/S3/Arith/Lattices/CofactorKernel.fromWeights_minimal_to_vector`
- Truth anchor: `D5/S3/Arith/Lattices/CofactorKernel.fromWeights_restrict`
- Truth anchor: `D5/S3/Arith/Lattices/CofactorKernel.fromWeights_support_subset`
- Truth anchor: `D5/S3/Arith/Lattices/CofactorKernel.kernel_cross_identity`
- Truth anchor: `D5/S3/Arith/Lattices/CofactorKernel.length_fromWeights`
- Truth anchor: `D5/S3/Arith/Lattices/CofactorKernel.lengths`
- Truth anchor: `D5/S3/Arith/Lattices/CofactorKernel.positive_kernel_orientation`
- Truth anchor: `D5/S3/Arith/Lattices/CofactorKernel.sequence_cofactor_length`
- Truth anchor: `D5/S3/Arith/Lattices/CofactorKernel.sequence_cofactor_multiplicities`
- Truth anchor: `D5/S3/Arith/Lattices/CofactorKernel.sum_cofactor_eq_det`
- Truth anchor: `D5/S3/Arith/Lattices/CofactorKernel.total_fromWeights_eq_mulVec`
