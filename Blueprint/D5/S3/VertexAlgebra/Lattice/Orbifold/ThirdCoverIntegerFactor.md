# The Integral Grid of the Third Cover

## Abstract

An explicit polynomial tensor splitting identifies all integral-frequency oscillators and their Sugawara action.

Use the native full polynomial Fock space F over the complex numbers, with variable X_k at creation index -(k+1). Complement is the subtype of natural labels k for which three does not divide k+1, ComplementFock is its polynomial algebra, and SplitFock is F tensor ComplementFock. The split adapts the variable partition and derivative transport of LeechHalfFockTensorSplit, using the Mathlib polynomial tensor equivalence for a sum of variable types. All identities apply to arbitrary polynomials.

**Definition 1.1 (Integral-grid label).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverIntegerFactor.ordinaryVar`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverIntegerFactor.ordinaryVar` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The ordinary variable of index n is sent to the native variable of index 3n+2, whose creation frequency on the cover is -(n+1).

**Theorem 1.2 (Integral-grid labels are injective).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverIntegerFactor.ordinaryVar_injective`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverIntegerFactor.ordinaryVar_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equality of the affine labels implies equality of the natural indices. The derivative transport uses this injection.

**Theorem 1.3 (Integral-grid divisibility).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverIntegerFactor.dvd_ordinaryVar_succ`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverIntegerFactor.dvd_ordinaryVar_succ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Three divides ordinaryVar(n)+1 with quotient n+1. This excludes the complementary variables from that range and is used in the partition and both derivative arguments.

**Definition 1.4 (Partition of the native labels).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverIntegerFactor.variableSplit`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverIntegerFactor.variableSplit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

If three divides k+1, send k to the ordinary index k/3. Otherwise send k to the complementary subtype. The inverse uses ordinaryVar on the first summand and the subtype value on the second. Both inverse identities are proved.

**Definition 1.5 (Scaling the ordinary variables).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverIntegerFactor.scale`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverIntegerFactor.scale` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any complex a, substitute a times X_n for every ordinary variable X_n. When a is nonzero, scaling by its inverse gives the inverse substitution.

**Definition 1.6 (Joining the two polynomial factors).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverIntegerFactor.join`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverIntegerFactor.join` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For nonzero complex s, first substitute s inverse times the ordinary variables and leave the complement unchanged. Then use the polynomial tensor equivalence and inverse variable partition.

**Definition 1.7 (Splitting the full native space).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverIntegerFactor.split`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverIntegerFactor.split` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The inverse algebra equivalence of join identifies the full native Fock space with the ordinary and complementary polynomial factors.

**Theorem 1.8 (Joining arbitrary pure tensors).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverIntegerFactor.join_tmul`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverIntegerFactor.join_tmul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The image of P tensor Q is the product of the ordinary renaming of scale(s inverse)(P) and the complementary renaming of Q. The two tensor inclusions agree with the renamings on polynomial generators, and multiplying them gives the formula.

**Theorem 1.9 (Integral creation variable).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverIntegerFactor.join_X_tmul_one`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverIntegerFactor.join_X_tmul_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Joining X_n tensor 1 gives s inverse times X_(3n+2). This formula is used by the negative integral mode intertwining.

**Theorem 1.10 (Complementary creation variable).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverIntegerFactor.join_one_tmul_X`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverIntegerFactor.join_one_tmul_X` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Joining 1 tensor X_k gives the native X_(k.val). The complementary negative mode intertwining consumes this identity.

**Definition 1.11 (A particular scale).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverIntegerFactor.sqrtThree`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverIntegerFactor.sqrtThree` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Choose the complex image of the nonnegative real square root of three.

**Theorem 1.12 (Square of the chosen scale).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverIntegerFactor.sqrtThree_sq`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverIntegerFactor.sqrtThree_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The real square-root identity, transported to the complex numbers, proves that the chosen scale has square three. The complement’s commutator and spectrum proofs consume this identity.

**Theorem 1.13 (Nonzero square root).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverIntegerFactor.ne_zero_of_sq_eq_three`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverIntegerFactor.ne_zero_of_sq_eq_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every complex s with square three is nonzero, so the corresponding algebra equivalence and reciprocal scaling are defined.

**Theorem 1.14 (Integral native mode on a pure tensor).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverIntegerFactor.mode_join_tmul`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverIntegerFactor.mode_join_tmul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every s with s squared equal to three and every integer r, mode(3r) acting on join(P tensor Q) equals s times join(mode(r)(P) tensor Q). Positive modes differentiate only the ordinary factor and obtain the factor 3/s=s. Negative modes multiply by the corresponding variable and use the inverse scaling. The zero mode vanishes.

**Theorem 1.15 (Normal-ordered integral pairs).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverIntegerFactor.normalPair_join_tmul`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverIntegerFactor.normalPair_join_tmul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiplying both native mode indices by three preserves their order. The two integral-mode intertwiners multiply their scalar factors to three, giving three times the ordinary normal pair on P and leaving Q alone.

**Definition 1.16 (Integral part of the cover Sugawara operator).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverIntegerFactor.integerSugawara`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverIntegerFactor.integerSugawara` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Define the sum of normal pairs (3m-k,k) restricted to native indices divisible by three, times 1/6. The native support interval proves local finiteness of this restricted sum and permits its linear extension.

**Theorem 1.17 (Pointwise restricted sum).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverIntegerFactor.integerSugawara_apply`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverIntegerFactor.integerSugawara_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The defining action of integerSugawara(m) on P is one third of one half of the finsum of normalPair(3m-k,k)(P) over the multiples of three. The reindexing and complementary subtraction consume this defining formula.

**Theorem 1.18 (Ordinary Sugawara action on joined tensors).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverIntegerFactor.integerSugawara_join_tmul`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverIntegerFactor.integerSugawara_join_tmul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reindex the restricted sum by k=3j using injectivity of multiplication by three and its range. Each normal pair contributes a factor of three, which cancels the cover rescaling. Finite support permits moving the tensor inclusion through the sum, giving join(L(m)(P) tensor Q).

**Theorem 1.19 (Ordinary Virasoro action on all split states).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverIntegerFactor.split_integerSugawara`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverIntegerFactor.split_integerSugawara` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Tensor extensionality upgrades the pure-tensor calculation to the conjugation identity with L(m) on the ordinary factor and identity on the complement.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverIntegerFactor.dvd_ordinaryVar_succ`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverIntegerFactor.integerSugawara`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverIntegerFactor.integerSugawara_apply`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverIntegerFactor.integerSugawara_join_tmul`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverIntegerFactor.join`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverIntegerFactor.join_X_tmul_one`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverIntegerFactor.join_one_tmul_X`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverIntegerFactor.join_tmul`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverIntegerFactor.mode_join_tmul`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverIntegerFactor.ne_zero_of_sq_eq_three`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverIntegerFactor.normalPair_join_tmul`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverIntegerFactor.ordinaryVar`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverIntegerFactor.ordinaryVar_injective`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverIntegerFactor.scale`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverIntegerFactor.split`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverIntegerFactor.split_integerSugawara`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverIntegerFactor.sqrtThree`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverIntegerFactor.sqrtThree_sq`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverIntegerFactor.variableSplit`
- Dependency: [D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverVirasoro](ThirdCoverVirasoro.md)
