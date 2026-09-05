# Finite Atomic Hankel-Vandermonde Factorization

## Abstract

Finite atomic Hankel moment matrices, their one-step shift, and their pencil factor through one shared Vandermonde feature matrix with diagonal atomic weights.

**Definition 1.1 (Finite atomic moment).**

Lean statement: `D5/S3/Weil/Pick/FiniteAtomicHankelVandermonde.atomicMoment`

*Formalization.* `D5/S3/Weil/Pick/FiniteAtomicHankelVandermonde.atomicMoment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The weighted finite power sum of the atomic nodes.

**Definition 1.2 (Vandermonde feature matrix).**

Lean statement: `D5/S3/Weil/Pick/FiniteAtomicHankelVandermonde.vandermondeFeatureMatrix`

*Formalization.* `D5/S3/Weil/Pick/FiniteAtomicHankelVandermonde.vandermondeFeatureMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Rows are moment degrees and columns are atomic nodes.

**Definition 1.3 (Hankel moment matrix).**

Lean statement: `D5/S3/Weil/Pick/FiniteAtomicHankelVandermonde.hankelMomentMatrix`

*Formalization.* `D5/S3/Weil/Pick/FiniteAtomicHankelVandermonde.hankelMomentMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Entry i,j is the atomic moment of degree i plus j.

**Definition 1.4 (Shifted Hankel moment matrix).**

Lean statement: `D5/S3/Weil/Pick/FiniteAtomicHankelVandermonde.shiftedHankelMomentMatrix`

*Formalization.* `D5/S3/Weil/Pick/FiniteAtomicHankelVandermonde.shiftedHankelMomentMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Entry i,j is the atomic moment of degree i plus j plus one.

**Definition 1.5 (Hankel moment pencil).**

Lean statement: `D5/S3/Weil/Pick/FiniteAtomicHankelVandermonde.hankelMomentPencil`

*Formalization.* `D5/S3/Weil/Pick/FiniteAtomicHankelVandermonde.hankelMomentPencil` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite atomic pencil with diagonal weight w(a)(x(a)-lambda).

**Theorem 1.6 (The Hankel matrix has a Vandermonde factorization).**

$$\operatorname{H}(w, x) = \operatorname{V}(x)\cdot\operatorname{D}(w)\cdot\operatorname{V}(x)^{T}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Pick/FiniteAtomicHankelVandermonde.hankel_moment_matrix_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Expanding matrix multiplication and the diagonal weight matrix leaves one finite atomic sum; multiplication of node powers adds the two degrees.

**Theorem 1.7 (The shifted Hankel matrix has the same features).**

$$H^{+}(w, x) = \operatorname{V}(x)\cdot\operatorname{D}(w\cdot x)\cdot\operatorname{V}(x)^{T}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Pick/FiniteAtomicHankelVandermonde.shifted_hankel_moment_matrix_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The one-step moment shift is absorbed entirely into the diagonal atomic weight by multiplication with the node.

**Theorem 1.8 (The pencil is shifted minus lambda times unshifted).**

$$\operatorname{P}(\lambda) = H^{+}-\lambda\cdot H$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Pick/FiniteAtomicHankelVandermonde.hankel_moment_pencil_eq_shifted_sub` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The identity is entrywise and requires no rank or distinctness hypothesis.

**Theorem 1.9 (The Hankel pencil has a shifted diagonal factorization).**

$$\operatorname{P}(\lambda) = \operatorname{V}(x)\cdot\operatorname{D}(w\cdot(x-\lambda))\cdot\operatorname{V}(x)^{T}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Pick/FiniteAtomicHankelVandermonde.hankel_moment_pencil_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The factorization exposes the same localizing coordinate x minus lambda that appears in the finite Stieltjes mass-support pencil.

## References

- Truth anchor: `D5/S3/Weil/Pick/FiniteAtomicHankelVandermonde.atomicMoment`
- Truth anchor: `D5/S3/Weil/Pick/FiniteAtomicHankelVandermonde.hankelMomentMatrix`
- Truth anchor: `D5/S3/Weil/Pick/FiniteAtomicHankelVandermonde.hankelMomentPencil`
- Truth anchor: `D5/S3/Weil/Pick/FiniteAtomicHankelVandermonde.hankel_moment_matrix_factorization`
- Truth anchor: `D5/S3/Weil/Pick/FiniteAtomicHankelVandermonde.hankel_moment_pencil_eq_shifted_sub`
- Truth anchor: `D5/S3/Weil/Pick/FiniteAtomicHankelVandermonde.hankel_moment_pencil_factorization`
- Truth anchor: `D5/S3/Weil/Pick/FiniteAtomicHankelVandermonde.shiftedHankelMomentMatrix`
- Truth anchor: `D5/S3/Weil/Pick/FiniteAtomicHankelVandermonde.shifted_hankel_moment_matrix_factorization`
- Truth anchor: `D5/S3/Weil/Pick/FiniteAtomicHankelVandermonde.vandermondeFeatureMatrix`
