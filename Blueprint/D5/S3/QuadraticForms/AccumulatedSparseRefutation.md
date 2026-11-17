# Accumulated sparse quadratic errors

## Abstract

An equicorrelated positive semidefinite Euclidean contraction has accumulated best sparse squared errors exceeding one.

**Theorem 1.1 (The quadratic form).**

$$\forall (y : Euclidean\left(64\right)), Q\left(y\right) = \frac{A\left(y\right) + B\left(y\right)^{2}}{128}$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/AccumulatedSparseRefutation.quadratic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ekene E. (2026). *A bound on accumulated PSD contractions, revision 2*. URL: <https://mathoverflow.net/revisions/509794/2>.

*Commentary.*

For every real 64-coordinate vector y, let A(y) be the sum of its coordinate squares and B(y) the sum of its coordinates. For K=(I+J)/128, Q(y)=y-transpose K y=(A(y)+B(y)^2)/128. The Euclidean norm is used throughout.

**Theorem 1.2 (The actual attained minimum).**

$$\forall (d : Nat), 1 \le d \le 64 \Rightarrow IsLeast\left(E\left(d\right), t\left(d\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/AccumulatedSparseRefutation.sparse_minimum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ekene E. (2026). *A bound on accumulated PSD contractions, revision 2*. URL: <https://mathoverflow.net/revisions/509794/2>.

*Commentary.*

Here E(d) is the set of all values (x-z)-transpose K(x-z) with z real and at most d nonzero coordinates, x_i=1/8, and t(d)=65(64-d)/(8192(d+1)). There is no sign or magnitude restriction on z. Cauchy--Schwarz on the actual nonzero support gives the universal lower bound. On any d-element coordinate subset, z_i=65/(8(d+1)) and zero elsewhere attains it. Smaller supports, negative coefficients and cancellations are all included.

**Theorem 1.3 (Accumulation exceeds one).**

$$1 < T$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/AccumulatedSparseRefutation.accumulation_gt_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ekene E. (2026). *A bound on accumulated PSD contractions, revision 2*. URL: <https://mathoverflow.net/revisions/509794/2>.

*Commentary.*

T is the sum of t(d) for d from 1 through 63, on the same fixed matrix and vector. Its strict inequality is an exact rational calculation. No errors from different matrices or incompatible vectors are combined.

**Theorem 1.4 (The full finite assertion is false).**

$$\neg P$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/AccumulatedSparseRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/mathoverflow-509794-accumulated-sparse-errors` (refuted) by `D5/S3/QuadraticForms/AccumulatedSparseRefutation.result` and `D5/S3/HilbertOperators/Approximation/AccumulatedSupportRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"mathoverflow-509794-accumulated-sparse-errors","declaration_gid":"D5/S3/QuadraticForms/AccumulatedSparseRefutation.result","resolution_kind":"refuted"} -->

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"mathoverflow-509794-accumulated-sparse-errors","declaration_gid":"D5/S3/HilbertOperators/Approximation/AccumulatedSupportRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Ekene E. (2026). *A bound on accumulated PSD contractions, revision 2*. URL: <https://mathoverflow.net/revisions/509794/2>.

*Commentary.*

P denotes the original universal finite assertion: for every positive integer m, every real symmetric positive semidefinite Euclidean contraction K, and every nonnegative Euclidean unit vector x with K_ii at most x_i squared, the sum from d=1 to m-1 of the actual minimum over all real z of support cardinality at most d is at most one. The closed Lean definition claim quantifies over the full original domain. Its sum-of-coordinate-squares contraction condition is equivalent to the Euclidean operator contraction condition.

The matrix K=(I+J)/128 and x_i=1/8 satisfy these hypotheses in dimension 64. The diagonal equals x_i squared. The quadratic identity proves positivity. Cauchy--Schwarz bounds the squared norm of Ky by (65/128)^2 times the squared norm of y, hence by the squared norm of y. The IsLeast theorem proves nonemptiness, a lower bound and attainment of every source error used in the sum. Thus the real infimum is an actual minimum, and T>1 contradicts P.

Ekene E. posed both assertions in MathOverflow 509794 revision 2, licensed CC BY-SA 4.0. The finite and Hilbert negations are separate members of one source event. The shared component of the equicorrelated geometry leaves errors that accumulate across sparsity levels.

## References

- Truth anchor: `D5/S3/QuadraticForms/AccumulatedSparseRefutation.accumulation_gt_one`
- Truth anchor: `D5/S3/QuadraticForms/AccumulatedSparseRefutation.quadratic`
- Truth anchor: `D5/S3/QuadraticForms/AccumulatedSparseRefutation.result`
- Truth anchor: `D5/S3/QuadraticForms/AccumulatedSparseRefutation.sparse_minimum`
