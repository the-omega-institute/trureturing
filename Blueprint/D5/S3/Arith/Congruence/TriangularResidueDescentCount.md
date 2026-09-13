# The Triangular-Residue Descent Count

## Abstract

Kagey's descent count for the triangular-number permutation modulo a positive power of two.

**Definition 1.1 (Triangular residues).**

$$\forall n \in N, k \in N,\; T\left(n, k\right) = mod\left(\frac{k \cdot (k + 1)}{2}, 2^{n}\right)$$

*Formalization.* `D5/S3/Arith/Congruence/TriangularResidueDescentCount.T` (`✓ std3`).

*Citation.* Peter Kagey (2019). *OEIS A329278, Irregular table read by rows. The n-th row is the permutation of {0, 1, 2, ..., 2^n-1} given by T(n,k) = k(k+1)/2 (mod 2^n)*. URL: <https://oeis.org/A329278>.

*Commentary.*

For positive n and natural k, T(n,k) is the k-th triangular number reduced modulo 2^n, giving row n of A329278 with offset zero.

**Definition 1.2 (Adjacent strict descents).**

$$\forall n \in N,\; descents\left(n\right) = card\left(filter\left((k \mapsto T\left(n, k + 1\right) < T\left(n, k\right)), range\left(2^{n} - 1\right)\right)\right)$$

*Formalization.* `D5/S3/Arith/Congruence/TriangularResidueDescentCount.descents` (`✓ std3`).

*Citation.* Peter Kagey (2019). *OEIS A329278, Irregular table read by rows. The n-th row is the permutation of {0, 1, 2, ..., 2^n-1} given by T(n,k) = k(k+1)/2 (mod 2^n)*. URL: <https://oeis.org/A329278>.

*Commentary.*

For positive n, descents(n) counts the indices k from zero through 2^n-2 at which T(n,k) is strictly greater than T(n,k+1).

**Theorem 1.3 (Kagey's descent formula).**

$$\forall n \in N,\; 0 < n \Rightarrow descents\left(n\right) = 2^{n - 1} - 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/TriangularResidueDescentCount.kagey_a329278` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a329278-triangular-residue-descent-count` (proved) by `D5/S3/Arith/Congruence/TriangularResidueDescentCount.kagey_a329278`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a329278-triangular-residue-descent-count","declaration_gid":"D5/S3/Arith/Congruence/TriangularResidueDescentCount.kagey_a329278","resolution_kind":"proved"} -->

*Citation.* Peter Kagey (2019). *OEIS A329278, Irregular table read by rows. The n-th row is the permutation of {0, 1, 2, ..., 2^n-1} given by T(n,k) = k(k+1)/2 (mod 2^n)*. URL: <https://oeis.org/A329278>.

*Commentary.*

For positive n, put M=2^n and A(j)=j(j+1)/2. Induction on j at most M-1 shows that the number of descents before j is A(j) divided by M: both quantities increase by one exactly when the next residue wraps. At j=M-1, the terminal quotient is 2^(n-1)-1.

## References

- Truth anchor: `D5/S3/Arith/Congruence/TriangularResidueDescentCount.T`
- Truth anchor: `D5/S3/Arith/Congruence/TriangularResidueDescentCount.descents`
- Truth anchor: `D5/S3/Arith/Congruence/TriangularResidueDescentCount.kagey_a329278`
