# Indecomposable Permutations and Kurkov's Double Array

## Abstract

The actual indecomposable-permutation count is the common exact left border of Kurkov's two arrays.

All indices are natural numbers. A permutation of Fin n is indecomposable when no proper nonempty initial interval is invariant. The two arrays are defined independently by their exact source recurrences; the count is not replaced by a recurrence-defined proxy.

**Definition 1.1 (Indecomposable permutations).**

Lean statement: `D5/S1/Recurrence/Algebraic/IndecomposablePermutationDoubleArray.IndecomposablePerm`

*Formalization.* `D5/S1/Recurrence/Algebraic/IndecomposablePermutationDoubleArray.IndecomposablePerm` (`✓ std3`).

*Citation.* Mikhail Kurkov (2024). *OEIS A003319 and Kurkov's A370380/A370381 double-array conjecture*. URL: <https://oeis.org/A003319>.

*Commentary.*

For each n, this subtype contains exactly the permutations p of Fin n for which no k with 0<k<n preserves membership in the initial segment {0,...,k-1}. Translating Fin n by one gives the source convention on permutations of {1,...,n}.

**Definition 1.2 (The actual permutation count).**

Lean statement: `D5/S1/Recurrence/Algebraic/IndecomposablePermutationDoubleArray.c`

*Formalization.* `D5/S1/Recurrence/Algebraic/IndecomposablePermutationDoubleArray.c` (`✓ std3`).

*Citation.* Mikhail Kurkov (2024). *OEIS A003319 and Kurkov's A370380/A370381 double-array conjecture*. URL: <https://oeis.org/A003319>.

*Commentary.*

The value c(n) is the finite cardinality of IndecomposablePerm(n). In particular, its meaning comes from the source permutation class rather than either triangular recurrence.

**Definition 1.3 (Kurkov's first array).**

Lean statement: `D5/S1/Recurrence/Algebraic/IndecomposablePermutationDoubleArray.U`

*Formalization.* `D5/S1/Recurrence/Algebraic/IndecomposablePermutationDoubleArray.U` (`✓ std3`).

*Citation.* Mikhail Kurkov (2024). *OEIS A003319 and Kurkov's A370380/A370381 double-array conjecture*. URL: <https://oeis.org/A003319>.

*Commentary.*

The initial row is U(0,k)=1. The successor recurrence is U(m+1,k)=(k+2)U(m,k+1)+sum_{j=0}^{k} U(m,j), with the displayed finite sum represented by range(k+1). This is OEIS A370380.

**Definition 1.4 (Kurkov's second array).**

Lean statement: `D5/S1/Recurrence/Algebraic/IndecomposablePermutationDoubleArray.V`

*Formalization.* `D5/S1/Recurrence/Algebraic/IndecomposablePermutationDoubleArray.V` (`✓ std3`).

*Citation.* Mikhail Kurkov (2024). *OEIS A003319 and Kurkov's A370380/A370381 double-array conjecture*. URL: <https://oeis.org/A003319>.

*Commentary.*

The initial row is V(0,k)=1. The successor recurrence is V(m+1,k)=sum_{j=0}^{k+1} binomial(k+2,j+1)V(m,j), represented by range(k+2). This is OEIS A370381.

**Theorem 1.5 (Kurkov's double-array conjecture).**

Lean statement: `D5/S1/Recurrence/Algebraic/IndecomposablePermutationDoubleArray.result`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/IndecomposablePermutationDoubleArray.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a003319-kurkov-double-array` (proved) by `D5/S1/Recurrence/Algebraic/IndecomposablePermutationDoubleArray.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a003319-kurkov-double-array","declaration_gid":"D5/S1/Recurrence/Algebraic/IndecomposablePermutationDoubleArray.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Mikhail Kurkov (2024). *OEIS A003319 and Kurkov's A370380/A370381 double-array conjecture*. URL: <https://oeis.org/A003319>.

*Commentary.*

There is one empty and one singleton indecomposable permutation. For n>=2, the theorem proves c(n)=U(n-2,0)=V(n-2,0). For the actual count, the least positive invariant prefix gives a proved equivalence between a permutation and its first indecomposable block together with the remaining permutation. Cardinality yields the factorial convolution. Partial sums and rising factorials give the same convolution for U. For V, a finite Nat-valued binomial operator is iterated on a shifted row, a delta sequence and power sequences; its unrolling gives the third convolution. Unit-diagonal triangular uniqueness then identifies both borders with the actual count. All auxiliary identities remain local to this theorem.

## References

- Truth anchor: `D5/S1/Recurrence/Algebraic/IndecomposablePermutationDoubleArray.IndecomposablePerm`
- Truth anchor: `D5/S1/Recurrence/Algebraic/IndecomposablePermutationDoubleArray.U`
- Truth anchor: `D5/S1/Recurrence/Algebraic/IndecomposablePermutationDoubleArray.V`
- Truth anchor: `D5/S1/Recurrence/Algebraic/IndecomposablePermutationDoubleArray.c`
- Truth anchor: `D5/S1/Recurrence/Algebraic/IndecomposablePermutationDoubleArray.result`
