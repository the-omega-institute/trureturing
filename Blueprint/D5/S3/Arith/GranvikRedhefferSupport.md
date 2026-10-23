# Granvik's Redheffer support conjecture

## Abstract

A divisor-pair count refutes Granvik's twenty conjectured Redheffer support values.

**Definition 1.1 (The modified Redheffer matrix).**

$$\operatorname{B}\left(n, i, j\right)$$

*Formalization.* `D5/S3/Arith/GranvikRedhefferSupport.B` (`✓ std3`).

*Citation.* Mats Granvik (2008). *OEIS A145110, Number of elements in the Redheffer matrix that contribute to the Moebius function*. URL: <https://oeis.org/A145110>.

*Commentary.*

Rows and columns are the subtype of natural numbers in the closed interval from one to n. B(n,i,j) is one exactly when j=1 or i divides j, except that the entry (n,n) is zero. Every other entry is zero. This is the Möbius variant identified in A143104 and A008683. The n=8 support array in A145110 uses the transposed display convention.

**Definition 1.2 (The union of contributing positions).**

$$\operatorname{contributingPositions}\left(n\right)$$

*Formalization.* `D5/S3/Arith/GranvikRedhefferSupport.contributingPositions` (`✓ std3`).

*Citation.* Mats Granvik (2008). *OEIS A145110, Number of elements in the Redheffer matrix that contribute to the Moebius function*. URL: <https://oeis.org/A145110>.

*Commentary.*

A pair (i,j) belongs to this finite set if some actual permutation sigma of all row indices maps i to j and every B(n,k,sigma(k)) equals one. This is the union of positions of nonzero determinant terms, before their signs cancel; it is not the number of such permutations.

**Definition 1.3 (The number of contributing positions).**

$$\operatorname{a}\left(n\right) = \operatorname{card}\left(\operatorname{contributingPositions}\left(n\right)\right)$$

*Formalization.* `D5/S3/Arith/GranvikRedhefferSupport.a` (`✓ std3`).

*Citation.* Mats Granvik (2008). *OEIS A145110, Number of elements in the Redheffer matrix that contribute to the Moebius function*. URL: <https://oeis.org/A145110>.

*Commentary.*

The count uses the literal permutation-support definition. At n=1 this definition gives zero, whereas the entry lists one; the conjecture being refuted concerns only indices eleven through thirty.

**Definition 1.4 (The twenty published equalities).**

$$claim = \left(\operatorname{a}\left(11\right) = 11 \land \left(\operatorname{a}\left(12\right) = 23 \land \left(\operatorname{a}\left(13\right) = 13 \land \left(\operatorname{a}\left(14\right) = 18 \land \left(\operatorname{a}\left(15\right) = 19 \land \left(\operatorname{a}\left(16\right) = 25 \land \left(\operatorname{a}\left(17\right) = 17 \land \left(\operatorname{a}\left(18\right) = 29 \land \left(\operatorname{a}\left(19\right) = 19 \land \left(\operatorname{a}\left(20\right) = 30 \land \left(\operatorname{a}\left(21\right) = 26 \land \left(\operatorname{a}\left(22\right) = 26 \land \left(\operatorname{a}\left(23\right) = 23 \land \left(\operatorname{a}\left(24\right) = 45 \land \left(\operatorname{a}\left(25\right) = 27 \land \left(\operatorname{a}\left(26\right) = 30 \land \left(\operatorname{a}\left(27\right) = 32 \land \left(\operatorname{a}\left(28\right) = 39 \land \left(\operatorname{a}\left(29\right) = 29 \land \operatorname{a}\left(30\right) = 48\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Arith/GranvikRedhefferSupport.claim` (`✓ std3`).

*Citation.* Mats Granvik (2008). *OEIS A145110, Number of elements in the Redheffer matrix that contribute to the Moebius function*. URL: <https://oeis.org/A145110>.

*Commentary.*

OEIS A145110 attributes this exact list to Mats Granvik: “a(11) to a(30) are conjectured to be 11, 23, 13, 18, 19, 25, 17, 29, 19, 30, 26, 26, 23, 45, 27, 30, 32, 39, 29, 48.” The proposition claim is closed and conjoins all twenty equalities in this order.

**Theorem 1.5 (Refutation by the general support formula).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GranvikRedhefferSupport.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a145110-granvik-redheffer-support-refutation` (refuted) by `D5/S3/Arith/GranvikRedhefferSupport.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a145110-granvik-redheffer-support-refutation","declaration_gid":"D5/S3/Arith/GranvikRedhefferSupport.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Mats Granvik (2008). *OEIS A145110, Number of elements in the Redheffer matrix that contribute to the Moebius function*. URL: <https://oeis.org/A145110>.

*Acknowledgement.* Herbert S. Wilf (2004). *The Redheffer matrix of a partially ordered set*. DOI: [10.48550/arXiv.math/0408263](https://doi.org/10.48550/arXiv.math/0408263).

*Commentary.*

For every n at least two, the proof establishes a(n)=n−1+sum over d dividing n of (card(d.divisors)−1). The contributing positions are exactly the n−2 interior diagonal positions, the closing position (n,1), and the strict-divisibility positions (i,j) with i<j and i dividing j dividing n. An admissible permutation preserves the divisor set of n; a finite sum of nonnegative coordinate increments forces every nondivisor to be fixed. Each strict-divisibility edge is realized by a cycle through 1,i,j,n, omitting repeated endpoints, and every remaining index is fixed. Disjoint counting by the second coordinate gives the formula. This support-union identity is derived here; Wilf's Theorem 1 concerns the contributing permutations of the standard Redheffer matrix. At n=20 the divisor summands are 0,1,2,1,3,5, so a(20)=19+12=31, contradicting the conjectured value 30. The theorem has type Not claim. No bound on the Mertens function follows from this support count.

## References

- Truth anchor: `D5/S3/Arith/GranvikRedhefferSupport.B`
- Truth anchor: `D5/S3/Arith/GranvikRedhefferSupport.a`
- Truth anchor: `D5/S3/Arith/GranvikRedhefferSupport.claim`
- Truth anchor: `D5/S3/Arith/GranvikRedhefferSupport.contributingPositions`
- Truth anchor: `D5/S3/Arith/GranvikRedhefferSupport.result`
