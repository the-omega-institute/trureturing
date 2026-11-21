# Jacobi products on an affine progression

## Abstract

Incomplete tuple averages and complete power moments for Jacobi symbols

Fix a finite set P of odd primes and let Q be their product. Fix natural b and m with b congruent to 3 modulo 4 and m divisible by 4. For every index i let d(i) = b + mi. All sums over interval indices start at a natural A and have a natural length L.

**Theorem 1.1 (Discrepancy for tuples with repeated primes).**

$$\operatorname{abs}\left(\operatorname{S}\left(A, L\right)-L M\right) \le 2 U$$

*Proof.* Machine-checked in Lean as `D5/S3/CharacterSums/JacobiTupleInterval.tuple_interval_mean` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a tuple f of any natural length with entries in P, take the product of the Jacobi symbols (f(j)/d(i)) at each index i. S(A,L) sums those products over A ≤ i < A+L, M = S(0,Q)/Q is the complete average, and U is the product of the entries with multiplicity.

Let R be the product of the distinct entries of the tuple. Reciprocity shows that R is a period, also when a prime divides the stride. Since R divides Q, both complete averages coincide. Removing complete blocks from the interval leaves two terms, each bounded in absolute value by L modulo R. The product R is at most U.

For the power-moment identity also assume that m is coprime to every prime in P. Choose arbitrary real coefficients a(p) and a natural exponent e. For p in P write χ(p,z) for the quadratic character of the field modulo p, multiplied by −1 if p is 3 modulo 4 and by 1 otherwise.

**Theorem 1.2 (Complete power moments over independent residue coordinates).**

$$\operatorname{B}\left(A, e\right) = \operatorname{G}\left(e\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/CharacterSums/JacobiTupleInterval.affine_complete_crt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

B(A,e) sums the e-th power of the weighted sum of (p/d(i)) over a block of Q indices beginning at A. G(e) sums the e-th power of the weighted sum of χ(p,z(p)) over all tuples of residue coordinates z, with one independent field coordinate modulo each prime p.

The affine map sending an index to its denominator permutes residues modulo Q. The Chinese remainder theorem transports this permutation to the product of the prime fields. Reciprocity identifies each summand after that change of variables.

**Theorem 1.3 (Values and mean of one signed coordinate).**

$$\operatorname{range}\left(c\right) \subseteq \{-1,0,1\} \land \operatorname{sum}\left(c\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/CharacterSums/JacobiTupleInterval.coordinate_laws` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here c denotes the signed character for the fixed odd prime p. The range and sum are taken over its entire field. The Jacobi symbol takes values −1, 0, 1. The quadratic character on an odd prime field has zero sum, and multiplication by its fixed reciprocity sign preserves both properties.

## References

- Truth anchor: `D5/S3/CharacterSums/JacobiTupleInterval.affine_complete_crt`
- Truth anchor: `D5/S3/CharacterSums/JacobiTupleInterval.coordinate_laws`
- Truth anchor: `D5/S3/CharacterSums/JacobiTupleInterval.tuple_interval_mean`
