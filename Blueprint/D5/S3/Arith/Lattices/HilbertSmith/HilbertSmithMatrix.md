# Smith factors of the integer Hilbert matrix

## Abstract

Let L be positive and divisible by the least common multiple of 1 through 2n-1. The matrix has entries L/(i+j+1) for indices from zero through n-1. The gcds of the absolute determinants of its order-k minors, for k at most n, give positive Smith factors expressed by interval least common multiples.

**Theorem 1.1 (Cauchy formula for the actual integer minor).**

Lean statement: `D5/S3/Arith/Lattices/HilbertSmith/HilbertSmithMatrix.det_integerHilbertMinor_cast`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/HilbertSmith/HilbertSmithMatrix.det_integerHilbertMinor_cast` (`✓ std3`). ∎

*Citation.* Christian Krattenthaler (1999). *Advanced Determinant Calculus*. DOI: [10.48550/arXiv.math/9902004](https://doi.org/10.48550/arXiv.math/9902004). URL: <https://arxiv.org/abs/math/9902004>.

*Commentary.*

Put the chosen rows and columns in increasing order. The denominator-clearing hypothesis identifies each entry after rational casting with the scaled Cauchy entry. The determinant formula uses the ordinary row coordinates and the column coordinates shifted by one.

**Theorem 1.2 (Valuation of each actual integer minor).**

Lean statement: `D5/S3/Arith/Lattices/HilbertSmith/HilbertSmithMatrix.integerHilbertMinor_valuation`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/HilbertSmith/HilbertSmithMatrix.integerHilbertMinor_valuation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every prime, twice the exponent in the absolute determinant is the doubled scale term plus the sum of squared discrepancies between row and reflected column residue counts. The Cauchy determinant is positive at a positive scale.

**Theorem 1.3 (The order-zero divisor).**

Lean statement: `D5/S3/Arith/Lattices/HilbertSmith/HilbertSmithMatrix.determinantalDivisor_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/HilbertSmith/HilbertSmithMatrix.determinantalDivisor_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The determinant of the empty submatrix is one, and its absolute determinant is the sole input to the order-zero gcd.

**Theorem 1.4 (Nonzero determinantal divisors).**

Lean statement: `D5/S3/Arith/Lattices/HilbertSmith/HilbertSmithMatrix.determinantalDivisor_ne_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/HilbertSmith/HilbertSmithMatrix.determinantalDivisor_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an order at most the matrix size, taking the first k rows and columns gives an actual minor with positive determinant at the prescribed scale. Its gcd with the other absolute determinants is nonzero.

**Theorem 1.5 (Simultaneous attainment at each prime).**

Lean statement: `D5/S3/Arith/Lattices/HilbertSmith/HilbertSmithMatrix.exists_integerHilbertMinor_minimizer`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/HilbertSmith/HilbertSmithMatrix.exists_integerHilbertMinor_minimizer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a prime p and let e be the base-p logarithm of 2n-1. A single pair of row and column sets of size k attains the bound at every layer up to e. Its prime exponent is k times the difference between the scale exponent and e, plus the sum over positive layers of the positive part of k minus capacity.

**Theorem 1.6 (Prime exponents of the actual gcd).**

Lean statement: `D5/S3/Arith/Lattices/HilbertSmith/HilbertSmithMatrix.determinantalDivisor_factorization`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/HilbertSmith/HilbertSmithMatrix.determinantalDivisor_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exponent in the gcd is the minimum exponent of the absolute determinants. The layer bounds hold for every minor, and the simultaneous minimizer realizes their sum in one minor for the chosen prime.

**Theorem 1.7 (Recurrence of determinantal divisors).**

Lean statement: `D5/S3/Arith/Lattices/HilbertSmith/HilbertSmithMatrix.determinantalDivisor_succ`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/HilbertSmith/HilbertSmithMatrix.determinantalDivisor_succ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The divisor at order k+1 is the divisor at order k multiplied by the scale divided by the least common multiple from k+1 through 2n-k-1. The prime exponent increments give the recurrence by unique factorization.

**Theorem 1.8 (Exact Smith factor).**

Lean statement: `D5/S3/Arith/Lattices/HilbertSmith/HilbertSmithMatrix.smithFactor_eq_intervalLCM`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/HilbertSmith/HilbertSmithMatrix.smithFactor_eq_intervalLCM` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an order k between one and n, the quotient of the order-k divisor by its predecessor is the scale divided by the least common multiple of the integers from k through 2n-k.

**Theorem 1.9 (Positive divisibility chain).**

Lean statement: `D5/S3/Arith/Lattices/HilbertSmith/HilbertSmithMatrix.smithFactor_pos_and_dvd`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/HilbertSmith/HilbertSmithMatrix.smithFactor_pos_and_dvd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The symmetric intervals shrink with increasing order. Their least common multiples divide the scale and each divides the preceding one, so the positive scale quotients divide all later quotients.

## References

- Truth anchor: `D5/S3/Arith/Lattices/HilbertSmith/HilbertSmithMatrix.det_integerHilbertMinor_cast`
- Truth anchor: `D5/S3/Arith/Lattices/HilbertSmith/HilbertSmithMatrix.determinantalDivisor_factorization`
- Truth anchor: `D5/S3/Arith/Lattices/HilbertSmith/HilbertSmithMatrix.determinantalDivisor_ne_zero`
- Truth anchor: `D5/S3/Arith/Lattices/HilbertSmith/HilbertSmithMatrix.determinantalDivisor_succ`
- Truth anchor: `D5/S3/Arith/Lattices/HilbertSmith/HilbertSmithMatrix.determinantalDivisor_zero`
- Truth anchor: `D5/S3/Arith/Lattices/HilbertSmith/HilbertSmithMatrix.exists_integerHilbertMinor_minimizer`
- Truth anchor: `D5/S3/Arith/Lattices/HilbertSmith/HilbertSmithMatrix.integerHilbertMinor_valuation`
- Truth anchor: `D5/S3/Arith/Lattices/HilbertSmith/HilbertSmithMatrix.smithFactor_eq_intervalLCM`
- Truth anchor: `D5/S3/Arith/Lattices/HilbertSmith/HilbertSmithMatrix.smithFactor_pos_and_dvd`
- Dependency: [D5/S3/Arith/Lattices/HilbertSmith/CauchyDeterminant](CauchyDeterminant.md)
- Dependency: [D5/S3/Arith/Lattices/HilbertSmith/DivisorFormula](DivisorFormula.md)
- Dependency: [D5/S3/Arith/Lattices/HilbertSmith/MinorValuation](MinorValuation.md)
