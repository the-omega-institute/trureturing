# Interval least common multiples and prime exponents

## Abstract

Reflected matching capacity determines the prime exponents of successive interval least common multiple quotients.

**Theorem 1.1 (Attained sum of layer bounds).**

Lean statement: `D5/S3/Arith/Lattices/HilbertSmith/DivisorFormula.residueLoss_sum_minimum`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/HilbertSmith/DivisorFormula.residueLoss_sum_minimum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Sum the layerwise lower bounds for two index sets of size k. The nested residue minimizer attains all the bounds with one pair, so the sum of bounds is the minimum.

**Theorem 1.2 (Positive interval least common multiple).**

Lean statement: `D5/S3/Arith/Lattices/HilbertSmith/DivisorFormula.intervalLCM_ne_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/HilbertSmith/DivisorFormula.intervalLCM_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every member of the symmetric interval is positive when its lower endpoint is positive. Its least common multiple is then nonzero, with value one for an empty interval.

**Theorem 1.3 (Divisibility of the interval least common multiples).**

Lean statement: `D5/S3/Arith/Lattices/HilbertSmith/DivisorFormula.intervalLCM_dvd_of_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/HilbertSmith/DivisorFormula.intervalLCM_dvd_of_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Increasing the lower endpoint of the symmetric interval also decreases the upper endpoint. The least common multiple over the smaller interval divides the one over the larger interval.

**Theorem 1.4 (Prime powers in the denominator-clearing scale).**

Lean statement: `D5/S3/Arith/Lattices/HilbertSmith/DivisorFormula.height_le_factorization`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/HilbertSmith/DivisorFormula.height_le_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive n, the largest power of p at most 2n minus one is among the numbers whose least common multiple divides the scale. The base-p logarithm of that endpoint therefore bounds the scale exponent from below.

**Theorem 1.5 (Capacity and multiples in the symmetric interval).**

Lean statement: `D5/S3/Arith/Lattices/HilbertSmith/DivisorFormula.le_capacity_iff_exists_dvd`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/HilbertSmith/DivisorFormula.le_capacity_iff_exists_dvd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive q and k at most n, the capacity at modulus q is at least k exactly when the interval from k through 2n minus k contains a multiple of q. The distance from n to its closest multiple is the minimum of the distances to the adjacent multiples given by the quotient and remainder of n by q.

**Theorem 1.6 (Prime exponent of the interval least common multiple).**

Lean statement: `D5/S3/Arith/Lattices/HilbertSmith/DivisorFormula.intervalLCM_factorization`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/HilbertSmith/DivisorFormula.intervalLCM_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 1 ≤ k ≤ n, the exponent counts the layers from one through the cutoff at which capacity is at least k. Divisibility of an interval least common multiple by a prime power is equivalent to divisibility of some member of the interval by that power.

**Theorem 1.7 (Increment of the divisor exponent).**

Lean statement: `D5/S3/Arith/Lattices/HilbertSmith/DivisorFormula.divisorExponent_succ_eq_intervalLCM`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/HilbertSmith/DivisorFormula.divisorExponent_succ_eq_intervalLCM` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Raising the order from k to k+1 adds one for each layer whose capacity is below k+1, together with the scale exponent minus the logarithmic cutoff. The complementary layers count the exponent in the interval least common multiple.

## References

- Truth anchor: `D5/S3/Arith/Lattices/HilbertSmith/DivisorFormula.divisorExponent_succ_eq_intervalLCM`
- Truth anchor: `D5/S3/Arith/Lattices/HilbertSmith/DivisorFormula.height_le_factorization`
- Truth anchor: `D5/S3/Arith/Lattices/HilbertSmith/DivisorFormula.intervalLCM_dvd_of_le`
- Truth anchor: `D5/S3/Arith/Lattices/HilbertSmith/DivisorFormula.intervalLCM_factorization`
- Truth anchor: `D5/S3/Arith/Lattices/HilbertSmith/DivisorFormula.intervalLCM_ne_zero`
- Truth anchor: `D5/S3/Arith/Lattices/HilbertSmith/DivisorFormula.le_capacity_iff_exists_dvd`
- Truth anchor: `D5/S3/Arith/Lattices/HilbertSmith/DivisorFormula.residueLoss_sum_minimum`
- Dependency: [D5/S3/Arith/Lattices/HilbertSmith/NestedResidueMatching](NestedResidueMatching.md)
