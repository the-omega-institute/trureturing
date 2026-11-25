# Golden cubic nonbranch minimal periods

## Abstract

Determine the least lifted period of a nonbranch periodic residue for the golden cubic trace.

**Theorem 1.1 (Exact nonbranch periods at every prime-power precision).**

Lean statement: `D5/S3/Arith/Primes/GoldenCubicNonbranchReturn.nonbranch_minimal_period`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/GoldenCubicNonbranchReturn.nonbranch_minimal_period` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a prime p greater than three and an integer starting trace y whose residue is periodic for x ↦ x³ + 3x and whose discriminant y² + 4 is nonzero modulo p. Let ℓ be the actual least period of that residue.

The least period either stays ℓ at every positive precision s, or one positive integer d and a single signed multiplier μ = ±3^ℓ work simultaneously for all s. The least period modulo p^s is then ℓ times the multiplicative order of μ in Z/(p^(max(s−d,0))). Modulus one has order one.

The proof works directly in the rank-two quadratic coefficient algebra, so the periodic nonbranch residue need not split over the residue field. Branch residues, transient starting residues, and the original Wall–Sun–Sun exclusion are not claimed.

## References

- Truth anchor: `D5/S3/Arith/Primes/GoldenCubicNonbranchReturn.nonbranch_minimal_period`
