# Weight Concentration at a Prime Power

## Abstract

An integral basis concentrates a weight vector modulo a prime power.

**Theorem 1.1 (Concentrating the insertion weights).**

Lean statement: `D5/S3/Combinatorics/Matroids/PrimePowerPivotBasis.primary_pivot_basis`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/PrimePowerPivotBasis.primary_pivot_basis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite basis with natural weights, at least one of which is nonzero, and a positive prime power, choose an index of nonzero weight. Change only that basis vector. Its weighted value agrees with the original weighted vector modulo a multiple of the prime power. The proof extracts the weight gcd and uses a coordinate whose normalized weight is a unit in the residue ring.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/PrimePowerPivotBasis.primary_pivot_basis`
