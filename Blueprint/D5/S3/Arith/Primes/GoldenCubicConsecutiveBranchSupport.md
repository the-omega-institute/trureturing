# Cyclotomic support of consecutive Fibonacci-compatible cubic labels

## Abstract

The consecutive cubic-label branch loci are private simple cyclotomic divisors.

**Theorem 1.1 (Consecutive marking has exact torsion support, without collisions).**

Lean statement: `D5/S3/Arith/Primes/GoldenCubicConsecutiveBranchSupport.consecutive_branch_support`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/GoldenCubicConsecutiveBranchSupport.consecutive_branch_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the Fibonacci conic, the Laurent parameter a projects to x=a minus its inverse. The cubic Lucas recurrence then comes from cubing a. For each depth i the excluded locus x squared equals minus three is precisely where a squared has exact multiplicative order three to the i plus one.

For a word of length k the union is the nontrivial three-to-the-k torsion of a squared. The product of the level factors, multiplied by a squared minus one, gives the exact division-free torsion equation. In the x coordinate, marked zeros have nonzero linear coefficient; no point is marked at two levels, and no marked point lies above a branch value of the conic projection.

This is the algebraic support input for a Kummer cover. The cover, its geometric genus, Hasse-Weil bounds, and distribution along one native Lucas orbit are not formalized here.

## References

- Truth anchor: `D5/S3/Arith/Primes/GoldenCubicConsecutiveBranchSupport.consecutive_branch_support`
