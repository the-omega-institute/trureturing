# Normalized zero-branch digit of the golden cubic

## Abstract

The first normalized digit of the later zero branch gives the earlier block unit up to a cube.

**Theorem 1.1 (The later zero-branch digit reads the earlier cube class).**

Lean statement: `D5/S3/Arith/Primes/GoldenCubicNormalizedZeroDigit.native_residue_cube_readout`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/GoldenCubicNormalizedZeroDigit.native_residue_cube_readout` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take a prime p greater than three and a positive index i with L_(3^i)^2 + 3 = p^h u, h positive. The unique zero-marked root modulo p^(h+1) of the actual cubic at level i+1+k has a representative p^h v. The residue of v modulo p is independent of that representative.

In the finite residue field the normalized observation -3 times the inverse of 3^k times v equals the cube of the unit 2 L_(3^i), multiplied by u times the inverse of twelve. Thus the observation is a cube exactly when u divided by twelve is a cube. For the exact depth, p does not divide u, so this is a nonzero cube class.

The construction consumes the actual marked root from GoldenCubicMarkedFibonacciDepth and uses the native recurrence and elementary cubic linearization. It is a finite residue result, not a formal p-adic Kummer classification, conductor reciprocity theorem or Wall-Sun-Sun exclusion.

## References

- Truth anchor: `D5/S3/Arith/Primes/GoldenCubicNormalizedZeroDigit.native_residue_cube_readout`
- Dependency: [D5/S3/Arith/Primes/GoldenCubicMarkedFibonacciDepth](GoldenCubicMarkedFibonacciDepth.md)
