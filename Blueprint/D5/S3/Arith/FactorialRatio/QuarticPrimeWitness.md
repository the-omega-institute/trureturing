# Quartic compact factorial gcd

## Abstract

A selected family member for each prime

**Theorem 1.1 (A selected family member for each prime).**

Lean statement: `D5/S3/Arith/FactorialRatio/QuarticPrimeWitness.quartic_prime_witness`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/QuarticPrimeWitness.quartic_prime_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At s=(r-1)(r-2), the zero parameter bounds the small-prime exponent excess by 3(r-1) times the integer base-p logarithm of r. For r<p<=s, Dirichlet approximation or the parameter floor(p/r) gives an admissible member. The paired floors telescope to a residue count. Folding the last quotient bin into the first bounds that count by a sum of integer interval lengths. Only the first prime power contributes, with excess at most 4r/sqrt(p). For p>s the zero parameter gives exponent zero.

## References

- Truth anchor: `D5/S3/Arith/FactorialRatio/QuarticPrimeWitness.quartic_prime_witness`
- Dependency: [D5/S3/Arith/FactorialRatio/CompactFactorialGcd](CompactFactorialGcd.md)
