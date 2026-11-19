# Prime logarithms and irrational rotation

## Abstract

Positive-tail density of prime logarithmic lattices.

**Theorem 1.1 (Incommensurable prime logarithms).**

Lean statement: `D5/S3/Arith/Robin/Analytic/LcmPowerLogLattice.irrational_prime_log_ratio`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/LcmPowerLogLattice.irrational_prime_log_ratio` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For natural primes p and q with p different from q, the real number log(p)/log(q) is irrational. A positive rational equality would give p^d=q^n for positive integers d and n. Primality would then force p=q.

**Theorem 1.2 (Every open interval meets every positive tail).**

Lean statement: `D5/S3/Arith/Robin/Analytic/LcmPowerLogLattice.positive_tail_lattice`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/LcmPowerLogLattice.positive_tail_lattice` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a,b,u,v be real with a>0, b>0, u<v and a/b irrational. For every natural N there exist natural i and j with N<=i, N<=j and u<i*a-j*b<v. Irrational rotation on the circle of length b visits the image of (u,v) infinitely often along natural indices. Choose such an i large enough that i*a>N*b+v, and lift the circle identity to an integer j. The upper bound v forces j>N.

**Theorem 1.3 (Distinct prime logarithms).**

Lean statement: `D5/S3/Arith/Robin/Analytic/LcmPowerLogLattice.prime_log_lattice_tail`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/LcmPowerLogLattice.prime_log_lattice_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For natural primes p!=q, real u<v and natural N, there exist natural i,j>=N with u<i*log(p)-j*log(q)<v. This directly applies the two preceding results with a=log(p) and b=log(q). The collision density argument uses this statement to keep the logarithmic difference between two fixed strict endpoint bounds while both exponents grow.

## References

- Truth anchor: `D5/S3/Arith/Robin/Analytic/LcmPowerLogLattice.irrational_prime_log_ratio`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/LcmPowerLogLattice.positive_tail_lattice`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/LcmPowerLogLattice.prime_log_lattice_tail`
