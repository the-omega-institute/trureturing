# Prime weights and integer transport of a signed contact graph

## Abstract

Prime weights and integer transport of a signed contact graph

**Theorem 1.1 (A connected real kernel has rational coordinate ratios).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/PrimeContactTransport.normalize_real_kernel`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/PrimeContactTransport.normalize_real_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A two-contact row transports one column coefficient to another by a signed ratio of coordinate weights. With rational nonzero weights, a connected real solution divided by its nonzero root value has rational, nowhere-zero coordinates.

**Theorem 1.2 (Distinct primes detect the integer exponent potential).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/PrimeContactTransport.real_prime_kernel_iff_potential`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/PrimeContactTransport.real_prime_kernel_iff_potential` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use pairwise distinct primes as coordinate weights. Valuation at each of these primes sends multiplication of nonzero rational numbers to addition of integers and sends the corresponding prime to its coordinate basis vector. Along a two-contact row the potential gains the source axis and loses the target axis. The sign of the rational coordinate gives the simultaneous transport of the two-element multiplicative sign group.

Conversely, the signed integer potential gives a nonzero kernel by evaluating the Laurent monomial attached to each column.

**Theorem 1.3 (One prime specialization gives the uniform Laurent family).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/PrimeContactTransport.exists_laurent_kernel_of_real_prime_kernel`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/PrimeContactTransport.exists_laurent_kernel_of_real_prime_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The integer gains and signs obtained at the prime weights are independent of subsequent weight choices. Every vector of nonvanishing real weights therefore admits the same signed Laurent monomial construction.

For the paired-column boundary of a balanced cubic nine-cube support, this identifies the connected two-contact branch with integer coordinate transport. It reduces the all-weight kernel condition to a geometric constraint on the contact graph in Hong, Wu and Xia's Problem 2. https://arxiv.org/html/2610.09483v1#Thmproblem2

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/PrimeContactTransport.exists_laurent_kernel_of_real_prime_kernel`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/PrimeContactTransport.normalize_real_kernel`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/PrimeContactTransport.real_prime_kernel_iff_potential`
