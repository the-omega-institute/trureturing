# QuadraticPrimeSplitting

## Abstract

The minimal polynomial modulo every rational prime gives the actual maximal-order Euler polynomial through index-one Kummer-Dedekind. Quadratic reciprocity identifies the odd-prime factors. At two the polynomial is treated separately in the two mod8 cases; at p it is ramified. No prime is omitted.

The minimal polynomial modulo every rational prime gives the actual maximal-order Euler polynomial through index-one Kummer-Dedekind. Quadratic reciprocity identifies the odd-prime factors. At two the polynomial is treated separately in the two mod8 cases; at p it is ramified. No prime is omitted.

Four-slot escape registrations are unfinished, tracked at https://github.com/the-omega-institute/trureturing/issues/26321. No declared_validated status is claimed. This registration debt is separate from the native mathematical proof.

**Definition 1.1 (quadraticRootEquivSqrts).**

Lean statement: `D5/S3/Arith/QuadraticFields/QuadraticPrimeSplitting.quadraticRootEquivSqrts`

*Formalization.* `D5/S3/Arith/QuadraticFields/QuadraticPrimeSplitting.quadraticRootEquivSqrts` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

Completing the square is a genuine bijection of root types in every odd field.

**Theorem 1.2 (quadratic_root_card).**

Lean statement: `D5/S3/Arith/QuadraticFields/QuadraticPrimeSplitting.quadratic_root_card`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/QuadraticFields/QuadraticPrimeSplitting.quadratic_root_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

Root count for the half-integral quadratic generator, including the ramified case.

**Theorem 1.3 (quadratic_euler_polynomial).**

Lean statement: `D5/S3/Arith/QuadraticFields/QuadraticPrimeSplitting.quadratic_euler_polynomial`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/QuadraticFields/QuadraticPrimeSplitting.quadratic_euler_polynomial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

The product over distinct irreducible factors is the local Euler polynomial. Repeated factors contribute only once, so this also handles ramified primes.

**Theorem 1.4 (negative_prime_reciprocity).**

Lean statement: `D5/S3/Arith/QuadraticFields/QuadraticPrimeSplitting.negative_prime_reciprocity`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/QuadraticFields/QuadraticPrimeSplitting.negative_prime_reciprocity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

The discriminant character is the conductor-p quadratic character, including at p. The prime two is treated separately because the integral generator has denominator two.

**Theorem 1.5 (integralGenerator_root_card).**

Lean statement: `D5/S3/Arith/QuadraticFields/QuadraticPrimeSplitting.integralGenerator_root_card`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/QuadraticFields/QuadraticPrimeSplitting.integralGenerator_root_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

The roots of the actual integral generator polynomial at each odd rational prime. This identifies its linear factors using the same character as the original double sum.

**Theorem 1.6 (integralGenerator_euler_polynomial).**

Lean statement: `D5/S3/Arith/QuadraticFields/QuadraticPrimeSplitting.integralGenerator_euler_polynomial`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/QuadraticFields/QuadraticPrimeSplitting.integralGenerator_euler_polynomial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

The local factor supplied to Kummer-Dedekind is expressed by the original conductor-p character, at every odd prime including the ramified prime p.

**Theorem 1.7 (integralGenerator_euler_polynomial_two).**

Lean statement: `D5/S3/Arith/QuadraticFields/QuadraticPrimeSplitting.integralGenerator_euler_polynomial_two`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/QuadraticFields/QuadraticPrimeSplitting.integralGenerator_euler_polynomial_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

At two the half-integral polynomial is irreducible for p congruent to three mod eight and has two distinct linear factors for p congruent to seven mod eight.

**Theorem 1.8 (integralGenerator_euler_polynomial_all).**

Lean statement: `D5/S3/Arith/QuadraticFields/QuadraticPrimeSplitting.integralGenerator_euler_polynomial_all`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/QuadraticFields/QuadraticPrimeSplitting.integralGenerator_euler_polynomial_all` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

Every rational prime, including two and the ramified prime p.

**Theorem 1.9 (primeIdeal_euler_polynomial).**

Lean statement: `D5/S3/Arith/QuadraticFields/QuadraticPrimeSplitting.primeIdeal_euler_polynomial`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/QuadraticFields/QuadraticPrimeSplitting.primeIdeal_euler_polynomial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

Actual prime ideals over every rational prime have the quadratic Euler factor. The maximal-order generator theorem discharges the index condition at every prime.

## References

- Truth anchor: `D5/S3/Arith/QuadraticFields/QuadraticPrimeSplitting.integralGenerator_euler_polynomial`
- Truth anchor: `D5/S3/Arith/QuadraticFields/QuadraticPrimeSplitting.integralGenerator_euler_polynomial_all`
- Truth anchor: `D5/S3/Arith/QuadraticFields/QuadraticPrimeSplitting.integralGenerator_euler_polynomial_two`
- Truth anchor: `D5/S3/Arith/QuadraticFields/QuadraticPrimeSplitting.integralGenerator_root_card`
- Truth anchor: `D5/S3/Arith/QuadraticFields/QuadraticPrimeSplitting.negative_prime_reciprocity`
- Truth anchor: `D5/S3/Arith/QuadraticFields/QuadraticPrimeSplitting.primeIdeal_euler_polynomial`
- Truth anchor: `D5/S3/Arith/QuadraticFields/QuadraticPrimeSplitting.quadraticRootEquivSqrts`
- Truth anchor: `D5/S3/Arith/QuadraticFields/QuadraticPrimeSplitting.quadratic_euler_polynomial`
- Truth anchor: `D5/S3/Arith/QuadraticFields/QuadraticPrimeSplitting.quadratic_root_card`
- Dependency: [D5/S3/Arith/QuadraticFields/QuadraticOrderGenerator](QuadraticOrderGenerator.md)
