# QuadraticOrderGenerator

## Abstract

The integral generator has its actual quadratic minimal polynomial. Its basis spans the whole maximal order, so the Kummer-Dedekind index is one. This index condition is proved, not assumed when computing rational-prime splitting.

The integral generator has its actual quadratic minimal polynomial. Its basis spans the whole maximal order, so the Kummer-Dedekind index is one. This index condition is proved, not assumed when computing rational-prime splitting.

Four-slot escape registrations are unfinished, tracked at https://github.com/the-omega-institute/trureturing/issues/26321. No declared_validated status is claimed. This registration debt is separate from the native mathematical proof.

**Definition 1.1 (orderPolynomial).**

Lean statement: `D5/S3/Arith/QuadraticFields/QuadraticOrderGenerator.orderPolynomial`

*Formalization.* `D5/S3/Arith/QuadraticFields/QuadraticOrderGenerator.orderPolynomial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

The defining polynomial of the coordinate generator of an integer quadratic algebra.

**Theorem 1.2 (orderGenerator_minpoly).**

Lean statement: `D5/S3/Arith/QuadraticFields/QuadraticOrderGenerator.orderGenerator_minpoly`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/QuadraticFields/QuadraticOrderGenerator.orderGenerator_minpoly` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

The two coordinate basis vectors prove minimality over the integers themselves.

**Definition 1.3 (integralGenerator).**

Lean statement: `D5/S3/Arith/QuadraticFields/QuadraticOrderGenerator.integralGenerator`

*Formalization.* `D5/S3/Arith/QuadraticFields/QuadraticOrderGenerator.integralGenerator` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

The half-integral generator in the actual ring of integers.

**Theorem 1.4 (integralGenerator_exponent).**

Lean statement: `D5/S3/Arith/QuadraticFields/QuadraticOrderGenerator.integralGenerator_exponent`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/QuadraticFields/QuadraticOrderGenerator.integralGenerator_exponent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

The maximality theorem discharges the exponent condition of Kummer-Dedekind at every rational prime, rather than leaving an assumed index-coprimality condition.

**Theorem 1.5 (integralGenerator_minpoly).**

Lean statement: `D5/S3/Arith/QuadraticFields/QuadraticOrderGenerator.integralGenerator_minpoly`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/QuadraticFields/QuadraticOrderGenerator.integralGenerator_minpoly` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

Its integer minimal polynomial is X squared minus X plus (p+1)/4.

## References

- Truth anchor: `D5/S3/Arith/QuadraticFields/QuadraticOrderGenerator.integralGenerator`
- Truth anchor: `D5/S3/Arith/QuadraticFields/QuadraticOrderGenerator.integralGenerator_exponent`
- Truth anchor: `D5/S3/Arith/QuadraticFields/QuadraticOrderGenerator.integralGenerator_minpoly`
- Truth anchor: `D5/S3/Arith/QuadraticFields/QuadraticOrderGenerator.orderGenerator_minpoly`
- Truth anchor: `D5/S3/Arith/QuadraticFields/QuadraticOrderGenerator.orderPolynomial`
- Dependency: [D5/S3/Arith/QuadraticFields/QuadraticOrderMaximal](QuadraticOrderMaximal.md)
