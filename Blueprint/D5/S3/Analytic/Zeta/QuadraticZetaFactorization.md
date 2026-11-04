# QuadraticZetaFactorization

## Abstract

Nonzero prime ideals are partitioned by their actual contraction to the rational integers. The convergent HasProd supplier justifies regrouping by rational primes. The actual local factors, including two and the ramified prime, then prove zeta_K=zeta_Q*L for real part greater than one.

Nonzero prime ideals are partitioned by their actual contraction to the rational integers. The convergent HasProd supplier justifies regrouping by rational primes. The actual local factors, including two and the ramified prime, then prove zeta_K=zeta_Q*L for real part greater than one.

Four-slot escape registrations are unfinished, tracked at https://github.com/the-omega-institute/trureturing/issues/26321. No declared_validated status is claimed. This registration debt is separate from the native mathematical proof.

**Definition 1.1 (primeIdealsOverEquiv).**

Lean statement: `D5/S3/Analytic/Zeta/QuadraticZetaFactorization.primeIdealsOverEquiv`

*Formalization.* `D5/S3/Analytic/Zeta/QuadraticZetaFactorization.primeIdealsOverEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

Nonzero maximal-order prime ideals, partitioned by their actual contraction to Z. This equivalence includes ramified primes.

**Theorem 1.2 (hasProd_rationalPrime_factors).**

Lean statement: `D5/S3/Analytic/Zeta/QuadraticZetaFactorization.hasProd_rationalPrime_factors`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Zeta/QuadraticZetaFactorization.hasProd_rationalPrime_factors` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

Genuine convergent regrouping of the Dedekind Euler product by rational primes. `HasProd` is required here: a bare equality of `tprod` expressions does not justify it.

**Theorem 1.3 (primeIdeal_euler_factor).**

Lean statement: `D5/S3/Analytic/Zeta/QuadraticZetaFactorization.primeIdeal_euler_factor`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Zeta/QuadraticZetaFactorization.primeIdeal_euler_factor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

The actual maximal-order Euler factor, including the factors at two and p.

**Theorem 1.4 (dedekindZeta_eq_riemannZeta_mul_LFunction).**

Lean statement: `D5/S3/Analytic/Zeta/QuadraticZetaFactorization.dedekindZeta_eq_riemannZeta_mul_LFunction`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Zeta/QuadraticZetaFactorization.dedekindZeta_eq_riemannZeta_mul_LFunction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

Quadratic Dedekind-zeta factorization for the actual number field and actual Legendre Dirichlet character, proved by convergent local-to-global products.

## References

- Truth anchor: `D5/S3/Analytic/Zeta/QuadraticZetaFactorization.dedekindZeta_eq_riemannZeta_mul_LFunction`
- Truth anchor: `D5/S3/Analytic/Zeta/QuadraticZetaFactorization.hasProd_rationalPrime_factors`
- Truth anchor: `D5/S3/Analytic/Zeta/QuadraticZetaFactorization.primeIdeal_euler_factor`
- Truth anchor: `D5/S3/Analytic/Zeta/QuadraticZetaFactorization.primeIdealsOverEquiv`
- Dependency: [D5/S3/Analytic/Zeta/NumberField/ZetaProductFactorization](NumberField/ZetaProductFactorization.md)
- Dependency: [D5/S3/Analytic/Zeta/PrimeQuadraticLValues](PrimeQuadraticLValues.md)
- Dependency: [D5/S3/Arith/QuadraticFields/QuadraticPrimeSplitting](../../Arith/QuadraticFields/QuadraticPrimeSplitting.md)
