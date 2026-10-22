# The formal series and its coefficients

## Abstract

Formal reciprocal Gamma series and boundary Turanian coefficients.

**Definition 1.1 (Formal coefficient sequences).**

Lean statement: `D5/S3/Analytic/ReciprocalGammaTuran/Series.formalSeries`

*Formalization.* `D5/S3/Analytic/ReciprocalGammaTuran/Series.formalSeries` (`✓ std3`).

*Citation.* S. I. Kalmykov and D. B. Karp (2013). *Log-concavity for series in reciprocal gamma functions and applications*. DOI: [10.1080/10652469.2013.764874](https://doi.org/10.1080/10652469.2013.764874). URL: <https://arxiv.org/abs/1206.4814>.

*Commentary.*

For a real sequence g and real b, formalSeries(g,b) has coefficient g(n)rgamma(n+b) in every natural degree n.

**Definition 1.2 (The boundary Turanian).**

Lean statement: `D5/S3/Analytic/ReciprocalGammaTuran/Series.boundarySeries`

*Formalization.* `D5/S3/Analytic/ReciprocalGammaTuran/Series.boundarySeries` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* S. I. Kalmykov and D. B. Karp (2013). *Log-concavity for series in reciprocal gamma functions and applications*. DOI: [10.1080/10652469.2013.764874](https://doi.org/10.1080/10652469.2013.764874). URL: <https://arxiv.org/abs/1206.4814>.

*Commentary.*

For every real t, the formal boundary series is formalSeries(1,0) squared minus formalSeries(1,-t) times formalSeries(1,t).

**Definition 1.3 (Boundary coefficients).**

Lean statement: `D5/S3/Analytic/ReciprocalGammaTuran/Series.d`

*Formalization.* `D5/S3/Analytic/ReciprocalGammaTuran/Series.d` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* S. I. Kalmykov and D. B. Karp (2013). *Log-concavity for series in reciprocal gamma functions and applications*. DOI: [10.1080/10652469.2013.764874](https://doi.org/10.1080/10652469.2013.764874). URL: <https://arxiv.org/abs/1206.4814>.

*Commentary.*

For real t and natural m, d(t,m) is the degree m coefficient of the formal boundary series.

**Theorem 1.4 (Exact formal Cauchy coefficients).**

Lean statement: `D5/S3/Analytic/ReciprocalGammaTuran/Series.coeff_mul`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ReciprocalGammaTuran/Series.coeff_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. I. Kalmykov and D. B. Karp (2013). *Log-concavity for series in reciprocal gamma functions and applications*. DOI: [10.1080/10652469.2013.764874](https://doi.org/10.1080/10652469.2013.764874). URL: <https://arxiv.org/abs/1206.4814>.

*Commentary.*

For every real sequence g, real mu, alpha and beta, and natural m, the coefficient of formalSeries(g,mu+alpha)formalSeries(g,mu+beta) minus formalSeries(g,mu)formalSeries(g,mu+alpha+beta) equals turanCoeff(g,mu,alpha,beta,m). The finite summation bounds justify replacing the natural difference m-k by its real value.

**Theorem 1.5 (Boundary specialization).**

Lean statement: `D5/S3/Analytic/ReciprocalGammaTuran/Series.turanCoeff_one_boundary`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ReciprocalGammaTuran/Series.turanCoeff_one_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. I. Kalmykov and D. B. Karp (2013). *Log-concavity for series in reciprocal gamma functions and applications*. DOI: [10.1080/10652469.2013.764874](https://doi.org/10.1080/10652469.2013.764874). URL: <https://arxiv.org/abs/1206.4814>.

*Commentary.*

For every real t and natural m, turanCoeff(1,-t,t,t,m) equals d(t,m).

## References

- Truth anchor: `D5/S3/Analytic/ReciprocalGammaTuran/Series.boundarySeries`
- Truth anchor: `D5/S3/Analytic/ReciprocalGammaTuran/Series.coeff_mul`
- Truth anchor: `D5/S3/Analytic/ReciprocalGammaTuran/Series.d`
- Truth anchor: `D5/S3/Analytic/ReciprocalGammaTuran/Series.formalSeries`
- Truth anchor: `D5/S3/Analytic/ReciprocalGammaTuran/Series.turanCoeff_one_boundary`
- Dependency: [D5/S3/Analytic/ReciprocalGammaTuran/Defs](Defs.md)
