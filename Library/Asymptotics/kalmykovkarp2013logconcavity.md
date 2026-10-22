---
bibkey: kalmykovkarp2013logconcavity
authors: S. I. Kalmykov and D. B. Karp
year: 2013
title: Log-concavity for series in reciprocal gamma functions and applications
doi: 10.1080/10652469.2013.764874
url: https://arxiv.org/abs/1206.4814
claim: "The Moreover clause of Conjecture 1 asserts positive coefficients for the shifted reciprocal Gamma Turanian under Theorem 2's sequence hypotheses."
strata_touched:
  - D5/S3/Analytic/ReciprocalGammaTuran/Defs
  - D5/S3/Analytic/ReciprocalGammaTuran/Series
  - D5/S3/Analytic/ReciprocalGammaTuran/Result
license: citation-only
triage: anchor
---

# Reciprocal Gamma Turanian coefficients

## Verified locator

DOI: 10.1080/10652469.2013.764874

Source: https://arxiv.org/abs/1206.4814

Pinned version: https://arxiv.org/abs/1206.4814v1, Conjecture 1,
equation (20), Theorem 2. Journal publication: *Integral Transforms and
Special Functions* 24(11) (2013), 859–872.

## Mathematical correspondence

Equation (20) defines

$$g(\mu,x)=\sum_{n=0}^{\infty}\frac{g_n x^n}{\Gamma(n+\mu)}.$$

Theorem 2 assumes a nontrivial nonnegative log-concave sequence without
internal zeros. Conjecture 1 asserts log-concavity in the positive
parameter and, in its Moreover clause, positivity of all coefficients of

$$g(\mu+\alpha,x)g(\mu+\beta,x)
-g(\mu,x)g(\mu+\alpha+\beta,x)$$

for $\alpha,\beta>0$, $\mu\ge-1$, $\mu+\alpha,\mu+\beta\ge0$.
The reciprocal Gamma value at a pole is zero.

`Defs.rgamma`, `Defs.AdmissibleSeq`, `Defs.turanCoeff` and `Defs.claim`
encode these objects and the coefficientwise clause. `Series.coeff_mul`
identifies the finite sum with the formal Cauchy coefficient.
`Boundary.d_two_neg` gives a negative second coefficient for the unit
sequence at every boundary shift $\mu=-t$, $\alpha=\beta=t$, $0<t<1$.
`Interior.interior_failure` places a negative second coefficient strictly
inside the stated parameter range. `Result.result` refutes only the
Moreover clause; it does not address the positive-parameter log-concavity
assertion.

The bounded literature scope and its limitations are stated in
`Problems/kalmykov-karp-2013-reciprocal-gamma-turanian-coefficients.md`.
