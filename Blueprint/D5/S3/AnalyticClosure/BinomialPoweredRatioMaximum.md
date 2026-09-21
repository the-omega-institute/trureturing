# Maximum of the Powered Binomial Ratio

## Abstract

The finite maximum of the actual powered-sum ratio has its exact asymptotic constant.

**Definition 1.1 (Finite maximum including both endpoints).**

Lean statement: `D5/S3/AnalyticClosure/BinomialPoweredRatioMaximum.maximumValue`

*Formalization.* `D5/S3/AnalyticClosure/BinomialPoweredRatioMaximum.maximumValue` (`✓ std3`).

*Citation.* Seok Hyun Byun and Svetlana Poznanović (2026). *Unimodality and log-concavity of generalized Glasby-Paseman sequences*. URL: <https://arxiv.org/abs/2604.14639v1>.

*Commentary.*

The maximum is taken over every natural r from zero through m of poweredRatio, whose denominator is the powered binomial sum. The definition does not select a unique maximizing index.

**Theorem 1.2 (Exact maximum asymptotic for every positive natural power).**

Lean statement: `D5/S3/AnalyticClosure/BinomialPoweredRatioMaximum.maximum_asymptotic`

*Proof.* Machine-checked in Lean as `D5/S3/AnalyticClosure/BinomialPoweredRatioMaximum.maximum_asymptotic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Seok Hyun Byun and Svetlana Poznanović (2026). *Unimodality and log-concavity of generalized Glasby-Paseman sequences*. URL: <https://arxiv.org/abs/2604.14639v1>.

*Acknowledgement.* Ulrich Abel, Wolfgang Gawronski, and Thorsten Neuschel (2013). *Binomial Polynomials*. DOI: [10.1007/s40315-013-0013-3](https://doi.org/10.1007/s40315-013-0013-3). URL: <https://doras.dcu.ie/31197/1/Binomialpolynomials.pdf>.

*Acknowledgement.* Frédéric Ouimet (2020). *A precise local limit theorem for the multinomial distribution and some applications*. DOI: [10.1016/j.jspi.2021.03.006](https://doi.org/10.1016/j.jspi.2021.03.006). URL: <https://arxiv.org/abs/2001.08512v4>.

*Commentary.*

For every fixed positive real a and positive natural l, the maximum divided by A_m tends to one, where A_m = sqrt(l)/sqrt(2 pi m) times sqrt(1+2a)(1+a)a^((l-2)/2)/((1+a)^l-1) times ((1+2a)/(1+a))^((m+1/2)l). The real exponent (l-2)/2 includes l=1 without natural-number subtraction. The expression is the target specified in Conjecture 1.1(d) for the sequence (1.4) of the source.

The proof uses a floor comparison, localization of actual ratio maximizers, the moving-endpoint geometric factor, normalization of the powered denominator along both sequences, and a uniform sharp binomial bound. Finite maximum existence is proved internally and ties are allowed. No exact-peak, uniqueness, or unimodality premise is used. The complete weighted denominator normalization is a classical literature result; it is not claimed as a new discovery. Clauses (a)-(c) of the source conjecture are outside this theorem. The source and eligibility boundaries are recorded in Problems/glasby-paseman-powered-ratio-maximum.md; no typed resolution claim is made here.

## References

- Truth anchor: `D5/S3/AnalyticClosure/BinomialPoweredRatioMaximum.maximumValue`
- Truth anchor: `D5/S3/AnalyticClosure/BinomialPoweredRatioMaximum.maximum_asymptotic`
- Dependency: [D5/S3/AnalyticClosure/BinomialPowerNormalization](BinomialPowerNormalization.md)
- Dependency: [D5/S3/AnalyticClosure/BinomialPoweredRatioLocalization](BinomialPoweredRatioLocalization.md)
- Dependency: [D5/S3/AnalyticClosure/BinomialUniformMaximum](BinomialUniformMaximum.md)
