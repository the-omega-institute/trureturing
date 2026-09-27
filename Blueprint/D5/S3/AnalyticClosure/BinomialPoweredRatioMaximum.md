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

*Resolves.* `Problems/glasby-paseman-powered-ratio-maximum` (proved) by `D5/S3/AnalyticClosure/BinomialPoweredRatioMaximum.maximum_asymptotic`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"glasby-paseman-powered-ratio-maximum","declaration_gid":"D5/S3/AnalyticClosure/BinomialPoweredRatioMaximum.maximum_asymptotic","resolution_kind":"proved"} -->

*Citation.* Seok Hyun Byun and Svetlana Poznanović (2026). *Unimodality and log-concavity of generalized Glasby-Paseman sequences*. URL: <https://arxiv.org/abs/2604.14639v1>.

*Commentary.*

For every fixed positive real a and positive natural l, the maximum divided by A_m tends to one, where A_m = sqrt(l)/sqrt(2 pi m) times sqrt(1+2a)(1+a)a^((l-2)/2)/((1+a)^l-1) times ((1+2a)/(1+a))^((m+1/2)l). The real exponent (l-2)/2 includes l=1 without natural-number subtraction. The expression is the target specified in Conjecture 1.1(d) for the sequence (1.4) of the source. This attribution identifies the published conjecture statement; the source does not prove the full parameter range.

The classical complete weighted power-sum normalization is supplied by Abel, Gawronski and Neuschel: `D5/L/Analytic/abel2013binomial`; the classical local Gaussian estimate is supplied by Ouimet: `D5/L/Analytic/ouimet2020precise`.

The proof uses a floor comparison, localization of actual ratio maximizers, the moving-endpoint geometric factor, normalization of the powered denominator along both sequences, and a uniform sharp binomial bound. Finite maximum existence is proved internally and ties are allowed. No exact-peak, uniqueness, or unimodality premise is used. The complete weighted denominator normalization is a classical literature result; it is not claimed as a new discovery. Clauses (a)-(c) of the source conjecture are outside this theorem. The source and eligibility boundaries are recorded in Problems/glasby-paseman-powered-ratio-maximum.md. The resolution binding concerns the full clause (d) for each fixed a and l; it asserts no uniformity when those parameters vary.

## References

- Truth anchor: `D5/S3/AnalyticClosure/BinomialPoweredRatioMaximum.maximumValue`
- Truth anchor: `D5/S3/AnalyticClosure/BinomialPoweredRatioMaximum.maximum_asymptotic`
- Dependency: [D5/S3/AnalyticClosure/BinomialPowerNormalization](BinomialPowerNormalization.md)
- Dependency: [D5/S3/AnalyticClosure/BinomialPoweredRatioLocalization](BinomialPoweredRatioLocalization.md)
- Dependency: [D5/S3/AnalyticClosure/BinomialUniformMaximum](BinomialUniformMaximum.md)
