# Rational Basis for the Robin Certificate

## Abstract

Sharp rational logarithm bounds and an exact rational checker certify the additive Robin gap at 10080 without floating-point assumptions.

**Definition 1.1 (Truncated atanh expansion).**

$$\forall t \in \mathbb{R}, K \in \mathbb{N},\; atanhPartial\left(t, K\right) = 2 \cdot \sum_{j \in range\left(K\right)} (\frac{(t)^{2 \cdot j + 1}}{(castReal\left(2 \cdot j + 1\right))})$$

*Formalization.* `D5/S3/Arith/GoldenResource/RobinRationalBasis.atanhPartial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For real t and natural K, atanhPartial is twice the sum over natural j with 0 <= j < K of t^(2j+1)/(2j+1). The denominator is coerced to the reals. This is the defining expression in the ZECKENDORF_EULER_5040 appendix.

**Definition 1.2 (Atanh reduction parameter).**

$$\forall y \in \mathbb{R},\; atanhParameter\left(y\right) = \frac{y - 1}{(y + 1)}$$

*Formalization.* `D5/S3/Arith/GoldenResource/RobinRationalBasis.atanhParameter` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For real y, atanhParameter is exactly (y-1)/(y+1), as stated in the ZECKENDORF_EULER_5040 appendix.

**Theorem 1.3 (Atanh parameter interval).**

$$\forall y \in \mathbb{R},\; \left(1 \le y \land y < 2\right) \Rightarrow \left(0 \le atanhParameter\left(y\right) \land atanhParameter\left(y\right) < \frac{1}{3}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/RobinRationalBasis.atanhParameter_lt_third` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 1 <= y < 2, the appendix parameter is nonnegative and strictly less than 1/3. This elementary estimate is stated as in the ZECKENDORF_EULER_5040 appendix.

**Definition 1.4 (Named logarithm remainder).**

$$\forall y \in \mathbb{R}, K \in \mathbb{N},\; logRemainder\left(y, K\right) = log\left(y\right) - atanhPartial\left(atanhParameter\left(y\right), K\right)$$

*Formalization.* `D5/S3/Arith/GoldenResource/RobinRationalBasis.logRemainder` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For real y and natural K, logRemainder is exactly log y minus the truncated atanh series evaluated at atanhParameter y.

**Theorem 1.5 (Sharp logarithm expansion remainder).**

$$\forall y \in \mathbb{R}, K \in \mathbb{N},\; \left(1 \le y \land y < 2\right) \Rightarrow \left(0 \le logRemainder\left(y, K\right) \land logRemainder\left(y, K\right) \le \frac{2 \cdot ((atanhParameter\left(y\right)))^{2 \cdot K + 1}}{(castReal\left(2 \cdot K + 1\right) \cdot \left(1 - ((atanhParameter\left(y\right)))^{2}\right))}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/RobinRationalBasis.log_expansion_remainder_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 1 <= y < 2, substitute t=(y-1)/(y+1). The logarithm exceeds the finite sum by a nonnegative remainder bounded by 2t^(2K+1)/((2K+1)(1-t^2)). The sharp factor 1/(2K+1) is proved by an integral majorant. This is the first boxed statement of the ZECKENDORF_EULER_5040 appendix and an elementary atanh-series remainder estimate stated there.

**Theorem 1.6 (Termwise logarithmic estimate).**

$$\forall x \in \mathbb{R},\; 0 < x \Rightarrow \left(\frac{1}{(2 \cdot ((x + 1))^{2})} < log\left(\frac{x + 1}{(x)}\right) - \frac{1}{(x + 1)} \land log\left(\frac{x + 1}{(x)}\right) - \frac{1}{(x + 1)} < \frac{1}{(2 \cdot x \cdot \left(x + 1\right))}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/RobinRationalBasis.log_harmonic_term_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive real x, the displayed strict two-sided estimate bounds log((x+1)/x)-1/(x+1). It is the elementary appendix estimate used to prove A.1, stated as in ZECKENDORF_EULER_5040.

**Theorem 1.7 (Euler--Mascheroni remainder bracket A.1).**

$$\forall N \in \mathbb{N},\; 1 \le N \Rightarrow \left(\frac{1}{(2 \cdot castReal\left(N + 1\right))} < castReal\left(harmonic\left(N\right)\right) - log\left(castReal\left(N\right)\right) - eulerMascheroniConstant\left(\right) \land castReal\left(harmonic\left(N\right)\right) - log\left(castReal\left(N\right)\right) - eulerMascheroniConstant\left(\right) < \frac{1}{(2 \cdot castReal\left(N\right))}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/RobinRationalBasis.eulerMascheroni_remainder_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural N >= 1, this is exactly equation (A.1) of the ZECKENDORF_EULER_5040 appendix. The proof squeezes strictly monotone and antitone corrected harmonic sequences to the Euler--Mascheroni constant; this elementary harmonic-asymptotic estimate is stated as in that appendix.

**Theorem 1.8 (Pinned decimal bounds for log 2).**

$$\frac{6931471803}{10000000000} < log\left(2\right) \land log\left(2\right) < \frac{6931471808}{10000000000}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/RobinRationalBasis.log_two_decimal_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This companion records the two certified Mathlib decimal inequalities for log 2. Its consumer is eulerMascheroni_decimal_bounds through the logarithm-of-1000 calculation.

**Theorem 1.9 (Decimal Euler--Mascheroni bracket).**

$$\frac{5772155}{10000000} < eulerMascheroniConstant\left(\right) \land eulerMascheroniConstant\left(\right) < \frac{5772161}{10000000}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/RobinRationalBasis.eulerMascheroni_decimal_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The N=1000 specialization of A.1, together with the sharp logarithm expansion, proves 0.5772155 < gamma_EM < 0.5772161 in the Lean kernel.

**Definition 1.10 (Rational interval data).**

$$RationalBracket = structure\left(lower\left(\mathbb{Q}\right), upper\left(\mathbb{Q}\right)\right)$$

*Formalization.* `D5/S3/Arith/GoldenResource/RobinRationalBasis.RationalBracket` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

RationalBracket is a structure with rational fields lower and upper. It is data; endpoint order and semantic containment are checked separately.

**Definition 1.11 (Semantic bracket containment).**

$$\forall b \in RationalBracket, x \in \mathbb{R},\; Contains\left(b, x\right) \Leftrightarrow \left(castReal\left(lower\left(b\right)\right) \le x \land x \le castReal\left(upper\left(b\right)\right)\right)$$

*Formalization.* `D5/S3/Arith/GoldenResource/RobinRationalBasis.Contains` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Contains b x means that the rational endpoints b.lower and b.upper, each coerced to the reals, enclose x with non-strict inequalities.

**Definition 1.12 (Truncated rational exponential).**

$$\forall q \in \mathbb{Q}, terms \in \mathbb{N},\; expPartial\left(q, terms\right) = partialSum\left(expSeries\left(\mathbb{Q}, \mathbb{Q}\right), terms, q\right)$$

*Formalization.* `D5/S3/Arith/GoldenResource/RobinRationalBasis.expPartial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For rational q and natural term count, expPartial is Mathlib's exponential formal-series partial sum evaluated at q.

**Theorem 1.13 (Finite-sum form of the exponential partial sum).**

$$\forall q \in \mathbb{Q}, terms \in \mathbb{N},\; expPartial\left(q, terms\right) = \sum_{i \in range\left(terms\right)} (\frac{(q)^{i}}{(castRat\left(factorial\left(i\right)\right))})$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/RobinRationalBasis.expPartial_eq_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Mathlib formal-series wrapper equals the rational indexed sum over natural i in range terms of q^i/i!.

**Definition 1.14 (Additive Robin gap).**

$$\forall n \in \mathbb{N},\; robinDelta\left(n\right) = exp\left(eulerMascheroniConstant\left(\right)\right) \cdot castReal\left(n\right) \cdot log\left(log\left(castReal\left(n\right)\right)\right) - castReal\left(sigma\left(1, n\right)\right)$$

*Formalization.* `D5/S3/Arith/GoldenResource/RobinRationalBasis.robinDelta` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The additive Robin gap exp(gamma_EM) times n times log(log n), minus sigma_1(n), is an auxiliary quantity of this module. The volume's chapter-9 margin Delta(n) = gamma_EM + log(log(log n)) - log(sigma_1(n)/n) is a different (logarithmic) quantity, formalized in the companion module GoldenCell5040Certificate. Only the signs of the two agree, and no identity between them is claimed here. Its exact rational basis follows 「ZECKENDORF_EULER_5040 附录」.

**Definition 1.15 (Rational positivity predicate).**

$$\forall n \in \mathbb{N}, terms \in \mathbb{N}, gamma \in RationalBracket, logLog \in RationalBracket,\; RobinPositiveJudge\left(n, terms, gamma, logLog\right) \Leftrightarrow \left(lower\left(gamma\right) \le upper\left(gamma\right) \land \left(lower\left(logLog\right) \le upper\left(logLog\right) \land \left(0 \le lower\left(gamma\right) \land \left(0 \le lower\left(logLog\right) \land castRat\left(sigma\left(1, n\right)\right) < expPartial\left(lower\left(gamma\right), terms\right) \cdot castRat\left(n\right) \cdot lower\left(logLog\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Arith/GoldenResource/RobinRationalBasis.RobinPositiveJudge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This module's own auxiliary judge for the additive Robin gap checks ordered gamma and log-log brackets, nonnegative lower endpoints, and one strict rational inequality. sigma_1(n) and n are coerced to rationals. Its exact rational basis follows 「ZECKENDORF_EULER_5040 附录」; no floating-point value enters this predicate.

**Definition 1.16 (Decidability of the rational judge).**

$$\forall n \in \mathbb{N}, terms \in \mathbb{N}, gamma \in RationalBracket, logLog \in RationalBracket,\; Decidable\left(RobinPositiveJudge\left(n, terms, gamma, logLog\right)\right)$$

*Formalization.* `D5/S3/Arith/GoldenResource/RobinRationalBasis.robinPositiveJudgeDecidable` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural input and rational bracket pair, the checker predicate has the explicitly named Decidable instance robinPositiveJudgeDecidable.

**Theorem 1.17 (Soundness of the rational checker).**

$$\forall n \in \mathbb{N}, terms \in \mathbb{N}, gamma \in RationalBracket, logLog \in RationalBracket,\; \left(Contains\left(gamma, eulerMascheroniConstant\left(\right)\right) \land \left(Contains\left(logLog, log\left(log\left(castReal\left(n\right)\right)\right)\right) \land RobinPositiveJudge\left(n, terms, gamma, logLog\right)\right)\right) \Rightarrow 0 < robinDelta\left(n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/RobinRationalBasis.robinPositiveJudge_sound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Valid semantic brackets and this module's own auxiliary judge imply positivity of the additive Robin gap. The proof lower-bounds exp(gamma_EM) by the truncated Taylor sum from the exact rational basis in 「ZECKENDORF_EULER_5040 附录」 and uses monotonicity. This is the general result named by the checker utility record, not an identity with the volume's logarithmic margin.

**Theorem 1.18 (Logarithm bounds after binary scaling).**

$$\forall y \in \mathbb{R}, k \in \mathbb{N}, K \in \mathbb{N},\; \left(1 \le k \land \left(1 \le y \land y < 2\right)\right) \Rightarrow \left(castReal\left(k\right) \cdot \frac{6931471803}{10000000000} + atanhPartial\left(\frac{y - 1}{(y + 1)}, K\right) < log\left((2)^{k} \cdot y\right) \land log\left((2)^{k} \cdot y\right) < castReal\left(k\right) \cdot \frac{6931471808}{10000000000} + atanhPartial\left(\frac{y - 1}{(y + 1)}, K\right) + \frac{2 \cdot ((\frac{y - 1}{(y + 1)}))^{2 \cdot K + 1}}{(castReal\left(2 \cdot K + 1\right) \cdot \left(1 - ((\frac{y - 1}{(y + 1)}))^{2}\right))}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/RobinRationalBasis.log_pow_two_mul_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive natural k and 1 <= y < 2, the appendix log-2 bracket and sharp atanh remainder give the displayed enclosure of log(2^k y).

**Theorem 1.19 (Transfer a checked atanh calculation).**

$$\forall x \in \mathbb{R}, y \in \mathbb{R}, lo \in \mathbb{R}, hi \in \mathbb{R}, k \in \mathbb{N}, K \in \mathbb{N},\; \left(x = (2)^{k} \cdot y \land \left(1 \le k \land \left(1 \le y \land \left(y < 2 \land \left(lo < castReal\left(k\right) \cdot \frac{6931471803}{10000000000} + atanhPartial\left(\frac{y - 1}{(y + 1)}, K\right) \land castReal\left(k\right) \cdot \frac{6931471808}{10000000000} + atanhPartial\left(\frac{y - 1}{(y + 1)}, K\right) + \frac{2 \cdot ((\frac{y - 1}{(y + 1)}))^{2 \cdot K + 1}}{(castReal\left(2 \cdot K + 1\right) \cdot \left(1 - ((\frac{y - 1}{(y + 1)}))^{2}\right))} < hi\right)\right)\right)\right)\right) \Rightarrow \left(lo < log\left(x\right) \land log\left(x\right) < hi\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/RobinRationalBasis.rational_log_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An exact identity x=2^k y and a checked pair of rational endpoint inequalities transfer to lo < log x < hi. This public helper is consumed by module 2.

**Theorem 1.20 (Transfer logarithm endpoint bounds).**

$$\forall x \in \mathbb{R}, a \in \mathbb{R}, b \in \mathbb{R}, lo \in \mathbb{R}, hi \in \mathbb{R},\; \left(0 < a \land \left(a < x \land \left(x < b \land \left(lo < log\left(a\right) \land log\left(b\right) < hi\right)\right)\right)\right) \Rightarrow \left(lo < log\left(x\right) \land log\left(x\right) < hi\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/RobinRationalBasis.log_interval_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 0<a<x<b, a certified lower bound for log a and upper bound for log b transfer across strict monotonicity of the real logarithm.

**Theorem 1.21 (Rational bounds for log 10080).**

$$\frac{921830853}{100000000} < log\left(10080\right) \land log\left(10080\right) < \frac{184366171}{20000000}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/RobinRationalBasis.log_10080_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The public exact-rational calculation encloses log 10080 between the displayed endpoints.

**Theorem 1.22 (Rational bounds for log log 10080).**

$$\frac{55529789}{25000000} < log\left(log\left(10080\right)\right) \land log\left(log\left(10080\right)\right) < \frac{222119157}{100000000}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/RobinRationalBasis.logLog_10080_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The public interval transfer encloses log(log 10080); its endpoints are those stored in logLog10080Bracket.

**Definition 1.23 (Concrete gamma checker input).**

$$gammaBracket = RationalBracket\left(\frac{5772155}{10000000}, \frac{5772161}{10000000}\right)$$

*Formalization.* `D5/S3/Arith/GoldenResource/RobinRationalBasis.gammaBracket` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

gammaBracket is exactly the pair 5772155/10000000 and 5772161/10000000.

**Definition 1.24 (Concrete log-log checker input).**

$$logLog10080Bracket = RationalBracket\left(\frac{55529789}{25000000}, \frac{222119157}{100000000}\right)$$

*Formalization.* `D5/S3/Arith/GoldenResource/RobinRationalBasis.logLog10080Bracket` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

logLog10080Bracket is exactly the pair 55529789/25000000 and 222119157/100000000.

**Theorem 1.25 (First exact checker computation).**

$$RobinPositiveJudge\left(10080, 4, gammaBracket, logLog10080Bracket\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/RobinRationalBasis.robin_positive_judge_10080` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Kernel reduction proves that four exponential terms make the rational checker true at n=10080. The exact divisor sum sigma_1(10080)=39312 is proved privately.

**Theorem 1.26 (Positive additive Robin gap at 10080).**

$$0 < robinDelta\left(10080\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/RobinRationalBasis.robin_delta_10080_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Checker soundness, the two semantic brackets, and the decided four-term input from the exact rational basis in 「ZECKENDORF_EULER_5040 附录」 prove that this module's own auxiliary additive Robin gap is positive at 10080 without floating point; this is not an identity with the volume's logarithmic margin.

## References

- Truth anchor: `D5/S3/Arith/GoldenResource/RobinRationalBasis.Contains`
- Truth anchor: `D5/S3/Arith/GoldenResource/RobinRationalBasis.RationalBracket`
- Truth anchor: `D5/S3/Arith/GoldenResource/RobinRationalBasis.RobinPositiveJudge`
- Truth anchor: `D5/S3/Arith/GoldenResource/RobinRationalBasis.atanhParameter`
- Truth anchor: `D5/S3/Arith/GoldenResource/RobinRationalBasis.atanhParameter_lt_third`
- Truth anchor: `D5/S3/Arith/GoldenResource/RobinRationalBasis.atanhPartial`
- Truth anchor: `D5/S3/Arith/GoldenResource/RobinRationalBasis.eulerMascheroni_decimal_bounds`
- Truth anchor: `D5/S3/Arith/GoldenResource/RobinRationalBasis.eulerMascheroni_remainder_bounds`
- Truth anchor: `D5/S3/Arith/GoldenResource/RobinRationalBasis.expPartial`
- Truth anchor: `D5/S3/Arith/GoldenResource/RobinRationalBasis.expPartial_eq_sum`
- Truth anchor: `D5/S3/Arith/GoldenResource/RobinRationalBasis.gammaBracket`
- Truth anchor: `D5/S3/Arith/GoldenResource/RobinRationalBasis.logLog10080Bracket`
- Truth anchor: `D5/S3/Arith/GoldenResource/RobinRationalBasis.logLog_10080_bounds`
- Truth anchor: `D5/S3/Arith/GoldenResource/RobinRationalBasis.logRemainder`
- Truth anchor: `D5/S3/Arith/GoldenResource/RobinRationalBasis.log_10080_bounds`
- Truth anchor: `D5/S3/Arith/GoldenResource/RobinRationalBasis.log_expansion_remainder_bound`
- Truth anchor: `D5/S3/Arith/GoldenResource/RobinRationalBasis.log_harmonic_term_bounds`
- Truth anchor: `D5/S3/Arith/GoldenResource/RobinRationalBasis.log_interval_bounds`
- Truth anchor: `D5/S3/Arith/GoldenResource/RobinRationalBasis.log_pow_two_mul_bounds`
- Truth anchor: `D5/S3/Arith/GoldenResource/RobinRationalBasis.log_two_decimal_bounds`
- Truth anchor: `D5/S3/Arith/GoldenResource/RobinRationalBasis.rational_log_bounds`
- Truth anchor: `D5/S3/Arith/GoldenResource/RobinRationalBasis.robinDelta`
- Truth anchor: `D5/S3/Arith/GoldenResource/RobinRationalBasis.robinPositiveJudgeDecidable`
- Truth anchor: `D5/S3/Arith/GoldenResource/RobinRationalBasis.robinPositiveJudge_sound`
- Truth anchor: `D5/S3/Arith/GoldenResource/RobinRationalBasis.robin_delta_10080_pos`
- Truth anchor: `D5/S3/Arith/GoldenResource/RobinRationalBasis.robin_positive_judge_10080`
