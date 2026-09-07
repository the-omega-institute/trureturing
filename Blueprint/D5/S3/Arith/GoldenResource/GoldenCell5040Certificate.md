# The Six-Element Golden Cell at 5040

## Abstract

The golden observation fibre at 5040 has six points. Exact divisor sums and outward rational logarithm brackets certify the strict Robin margins.

**Definition 1.1 (Golden Fibonacci weights).**

$$\forall L \in \mathbb{N},\; goldenWeight\left(L\right) = fib\left(L + 2\right)$$

*Formalization.* `D5/S3/Arith/GoldenResource/GoldenCell5040Certificate.goldenWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For natural L, goldenWeight L is exactly Fib(L+2), the weight G_L in ZECKENDORF_EULER_5040.

**Definition 1.2 (Golden exponent window).**

$$\forall a \in \mathbb{N},\; goldenBaseExponent\left(a\right) = fib\left(greatestFib\left(a + 1\right)\right) - 1$$

*Formalization.* `D5/S3/Arith/GoldenResource/GoldenCell5040Certificate.goldenBaseExponent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For natural a, the base exponent is Fib(greatestFib(a+1))-1. This is the left endpoint of the unique golden exponent window containing a.

**Theorem 1.3 (The zero exponent window).**

$$\forall a \in \mathbb{N},\; goldenBaseExponent\left(a\right) = 0 \Leftrightarrow a = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/GoldenCell5040Certificate.goldenBaseExponent_eq_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The zero base-exponent fibre consists only of exponent zero.

**Theorem 1.4 (The exponent-one window).**

$$\forall a \in \mathbb{N},\; goldenBaseExponent\left(a\right) = 1 \Leftrightarrow a = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/GoldenCell5040Certificate.goldenBaseExponent_eq_one_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The base-exponent-one fibre consists only of exponent one.

**Theorem 1.5 (The exponent-two window).**

$$\forall a \in \mathbb{N},\; goldenBaseExponent\left(a\right) = 2 \Leftrightarrow \left(a = 2 \lor a = 3\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/GoldenCell5040Certificate.goldenBaseExponent_eq_two_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The base-exponent-two fibre consists exactly of exponents two and three.

**Theorem 1.6 (The exponent-four window).**

$$\forall a \in \mathbb{N},\; goldenBaseExponent\left(a\right) = 4 \Leftrightarrow \left(a = 4 \lor \left(a = 5 \lor a = 6\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/GoldenCell5040Certificate.goldenBaseExponent_eq_four_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The base-exponent-four fibre consists exactly of exponents four, five, and six.

**Definition 1.7 (Observed prime-exponent table).**

$$\forall n \in \mathbb{N},\; goldenFactorization\left(n\right) = mapRange\left(factorization\left(n\right), goldenBaseExponent\right)$$

*Formalization.* `D5/S3/Arith/GoldenResource/GoldenCell5040Certificate.goldenFactorization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

goldenFactorization maps goldenBaseExponent over every value of the natural prime factorization. The proof-irrelevant zero-preservation argument is omitted from the displayed computational expression.

**Definition 1.8 (Golden observation).**

$$\forall n \in \mathbb{N},\; goldenObservation\left(n\right) = prod\left(goldenFactorization\left(n\right), lambda\left(p, a, (p)^{a}\right)\right)$$

*Formalization.* `D5/S3/Arith/GoldenResource/GoldenCell5040Certificate.goldenObservation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

goldenObservation is exactly the finite-support product of p raised to its goldenFactorization exponent.

**Definition 1.9 (Golden observation cell).**

$$\forall m \in \mathbb{N},\; goldenCell\left(m\right) = \{n \in \mathbb{N} \mid 0 < n \land goldenObservation\left(n\right) = m\}$$

*Formalization.* `D5/S3/Arith/GoldenResource/GoldenCell5040Certificate.goldenCell` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

goldenCell m is the set of positive naturals whose goldenObservation equals m.

**Definition 1.10 (The part beyond 5040).**

$$\forall m \in \mathbb{N},\; goldenCellPlus\left(m\right) = intersection\left(goldenCell\left(m\right), \{n \in \mathbb{N} \mid 5040 < n\}\right)$$

*Formalization.* `D5/S3/Arith/GoldenResource/GoldenCell5040Certificate.goldenCellPlus` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

goldenCellPlus m is exactly goldenCell m intersected with the naturals strictly greater than 5040. The named intersection operator denotes set intersection.

**Theorem 1.11 (The six-element 5040 cell).**

$$goldenCell\left(5040\right) = \{5040, 10080, 15120, 20160, 30240, 60480\}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/GoldenCell5040Certificate.golden_cell_5040_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This proves only the cell-identity clause of ZECKENDORF_EULER_5040 theorem 4.5. The divisor-language equivalences and divisor count in that theorem are not asserted here.

**Theorem 1.12 (Every positive cell is finite).**

$$\forall m \in \mathbb{N},\; Finite\left(goldenCellPlus\left(m\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/GoldenCell5040Certificate.goldenCellPlus_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every goldenCellPlus m is finite. The proof shows each n in goldenCell m divides m squared by bounding each exponent by twice its observed exponent.

**Theorem 1.13 (Exact divisor sums on the cell).**

$$sigma\left(1, 5040\right) = 19344 \land \left(sigma\left(1, 10080\right) = 39312 \land \left(sigma\left(1, 15120\right) = 59520 \land \left(sigma\left(1, 20160\right) = 79248 \land \left(sigma\left(1, 30240\right) = 120960 \land sigma\left(1, 60480\right) = 243840\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/GoldenCell5040Certificate.sigma_5040_cell_values` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiplicativity over the coprime prime-power factorizations gives sigma_1 values 19344, 39312, 59520, 79248, 120960, and 243840 in cell order.

**Definition 1.14 (Triple logarithm).**

$$\forall n \in \mathbb{N},\; tripleLog\left(n\right) = log\left(log\left(log\left(castReal\left(n\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Arith/GoldenResource/GoldenCell5040Certificate.tripleLog` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

tripleLog n is exactly log(log(log n)); n is coerced to the reals.

**Definition 1.15 (Logarithmic divisor-sum ratio).**

$$\forall n \in \mathbb{N},\; logSigmaRatio\left(n\right) = log\left(\frac{castReal\left(sigma\left(1, n\right)\right)}{(castReal\left(n\right))}\right)$$

*Formalization.* `D5/S3/Arith/GoldenResource/GoldenCell5040Certificate.logSigmaRatio` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

logSigmaRatio n is log of sigma_1(n)/n after both naturals are coerced to reals.

**Definition 1.16 (Chapter-9 logarithmic Robin margin).**

$$\forall n \in \mathbb{N},\; robinLogMargin\left(n\right) = eulerMascheroniConstant\left(\right) + tripleLog\left(n\right) - logSigmaRatio\left(n\right)$$

*Formalization.* `D5/S3/Arith/GoldenResource/GoldenCell5040Certificate.robinLogMargin` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is verbatim ZECKENDORF_EULER_5040 definition 9.1: Euler's constant plus log(log(log n)) minus log(sigma_1(n)/n).

**Definition 1.17 (Additive Robin margin).**

$$\forall n \in \mathbb{N},\; robinAdditiveMargin\left(n\right) = castReal\left(sigma\left(1, n\right)\right) \cdot (exp\left(robinLogMargin\left(n\right)\right) - 1)$$

*Formalization.* `D5/S3/Arith/GoldenResource/GoldenCell5040Certificate.robinAdditiveMargin` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The additive margin is sigma_1(n) times (exp(robinLogMargin n)-1), with the divisor sum coerced to the reals.

**Definition 1.18 (Golden-cell critical margin).**

$$\forall m \in \mathbb{N},\; cellMinimum\left(m\right) = sInf\left(image\left(robinLogMargin, goldenCellPlus\left(m\right)\right)\right)$$

*Formalization.* `D5/S3/Arith/GoldenResource/GoldenCell5040Certificate.cellMinimum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

cellMinimum m is the infimum of the image of robinLogMargin on goldenCellPlus m. For the nonempty finite cells in ZECKENDORF_EULER_5040 definition 14.1, cellMinimum_mem proves that this infimum is the stated minimum.

**Theorem 1.19 (The finite-cell minimum is attained).**

$$\forall m \in \mathbb{N},\; Nonempty\left(goldenCellPlus\left(m\right)\right) \Rightarrow \left(\exists n \in \mathbb{N},\; n \in goldenCellPlus\left(m\right) \land cellMinimum\left(m\right) = robinLogMargin\left(n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/GoldenCell5040Certificate.cellMinimum_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every nonempty positive golden cell, an element realizes cellMinimum. Together with goldenCellPlus_finite this proves the existence clause of definition 14.1.

**Definition 1.20 (The thirteen outward rational brackets).**

$$RelaxedAnalyticBracketWitness = structure\left(field\left(gamma, eulerMascheroniConstant\left(\right) \in Ioo\left(\frac{5772155}{10000000}, \frac{5772161}{10000000}\right)\right), field\left(tlog5040, tripleLog\left(5040\right) \in Ioo\left(\frac{7622169}{10000000}, \frac{762217}{1000000}\right)\right), field\left(ratio5040, log\left(\frac{castReal\left(19344\right)}{(castReal\left(5040\right))}\right) \in Ioo\left(\frac{6724881}{5000000}, \frac{13449763}{10000000}\right)\right), field\left(tlog10080, tripleLog\left(10080\right) \in Ioo\left(\frac{7980437}{10000000}, \frac{3990219}{5000000}\right)\right), field\left(ratio10080, log\left(\frac{castReal\left(39312\right)}{(castReal\left(10080\right))}\right) \in Ioo\left(\frac{2721953}{2000000}, \frac{6804883}{5000000}\right)\right), field\left(tlog15120, tripleLog\left(15120\right) \in Ioo\left(\frac{65379}{80000}, \frac{8172377}{10000000}\right)\right), field\left(ratio15120, log\left(\frac{castReal\left(59520\right)}{(castReal\left(15120\right))}\right) \in Ioo\left(\frac{685147}{500000}, \frac{13702941}{10000000}\right)\right), field\left(tlog20160, tripleLog\left(20160\right) \in Ioo\left(\frac{1037703}{1250000}, \frac{66413}{80000}\right)\right), field\left(ratio20160, log\left(\frac{castReal\left(79248\right)}{(castReal\left(20160\right))}\right) \in Ioo\left(\frac{13688817}{10000000}, \frac{6844409}{5000000}\right)\right), field\left(tlog30240, tripleLog\left(30240\right) \in Ioo\left(\frac{1694983}{2000000}, \frac{2118729}{2500000}\right)\right), field\left(ratio30240, log\left(\frac{castReal\left(120960\right)}{(castReal\left(30240\right))}\right) \in Ioo\left(\frac{13862943}{10000000}, \frac{433217}{312500}\right)\right), field\left(tlog60480, tripleLog\left(60480\right) \in Ioo\left(\frac{273429}{312500}, \frac{8749729}{10000000}\right)\right), field\left(ratio60480, log\left(\frac{castReal\left(243840\right)}{(castReal\left(60480\right))}\right) \in Ioo\left(\frac{2788399}{2000000}, \frac{3485499}{2500000}\right)\right)\right)$$

*Formalization.* `D5/S3/Arith/GoldenResource/GoldenCell5040Certificate.RelaxedAnalyticBracketWitness` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The proposition has exactly thirteen fields: one Euler-constant bracket and, for each of the six cell points, a triple-log bracket and a log-sigma-ratio bracket. Every endpoint is displayed as an exact real rational.

**Theorem 1.21 (Construction of all analytic leaves).**

$$RelaxedAnalyticBracketWitness$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/GoldenCell5040Certificate.analytic_bracket_witness_constructed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The thirteen bracket fields are inhabited unconditionally using the sharp rational logarithm expansion from RobinRationalBasis. No floating-point number is used.

**Theorem 1.22 (Certified pointwise margins on the 5040 cell).**

$$-\frac{5545}{1000000} < robinLogMargin\left(5040\right) \land \left(robinLogMargin\left(5040\right) < -\frac{5542}{1000000} \land \left(\frac{1}{100} < robinLogMargin\left(10080\right) \land \left(\frac{1}{100} < robinLogMargin\left(15120\right) \land \left(\frac{1}{100} < robinLogMargin\left(20160\right) \land \left(\frac{1}{100} < robinLogMargin\left(30240\right) \land \frac{1}{100} < robinLogMargin\left(60480\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/GoldenCell5040Certificate.robin_log_margin_5040_point_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The margin at 5040 lies in the certified outward interval from -5545/1000000 to -5542/1000000, and each of the other five cell points has margin greater than 1/100.

**Theorem 1.23 (Certified margin bracket at 5040).**

$$-\frac{5545}{1000000} < robinLogMargin\left(5040\right) \land robinLogMargin\left(5040\right) < -\frac{5542}{1000000}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/GoldenCell5040Certificate.robin_log_margin_5040_bracket` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certified bracket -5545/1000000 < robinLogMargin 5040 < -5542/1000000 is the live negative-margin input to theorem 11.2.

**Theorem 1.24 (The stronger positive-cell bound).**

$$\forall n \in \mathbb{N},\; n \in goldenCellPlus\left(5040\right) \Rightarrow \frac{1}{100} < robinLogMargin\left(n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/GoldenCell5040Certificate.robin_log_margin_5040_cell_plus_gt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every n in goldenCellPlus 5040 has robinLogMargin n greater than 1/100. The consumer edge is theorem 11.2 below, which weakens 1/100 to 47/10000.

**Theorem 1.25 (Strict Robin certificate for the 5040 cell).**

$$robinLogMargin\left(5040\right) < 0 \land \left(\forall n \in \mathbb{N},\; n \in goldenCell\left(5040\right) \setminus \{5040\} \Rightarrow \frac{47}{10000} < robinLogMargin\left(n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/GoldenCell5040Certificate.robin_log_margin_5040_cell_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is exactly the two boxed clauses of ZECKENDORF_EULER_5040 theorem 11.2: the margin at 5040 is negative, while every other point of its golden cell has margin greater than 47/10000. The proof is unconditional.

**Theorem 1.26 (Strong lower bound for the 5040 cell minimum).**

$$\frac{1}{100} < cellMinimum\left(5040\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/GoldenCell5040Certificate.cell_minimum_5040_gt_one_hundredth` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact five-point minimum over goldenCellPlus 5040 exceeds 1/100.

**Theorem 1.27 (Positive critical margin at 5040).**

$$0 < cellMinimum\left(5040\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/GoldenCell5040Certificate.cell_minimum_5040_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The strong minimum bound yields the requested unconditional instance delta_cell(5040)>0 from ZECKENDORF_EULER_5040 definition 14.1.

## References

- Truth anchor: `D5/S3/Arith/GoldenResource/GoldenCell5040Certificate.RelaxedAnalyticBracketWitness`
- Truth anchor: `D5/S3/Arith/GoldenResource/GoldenCell5040Certificate.analytic_bracket_witness_constructed`
- Truth anchor: `D5/S3/Arith/GoldenResource/GoldenCell5040Certificate.cellMinimum`
- Truth anchor: `D5/S3/Arith/GoldenResource/GoldenCell5040Certificate.cellMinimum_mem`
- Truth anchor: `D5/S3/Arith/GoldenResource/GoldenCell5040Certificate.cell_minimum_5040_gt_one_hundredth`
- Truth anchor: `D5/S3/Arith/GoldenResource/GoldenCell5040Certificate.cell_minimum_5040_pos`
- Truth anchor: `D5/S3/Arith/GoldenResource/GoldenCell5040Certificate.goldenBaseExponent`
- Truth anchor: `D5/S3/Arith/GoldenResource/GoldenCell5040Certificate.goldenBaseExponent_eq_four_iff`
- Truth anchor: `D5/S3/Arith/GoldenResource/GoldenCell5040Certificate.goldenBaseExponent_eq_one_iff`
- Truth anchor: `D5/S3/Arith/GoldenResource/GoldenCell5040Certificate.goldenBaseExponent_eq_two_iff`
- Truth anchor: `D5/S3/Arith/GoldenResource/GoldenCell5040Certificate.goldenBaseExponent_eq_zero_iff`
- Truth anchor: `D5/S3/Arith/GoldenResource/GoldenCell5040Certificate.goldenCell`
- Truth anchor: `D5/S3/Arith/GoldenResource/GoldenCell5040Certificate.goldenCellPlus`
- Truth anchor: `D5/S3/Arith/GoldenResource/GoldenCell5040Certificate.goldenCellPlus_finite`
- Truth anchor: `D5/S3/Arith/GoldenResource/GoldenCell5040Certificate.goldenFactorization`
- Truth anchor: `D5/S3/Arith/GoldenResource/GoldenCell5040Certificate.goldenObservation`
- Truth anchor: `D5/S3/Arith/GoldenResource/GoldenCell5040Certificate.goldenWeight`
- Truth anchor: `D5/S3/Arith/GoldenResource/GoldenCell5040Certificate.golden_cell_5040_identity`
- Truth anchor: `D5/S3/Arith/GoldenResource/GoldenCell5040Certificate.logSigmaRatio`
- Truth anchor: `D5/S3/Arith/GoldenResource/GoldenCell5040Certificate.robinAdditiveMargin`
- Truth anchor: `D5/S3/Arith/GoldenResource/GoldenCell5040Certificate.robinLogMargin`
- Truth anchor: `D5/S3/Arith/GoldenResource/GoldenCell5040Certificate.robin_log_margin_5040_bracket`
- Truth anchor: `D5/S3/Arith/GoldenResource/GoldenCell5040Certificate.robin_log_margin_5040_cell_certificate`
- Truth anchor: `D5/S3/Arith/GoldenResource/GoldenCell5040Certificate.robin_log_margin_5040_cell_plus_gt`
- Truth anchor: `D5/S3/Arith/GoldenResource/GoldenCell5040Certificate.robin_log_margin_5040_point_bounds`
- Truth anchor: `D5/S3/Arith/GoldenResource/GoldenCell5040Certificate.sigma_5040_cell_values`
- Truth anchor: `D5/S3/Arith/GoldenResource/GoldenCell5040Certificate.tripleLog`
- Dependency: [D5/S3/Arith/GoldenResource/RobinRationalBasis](RobinRationalBasis.md)
