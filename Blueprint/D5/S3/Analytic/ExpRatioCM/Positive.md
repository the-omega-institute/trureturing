# The coefficient criterion

## Abstract

Positive exponential coefficients and complete monotonicity.

**Theorem 1.1 (The first signed derivative).**

Lean statement: `D5/S3/Analytic/ExpRatioCM/Positive.F_one`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ExpRatioCM/Positive.F_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive t, F(1,t)=exp(t)/(exp(t)-1)^2. The existing logarithmic derivative formula yields this identity, which supplies the low-index ratio formulas.

**Theorem 1.2 (Low-index ratio formulas).**

Lean statement: `D5/S3/Analytic/ExpRatioCM/Positive.ratio_low`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ExpRatioCM/Positive.ratio_low` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive t, ratioF(0,t)=1+F(0,t), ratioF(1,t)=1+2F(0,t), ratioF(2,t)=1+4F(0,t)-2F(0,2t), and ratioG(0,t)=F(0,t). These identities support the low-index complete monotonicity proof.

**Theorem 1.3 (The constant term in the second family).**

Lean statement: `D5/S3/Analytic/ExpRatioCM/Positive.G_zero_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ExpRatioCM/Positive.G_zero_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive t, G(0,t) equals 1+F(0,t).

**Theorem 1.4 (Smooth exponential moments).**

Lean statement: `D5/S3/Analytic/ExpRatioCM/Positive.contDiffOn_F`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ExpRatioCM/Positive.contDiffOn_F` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every F(i) is smooth on the positive half-line.

**Theorem 1.5 (Smooth first ratios).**

Lean statement: `D5/S3/Analytic/ExpRatioCM/Positive.contDiffOn_ratioF`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ExpRatioCM/Positive.contDiffOn_ratioF` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The quotient F(i+1)/F(i) is smooth on the positive half-line because its denominator is strictly positive.

**Theorem 1.6 (Smooth second ratios).**

Lean statement: `D5/S3/Analytic/ExpRatioCM/Positive.contDiffOn_ratioG`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ExpRatioCM/Positive.contDiffOn_ratioG` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The second consecutive ratios are smooth on the positive half-line. The zeroth denominator equals 1+F(0), and the positive-order denominators equal the corresponding F moments.

**Theorem 1.7 (Nonnegative exponential expansion).**

Lean statement: `D5/S3/Analytic/ExpRatioCM/Positive.cm_of_nonnegative_exponential_expansion`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ExpRatioCM/Positive.cm_of_nonnegative_exponential_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A smooth function whose every derivative is represented by nonnegative coefficients at nonnegative exponential frequencies has alternating derivatives of the required sign on the positive half-line.

**Theorem 1.8 (Low-index positive cases).**

Lean statement: `D5/S3/Analytic/ExpRatioCM/Positive.cm_of_le_two`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ExpRatioCM/Positive.cm_of_le_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The signed exponential moments give complete monotonicity of the zeroth moment. The frozen logarithm derivative theorem LogOneSubExpDerivatives.log_one_sub_exp_derivatives supplies the first two signed moment identities through Series.iteratedDeriv_F and neighborhood equality. Only the third signed moment identity requires one further differentiation, since the frozen theorem stops at the third logarithm derivative. These identities give the low-index closed forms on the entire positive half-line. The first two ratios are a nonnegative constant plus a nonnegative multiple of the zeroth moment. The third ratio is one plus four times that moment minus twice its value at twice the argument. At every derivative order the even terms of the moment series bound this subtraction, proving the required sign. This is the same coefficient positivity as coefficient four at positive odd frequencies and coefficient two at positive even frequencies. The zeroth ratio of the second family equals the zeroth moment, and its positive-index ratios agree with the first family.

## References

- Truth anchor: `D5/S3/Analytic/ExpRatioCM/Positive.F_one`
- Truth anchor: `D5/S3/Analytic/ExpRatioCM/Positive.G_zero_eq`
- Truth anchor: `D5/S3/Analytic/ExpRatioCM/Positive.cm_of_le_two`
- Truth anchor: `D5/S3/Analytic/ExpRatioCM/Positive.cm_of_nonnegative_exponential_expansion`
- Truth anchor: `D5/S3/Analytic/ExpRatioCM/Positive.contDiffOn_F`
- Truth anchor: `D5/S3/Analytic/ExpRatioCM/Positive.contDiffOn_ratioF`
- Truth anchor: `D5/S3/Analytic/ExpRatioCM/Positive.contDiffOn_ratioG`
- Truth anchor: `D5/S3/Analytic/ExpRatioCM/Positive.ratio_low`
- Dependency: [D5/S3/Analytic/ExpRatioCM/Series](Series.md)
- Dependency: [D5/S3/Analytic/Interpolation/LogOneSubExpDerivatives](../Interpolation/LogOneSubExpDerivatives.md)
