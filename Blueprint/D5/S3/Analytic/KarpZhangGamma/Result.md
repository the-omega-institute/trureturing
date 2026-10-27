# Pairing and the transformed Turanian

## Abstract

Paired reciprocal-gamma kernels and the two-variable transform.

**Theorem 1.1 (Reflection of a finite sum).**

$$\forall f \in Nat \to Real,\; \forall m \in Nat,\; \sum _{k \in \operatorname{Finset}.\operatorname{range}\left(m + 1\right)} (f\left(k\right)) = \sum _{k \in \operatorname{Finset}.\operatorname{range}\left(\operatorname{Nat}.\operatorname{div}\left(m, 2\right) + 1\right)} (\operatorname{if} (2 \cdot k < m) \operatorname{then} (f\left(k\right) + f\left(m - k\right)) \operatorname{else} (f\left(k\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangGamma/Result.pair_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any real sequence f and natural m, reflect the strict upper half of the finite interval onto the lower half. Each reflected pair contributes its two values, while an even-degree middle term occurs once. Nat.div is natural division. This identity supplies the finite pairing of scalar kernels and the central-tail decomposition.

**Theorem 1.2 (Closed form for the finite convolution).**

$$\forall b \in Real,\; \forall c \in Real,\; 0 < b \Rightarrow \left(0 < c \Rightarrow \left(\forall m \in Nat,\; \sum _{k \in \operatorname{Finset}.\operatorname{range}\left(m + 1\right)} (\frac{1}{\operatorname{Nat}.\operatorname{factorial}\left(k\right) \cdot \operatorname{Nat}.\operatorname{factorial}\left(m - k\right) \cdot \operatorname{Real}.\operatorname{Gamma}\left(b + k\right) \cdot \operatorname{Real}.\operatorname{Gamma}\left(c + (m - k)\right)}) = \frac{\operatorname{Polynomial}.\operatorname{eval}\left(b + c + m - 1, \operatorname{ascPochhammer}\left(Real, m\right)\right)}{\operatorname{Nat}.\operatorname{factorial}\left(m\right) \cdot \operatorname{Real}.\operatorname{Gamma}\left(b + m\right) \cdot \operatorname{Real}.\operatorname{Gamma}\left(c + m\right)}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangGamma/Result.reciprocalGamma_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive real b,c and every natural m, the sum over k=0,...,m of 1/[k factorial times (m-k) factorial times Real.Gamma(b+k) times Real.Gamma(c+m-k)] equals the evaluation of ascPochhammer at b+c+m-1 in degree m, divided by m factorial times Real.Gamma(b+m) times Real.Gamma(c+m). This is identity (3.11) of the gamma-series argument. It includes m=0 even when b+c-1 is nonpositive.

**Theorem 1.3 (Balancing the Gamma product).**

$$\forall a \in Real,\; \forall alpha \in Real,\; \forall beta \in Real,\; 0 < a \Rightarrow \left(0 \le alpha \Rightarrow \left(0 \le beta \Rightarrow \operatorname{Real}.\operatorname{Gamma}\left(a + alpha\right) \cdot \operatorname{Real}.\operatorname{Gamma}\left(a + beta\right) \le \operatorname{Real}.\operatorname{Gamma}\left(a\right) \cdot \operatorname{Real}.\operatorname{Gamma}\left(a + alpha + beta\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangGamma/Result.gamma_balanced_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive real a and nonnegative real alpha,beta, Real.Gamma(a+alpha) times Real.Gamma(a+beta) is at most Real.Gamma(a) times Real.Gamma(a+alpha+beta). The two interior arguments are complementary convex combinations of the endpoints. Add the two inequalities for log composed with Real.Gamma, then use positivity to exponentiate. If the sum of the shifts is zero the assertion is equality.

**Definition 1.4 (Unpaired scalar kernel).**

$$\forall a \in Real,\; \forall alpha \in Real,\; \forall beta \in Real,\; \forall m \in Nat,\; \forall k \in Nat,\; \operatorname{kernel}\left(a, alpha, beta, m, k\right) = \frac{1}{\operatorname{Nat}.\operatorname{factorial}\left(k\right) \cdot \operatorname{Nat}.\operatorname{factorial}\left(m - k\right)} \cdot \left(\frac{1}{\operatorname{Real}.\operatorname{Gamma}\left(a + alpha + k\right) \cdot \operatorname{Real}.\operatorname{Gamma}\left(a + beta + (m - k)\right)} - \frac{1}{\operatorname{Real}.\operatorname{Gamma}\left(a + k\right) \cdot \operatorname{Real}.\operatorname{Gamma}\left(a + alpha + beta + (m - k)\right)}\right)$$

*Formalization.* `D5/S3/Analytic/KarpZhangGamma/Result.kernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For real a,alpha,beta and natural m,k, kernel(a,alpha,beta,m,k) equals 1/[k factorial times (m-k) factorial] times the difference between 1/[Real.Gamma(a+alpha+k)Real.Gamma(a+beta+m-k)] and 1/[Real.Gamma(a+k)Real.Gamma(a+alpha+beta+m-k)]. Natural subtraction is literal; the theorems sum only over k <= m.

**Theorem 1.5 (Nonnegative total kernel).**

$$\forall a \in Real,\; \forall alpha \in Real,\; \forall beta \in Real,\; 0 < a \Rightarrow \left(0 \le alpha \Rightarrow \left(0 \le beta \Rightarrow \left(\forall m \in Nat,\; 0 \le \sum _{k \in \operatorname{Finset}.\operatorname{range}\left(m + 1\right)} (\operatorname{kernel}\left(a, alpha, beta, m, k\right))\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangGamma/Result.kernel_sum_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive real a, nonnegative real alpha,beta and natural m, the sum of kernel(a,alpha,beta,m,k) for k=0,...,m is nonnegative. The convolution formula factors this total as the rising-factorial prefactor divided by m factorial, times the reciprocal-gamma balancing difference at a+m. Jensen's inequality for Real.convexOn_log_Gamma makes that difference nonnegative. At m=0 the rising-factorial prefactor is one; at positive degree its argument is positive.

**Definition 1.6 (Paired scalar kernel).**

$$\forall a \in Real,\; \forall alpha \in Real,\; \forall beta \in Real,\; \forall m \in Nat,\; \forall k \in Nat,\; \operatorname{pairedKernel}\left(a, alpha, beta, m, k\right) = \operatorname{ite}\left(2 \cdot k < m, \operatorname{kernel}\left(a, alpha, beta, m, k\right) + \operatorname{kernel}\left(a, alpha, beta, m, m - k\right), \operatorname{kernel}\left(a, alpha, beta, m, k\right)\right)$$

*Formalization.* `D5/S3/Analytic/KarpZhangGamma/Result.pairedKernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For real a,alpha,beta and natural m,k, pairedKernel(a,alpha,beta,m,k) is kernel(a,alpha,beta,m,k) plus kernel(a,alpha,beta,m,m-k) when 2k < m, and is kernel(a,alpha,beta,m,k) otherwise. The theorems use only 0 <= k <= floor(m/2); the unique middle term in even degree is counted once.

**Theorem 1.7 (One negative-to-positive sign change).**

$$\forall a \in Real,\; \forall alpha \in Real,\; \forall beta \in Real,\; 0 < a \Rightarrow \left(0 \le alpha \Rightarrow \left(0 \le beta \Rightarrow \left(\forall m \in Nat,\; \forall i \in Nat,\; i \le \operatorname{Nat}.\operatorname{div}\left(m, 2\right) \Rightarrow \left(\forall j \in Nat,\; j \le \operatorname{Nat}.\operatorname{div}\left(m, 2\right) \Rightarrow \left(i < j \Rightarrow \left(0 < \operatorname{pairedKernel}\left(a, alpha, beta, m, i\right) \Rightarrow 0 \le \operatorname{pairedKernel}\left(a, alpha, beta, m, j\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangGamma/Result.pairedKernel_sign` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive real a, nonnegative real alpha,beta and natural m, take any natural i,j <= floor(m/2) with i < j. If pairedKernel(a,alpha,beta,m,i) is positive, pairedKernel(a,alpha,beta,m,j) is nonnegative. This is the sign condition needed for the finite weighting principle and includes either shift being zero. The proof propagates a nonpositive four-term bracket backwards in the index, then argues by contradiction against a positive earlier bracket.

**Theorem 1.8 (Finite pairing with symmetric weights).**

$$\forall a \in Real,\; \forall alpha \in Real,\; \forall beta \in Real,\; \forall m \in Nat,\; \forall W \in Nat \to Real,\; \left(\forall k \in Nat,\; k \le m \Rightarrow W\left(m - k\right) = W\left(k\right)\right) \Rightarrow \sum _{k \in \operatorname{Finset}.\operatorname{range}\left(m + 1\right)} (\operatorname{kernel}\left(a, alpha, beta, m, k\right) \cdot W\left(k\right)) = \sum _{k \in \operatorname{Finset}.\operatorname{range}\left(\operatorname{Nat}.\operatorname{div}\left(m, 2\right) + 1\right)} (\operatorname{pairedKernel}\left(a, alpha, beta, m, k\right) \cdot W\left(k\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangGamma/Result.finite_pairing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For real a,alpha,beta, natural m and a real sequence W satisfying W(m-k)=W(k) for every k <= m, the sum of kernel(a,alpha,beta,m,k) times W(k) over k=0,...,m equals the sum of pairedKernel(a,alpha,beta,m,k) times W(k) over k=0,...,floor(m/2). Split the full interval into its lower half and strict upper half, and reflect the upper half by k maps to m-k. The strict split ensures that an even-degree middle term occurs once.

**Theorem 1.9 (Nonnegative total paired kernel).**

$$\forall a \in Real,\; \forall alpha \in Real,\; \forall beta \in Real,\; 0 < a \Rightarrow \left(0 \le alpha \Rightarrow \left(0 \le beta \Rightarrow \left(\forall m \in Nat,\; 0 \le \sum _{k \in \operatorname{Finset}.\operatorname{range}\left(\operatorname{Nat}.\operatorname{div}\left(m, 2\right) + 1\right)} (\operatorname{pairedKernel}\left(a, alpha, beta, m, k\right))\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangGamma/Result.pairedKernel_sum_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive real a, nonnegative real alpha,beta and natural m, the sum of pairedKernel(a,alpha,beta,m,k) over k=0,...,floor(m/2) is nonnegative. Apply finite_pairing with W identically one and use kernel_sum_nonneg. Positivity of this total is not assumed as an additional hypothesis.

**Definition 1.10 (A finite coefficient of the transformed Turanian).**

$$\forall y \in Nat \to Real,\; \forall a \in Real,\; \forall alpha \in Real,\; \forall beta \in Real,\; \forall N \in Nat,\; \forall m \in Nat,\; \operatorname{transformDelta}\left(y, a, alpha, beta, N, m\right) = \sum _{k \in \operatorname{Finset}.\operatorname{range}\left(m + 1\right)} (\operatorname{kernel}\left(a, alpha, beta, m, k\right) \cdot \operatorname{productCoeff}\left(\operatorname{fun} (r:Nat) \mapsto y\left(2 \cdot k + r\right), \operatorname{fun} (r:Nat) \mapsto y\left(2 \cdot \left(m - k\right) + r\right), N\right))$$

*Formalization.* `D5/S3/Analytic/KarpZhangGamma/Result.transformDelta` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a real sequence y, real a,alpha,beta and natural N,m, transformDelta(y,a,alpha,beta,N,m) is the sum over k=0,...,m of kernel(a,alpha,beta,m,k) times Smoothing.productCoeff(r maps to y(2k+r),r maps to y(2(m-k)+r),N). It is the coefficient of z to degree N and w to degree m in the Turanian of H(a;z,w), where H has coefficient y(2j+r)/(r factorial times j factorial times Real.Gamma(a+j)) in degree (r,j). All sums defining a fixed coefficient are finite.

**Theorem 1.11 (Coefficient form of two_variable_nonneg).**

$$\forall y \in Nat \to Real,\; \operatorname{IsLogConcave}\left(y\right) \Rightarrow \left(\forall a \in Real,\; \forall alpha \in Real,\; \forall beta \in Real,\; 0 < a \Rightarrow \left(0 \le alpha \Rightarrow \left(0 \le beta \Rightarrow \left(\forall N \in Nat,\; \forall m \in Nat,\; 0 \le \operatorname{transformDelta}\left(y, a, alpha, beta, N, m\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangGamma/Result.two_variable_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real sequence y satisfying D5.S3.Analytic.KarpZhangReciprocal.Result.IsLogConcave, every positive real a, all nonnegative real alpha,beta and all natural N,m, transformDelta(y,a,alpha,beta,N,m) is nonnegative. There is no convergence or growth hypothesis. Commutativity of the finite smoothed convolution makes the weights symmetric; finite_pairing then expresses the coefficient in terms of pairedKernel. The one-sign-change theorem and nonnegative total supply the hypotheses of Smoothing.smoothed_weighting.

For x=a+k, z=a+m-k and alpha <= beta, let u,v,r,s be the reciprocal Gamma products with first arguments x+alpha, x+beta, x and x+alpha+beta respectively. Gamma balancing gives r <= u <= v. If B=u+v-r-s is nonpositive, then v <= s and r <= s. With S=x+z+alpha+beta and F(t)=(t-1)/(S-t), Gamma recurrence writes the preceding bracket as F(x+alpha)B + v(F(x+beta)-F(x+alpha)) + r(F(x+alpha)-F(x)) - s(F(x+alpha+beta)-F(x+alpha)). The first term is nonpositive, and the rest is at most s times F(x+beta)-F(x)-F(x+alpha+beta)+F(x+alpha), which is nonpositive because F has increasing increments. The increment formula is beta times (S-1) divided by the product of the two positive endpoint denominators. Swapping alpha and beta covers the other shift order.

## References

- Truth anchor: `D5/S3/Analytic/KarpZhangGamma/Result.finite_pairing`
- Truth anchor: `D5/S3/Analytic/KarpZhangGamma/Result.gamma_balanced_shift`
- Truth anchor: `D5/S3/Analytic/KarpZhangGamma/Result.kernel`
- Truth anchor: `D5/S3/Analytic/KarpZhangGamma/Result.kernel_sum_nonneg`
- Truth anchor: `D5/S3/Analytic/KarpZhangGamma/Result.pair_sum`
- Truth anchor: `D5/S3/Analytic/KarpZhangGamma/Result.pairedKernel`
- Truth anchor: `D5/S3/Analytic/KarpZhangGamma/Result.pairedKernel_sign`
- Truth anchor: `D5/S3/Analytic/KarpZhangGamma/Result.pairedKernel_sum_nonneg`
- Truth anchor: `D5/S3/Analytic/KarpZhangGamma/Result.reciprocalGamma_sum`
- Truth anchor: `D5/S3/Analytic/KarpZhangGamma/Result.transformDelta`
- Truth anchor: `D5/S3/Analytic/KarpZhangGamma/Result.two_variable_nonneg`
- Dependency: [D5/S3/Analytic/KarpZhangGamma/Smoothing](Smoothing.md)
- Dependency: [D5/S3/Analytic/KummerRatio/BetaIntegral](../KummerRatio/BetaIntegral.md)
