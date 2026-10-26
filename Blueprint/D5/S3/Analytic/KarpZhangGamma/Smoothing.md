# Finite exponential smoothing

## Abstract

Coefficientwise balancing of exponential derivatives.

**Definition 1.1 (Factorial-scaled coefficient).**

$$\forall f \in Nat \to Real,\; \forall g \in Nat \to Real,\; \forall N \in Nat,\; \operatorname{binomialProduct}\left(f, g, N\right) = \sum _{r \in \operatorname{Finset}.\operatorname{range}\left(N + 1\right)} (\operatorname{Nat}.\operatorname{choose}\left(N, r\right) \cdot f\left(r\right) \cdot g\left(N - r\right))$$

*Formalization.* `D5/S3/Analytic/KarpZhangGamma/Smoothing.binomialProduct` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For real sequences f,g and natural N, binomialProduct(f,g,N) is the sum over r=0,...,N of Nat.choose(N,r) times f(r)g(N-r), with the binomial coefficient cast to the reals. It is N factorial times the ordinary coefficient of the product of the exponential generating series of f and g.

**Definition 1.2 (Ordinary coefficient).**

$$\forall f \in Nat \to Real,\; \forall g \in Nat \to Real,\; \forall N \in Nat,\; \operatorname{productCoeff}\left(f, g, N\right) = \sum _{r \in \operatorname{Finset}.\operatorname{range}\left(N + 1\right)} (\frac{f\left(r\right) \cdot g\left(N - r\right)}{\operatorname{Nat}.\operatorname{factorial}\left(r\right) \cdot \operatorname{Nat}.\operatorname{factorial}\left(N - r\right)})$$

*Formalization.* `D5/S3/Analytic/KarpZhangGamma/Smoothing.productCoeff` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For real sequences f,g and natural N, productCoeff(f,g,N) is the sum over r=0,...,N of f(r)g(N-r) divided by r factorial times (N-r) factorial. This is an ordinary finite Cauchy coefficient, without convergence assumptions.

**Theorem 1.3 (General balancing inequality).**

$$\forall y \in Nat \to Real,\; \operatorname{IsLogConcave}\left(y\right) \Rightarrow \left(\forall L \in Nat,\; \forall R \in Nat,\; \forall u \in Nat,\; \forall v \in Nat,\; L \le u \Rightarrow \left(L \le v \Rightarrow \left(u \le R \Rightarrow \left(v \le R \Rightarrow \left(u + v = L + R \Rightarrow y\left(L\right) \cdot y\left(R\right) \le y\left(u\right) \cdot y\left(v\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangGamma/Smoothing.balanced_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let y satisfy D5.S3.Analytic.KarpZhangReciprocal.Result.IsLogConcave. For natural L,R,u,v satisfying L <= u, L <= v, u <= R, v <= R and u+v=L+R, y(L)y(R) <= y(u)y(v). The proof reuses the existing balanced_step theorem at fixed index sum, including sequences whose lower support boundary is positive.

**Theorem 1.4 (Finite Leibniz recurrence).**

$$\forall f \in Nat \to Real,\; \forall g \in Nat \to Real,\; \forall N \in Nat,\; \operatorname{binomialProduct}\left(f, g, N + 1\right) = \operatorname{binomialProduct}\left(\operatorname{fun} (r:Nat) \mapsto f\left(r + 1\right), g, N\right) + \operatorname{binomialProduct}\left(f, \operatorname{fun} (r:Nat) \mapsto g\left(r + 1\right), N\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangGamma/Smoothing.binomialProduct_succ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every pair of real sequences f,g and natural N, binomialProduct(f,g,N+1) equals binomialProduct(r maps to f(r+1),g,N) plus binomialProduct(f,r maps to g(r+1),N). Finset.sum_choose_succ_mul supplies the recurrence for the function (i,j) maps to f(i)g(j), retaining both endpoint terms exactly.

**Theorem 1.5 (Commutativity of the finite convolution).**

$$\forall f \in Nat \to Real,\; \forall g \in Nat \to Real,\; \forall N \in Nat,\; \operatorname{binomialProduct}\left(f, g, N\right) = \operatorname{binomialProduct}\left(g, f, N\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangGamma/Smoothing.binomialProduct_comm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every pair of real sequences f,g and natural N, binomialProduct(f,g,N) equals binomialProduct(g,f,N). Reflection r maps to N-r preserves the binomial coefficient and interchanges the two factors. Together with productCoeff_eq this makes the smoothed weights symmetric around m/2.

**Theorem 1.6 (Factorial conversion).**

$$\forall f \in Nat \to Real,\; \forall g \in Nat \to Real,\; \forall N \in Nat,\; \operatorname{productCoeff}\left(f, g, N\right) = \frac{\operatorname{binomialProduct}\left(f, g, N\right)}{\operatorname{Nat}.\operatorname{factorial}\left(N\right)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangGamma/Smoothing.productCoeff_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every pair of real sequences f,g and natural N, productCoeff(f,g,N) equals binomialProduct(f,g,N) divided by N factorial. Nat.choose_mul_factorial_mul_factorial supplies the finite coefficient identity; factorials are positive.

**Theorem 1.7 (Every smoothed minor is nonnegative).**

$$\forall y \in Nat \to Real,\; \operatorname{IsLogConcave}\left(y\right) \Rightarrow \left(\forall p \in Nat,\; \forall q \in Nat,\; \forall N \in Nat,\; p \le q + 1 \Rightarrow \operatorname{productCoeff}\left(\operatorname{fun} (r:Nat) \mapsto y\left(p + r\right), \operatorname{fun} (r:Nat) \mapsto y\left(q + 2 + r\right), N\right) \le \operatorname{productCoeff}\left(\operatorname{fun} (r:Nat) \mapsto y\left(p + 1 + r\right), \operatorname{fun} (r:Nat) \mapsto y\left(q + 1 + r\right), N\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangGamma/Smoothing.smoothing_minor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real sequence y satisfying IsLogConcave and all natural p,q,N with p <= q+1, productCoeff(r maps to y(p+r),r maps to y(q+2+r),N) <= productCoeff(r maps to y(p+1+r),r maps to y(q+1+r),N). Thus the degree-N coefficient of P(p+1)P(q+1)-P(p)P(q+2) is nonnegative, where P(j) has coefficient y(j+r)/r factorial in degree r. The adjacent-index boundary p=q+1 is equality.

**Theorem 1.8 (Weighted transformed minors).**

$$\forall y \in Nat \to Real,\; \operatorname{IsLogConcave}\left(y\right) \Rightarrow \left(\forall A \in Nat \to Real,\; \forall m \in Nat,\; \left(\forall i \in Nat,\; i \le \operatorname{Nat}.\operatorname{div}\left(m, 2\right) \Rightarrow \left(\forall j \in Nat,\; j \le \operatorname{Nat}.\operatorname{div}\left(m, 2\right) \Rightarrow \left(i < j \Rightarrow \left(0 < A\left(i\right) \Rightarrow 0 \le A\left(j\right)\right)\right)\right)\right) \Rightarrow \left(0 \le \sum _{i \in \operatorname{Finset}.\operatorname{range}\left(\operatorname{Nat}.\operatorname{div}\left(m, 2\right) + 1\right)} (A\left(i\right)) \Rightarrow \left(\forall N \in Nat,\; 0 \le \sum _{k \in \operatorname{Finset}.\operatorname{range}\left(\operatorname{Nat}.\operatorname{div}\left(m, 2\right) + 1\right)} (A\left(k\right) \cdot \operatorname{productCoeff}\left(\operatorname{fun} (r:Nat) \mapsto y\left(2 \cdot k + r\right), \operatorname{fun} (r:Nat) \mapsto y\left(2 \cdot \left(m - k\right) + r\right), N\right))\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangGamma/Smoothing.smoothed_weighting` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let y satisfy IsLogConcave, let A be a real sequence and m a natural number, and put h=floor(m/2). Assume that for all i,j <= h with i < j, A(i)>0 implies A(j)>=0, and that the sum of A(i) for i=0,...,h is nonnegative. Then for every natural degree N, the sum over k=0,...,h of A(k) times productCoeff(r maps to y(2k+r),r maps to y(2(m-k)+r),N) is nonnegative. The sign and total-sum hypotheses concern A alone.

Induct simultaneously in the coefficient degree for all derivative-index pairs. The finite Leibniz recurrence makes the next minor the sum of two current minors because the middle products cancel. At the adjacent-index boundary one minor is zero by commutativity. The constant coefficient is the general balancing inequality, obtained by repeated use of the existing balanced_step theorem. Two consecutive balancing steps make P(2k)P(2(m-k)) increase up to the middle; the weighting principle then gives the last theorem. This finite induction proves the same coefficient inequality as the finite Cauchy-Binet argument, without introducing power series or convergence hypotheses.

## References

- Truth anchor: `D5/S3/Analytic/KarpZhangGamma/Smoothing.balanced_product`
- Truth anchor: `D5/S3/Analytic/KarpZhangGamma/Smoothing.binomialProduct`
- Truth anchor: `D5/S3/Analytic/KarpZhangGamma/Smoothing.binomialProduct_comm`
- Truth anchor: `D5/S3/Analytic/KarpZhangGamma/Smoothing.binomialProduct_succ`
- Truth anchor: `D5/S3/Analytic/KarpZhangGamma/Smoothing.productCoeff`
- Truth anchor: `D5/S3/Analytic/KarpZhangGamma/Smoothing.productCoeff_eq`
- Truth anchor: `D5/S3/Analytic/KarpZhangGamma/Smoothing.smoothed_weighting`
- Truth anchor: `D5/S3/Analytic/KarpZhangGamma/Smoothing.smoothing_minor`
- Dependency: [D5/S3/Analytic/KarpZhangGamma/Weighting](Weighting.md)
- Dependency: [D5/S3/Analytic/KarpZhangReciprocal/Result](../KarpZhangReciprocal/Result.md)
