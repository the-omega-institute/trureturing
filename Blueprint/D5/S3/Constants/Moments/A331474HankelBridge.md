# A331474 Signed Hankel Bridge

## Abstract

The literal A331473 moments and their A331474 Hankel determinants are connected to a signed period-two continuant, yielding an exact all-order scalar bridge.

All indices below are natural numbers. Integer-valued sequences are written with subscripts. The symbol X is the polynomial indeterminate, coeff selects a polynomial coefficient, and det is the determinant of the displayed finite matrix. These definitions use the literal offset-zero OEIS source, not a recurrence-defined replacement for its Hankel transform.

**Definition 1.1 (Unsigned Catalan-derivative moments).**

$$\forall n \in \mathbb{N}, b_{n} = \operatorname{binom}\left(2 \cdot n + 2, n\right)$$

*Formalization.* `D5/S3/Constants/Moments/A331474HankelBridge.b` (`✓ std3`).

*Citation.* Paul Barry (2020). *OEIS A331474, Hankel transform of A331473*. URL: <https://oeis.org/A331474>.

*Commentary.*

The moment b(n) is exactly binomial(2n+2,n), equivalently (n+1) times the Catalan number of index n+1. It is the coefficient sequence obtained by differentiating the Catalan power series.

**Definition 1.2 (Literal alternating source sequence).**

$$\forall n \in \mathbb{N}, s_{n} = \sum_{k = 0}^{n} (-1)^{n - k} \cdot \operatorname{binom}\left(2 \cdot k + 2, k\right)$$

*Formalization.* `D5/S3/Constants/Moments/A331474HankelBridge.s` (`✓ std3`).

*Citation.* Paul Barry (2020). *OEIS A331474, Hankel transform of A331473*. URL: <https://oeis.org/A331474>.

*Commentary.*

This is the full alternating binomial transform printed in A331473, with k ranging from zero through n and with no recurrence substituted for it.

**Definition 1.3 (Literal Hankel determinant).**

$$\forall n \in \mathbb{N}, H_{n} = \operatorname{det}\left((s_{i + j})_{0 \leq i,j \leq n}\right)$$

*Formalization.* `D5/S3/Constants/Moments/A331474HankelBridge.H` (`✓ std3`).

*Citation.* Paul Barry (2020). *OEIS A331474, Hankel transform of A331473*. URL: <https://oeis.org/A331474>.

*Commentary.*

H(n) is the determinant of the actual (n+1)-square Hankel matrix of s. Consequently the final generating function is about PowerSeries.mk H, rather than a sequence introduced later by its recurrence.

**Definition 1.4 (Period-two diagonal coefficient).**

$$\forall n \in \mathbb{N}, a_{n} = \operatorname{ite}\left(\operatorname{Even}\left(n\right), 4, 0\right)$$

*Formalization.* `D5/S3/Constants/Moments/A331474HankelBridge.a` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul Barry (2020). *OEIS A331474, Hankel transform of A331473*. URL: <https://oeis.org/A331474>.

*Acknowledgement.* Radica Bojičić; M. D. Petković; Paul Barry (2025). *Hankel transform of linear combination of three consecutive Catalan numbers*. DOI: [10.15672/hujms.1564485](https://doi.org/10.15672/hujms.1564485).

*Commentary.*

The source-specific monic continuant uses diagonal coefficient 4 at even indices and 0 at odd indices. This period-two tail is derived from the Catalan derivative equation.

**Definition 1.5 (Signed monic continuants).**

$$\begin{aligned}P_{0} = 1\\P_{1} = X - 4\\\forall m \in \mathbb{N}, P_{m + 2} = (X - a_{m + 1}) \cdot P_{m + 1} + P_{m}\end{aligned}$$

*Formalization.* `D5/S3/Constants/Moments/A331474HankelBridge.P` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul Barry (2020). *OEIS A331474, Hankel transform of A331473*. URL: <https://oeis.org/A331474>.

*Acknowledgement.* Radica Bojičić; M. D. Petković; Paul Barry (2025). *Hankel transform of linear combination of three consecutive Catalan numbers*. DOI: [10.15672/hujms.1564485](https://doi.org/10.15672/hujms.1564485).

*Commentary.*

The polynomials are monic: P(0)=1, P(1)=X-4, and P(m+2)=(X-a(m+1))P(m+1)+P(m). The plus sign gives signed squared norms (-1)^k; positivity is neither assumed nor true here.

**Definition 1.6 (Unsigned moment functional).**

$$\forall f \in \mathbb{Z}[X], \operatorname{B}\left(f\right) = \sum_{n \in \mathbb{N}} \operatorname{coeff}\left(f, n\right) \cdot b_{n}$$

*Formalization.* `D5/S3/Constants/Moments/A331474HankelBridge.B` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul Barry (2020). *OEIS A331474, Hankel transform of A331473*. URL: <https://oeis.org/A331474>.

*Acknowledgement.* Radica Bojičić; M. D. Petković; Paul Barry (2025). *Hankel transform of linear combination of three consecutive Catalan numbers*. DOI: [10.15672/hujms.1564485](https://doi.org/10.15672/hujms.1564485).

*Commentary.*

B evaluates an integer polynomial by weighting every coefficient with b. The Catalan derivative equation supplies the two alternating tails used to prove orthogonality of the monic continuants.

**Definition 1.7 (Literal alternating moment functional).**

$$\forall f \in \mathbb{Z}[X], \operatorname{S}\left(f\right) = \sum_{n \in \mathbb{N}} \operatorname{coeff}\left(f, n\right) \cdot s_{n}$$

*Formalization.* `D5/S3/Constants/Moments/A331474HankelBridge.S` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul Barry (2020). *OEIS A331474, Hankel transform of A331473*. URL: <https://oeis.org/A331474>.

*Acknowledgement.* Radica Bojičić; M. D. Petković; Paul Barry (2025). *Hankel transform of linear combination of three consecutive Catalan numbers*. DOI: [10.15672/hujms.1564485](https://doi.org/10.15672/hujms.1564485).

*Commentary.*

S evaluates a polynomial against the literal sequence s. The source relation b(n+1)=s(n+1)+s(n) transfers the unsigned Catalan identities to this signed functional.

**Definition 1.8 (Continuant constant terms).**

$$\forall n \in \mathbb{N}, p_{n} = \operatorname{coeff}\left(P_{n}, 0\right)$$

*Formalization.* `D5/S3/Constants/Moments/A331474HankelBridge.p` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul Barry (2020). *OEIS A331474, Hankel transform of A331473*. URL: <https://oeis.org/A331474>.

*Acknowledgement.* Radica Bojičić; M. D. Petković; Paul Barry (2025). *Hankel transform of linear combination of three consecutive Catalan numbers*. DOI: [10.15672/hujms.1564485](https://doi.org/10.15672/hujms.1564485).

*Commentary.*

The scalar p(n) is the constant coefficient of P(n). Its exact initial values and recurrence are included in the bridge theorem below.

**Definition 1.9 (Literal functional values).**

$$\forall n \in \mathbb{N}, u_{n} = \operatorname{S}\left(P_{n}\right)$$

*Formalization.* `D5/S3/Constants/Moments/A331474HankelBridge.u` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul Barry (2020). *OEIS A331474, Hankel transform of A331473*. URL: <https://oeis.org/A331474>.

*Acknowledgement.* Radica Bojičić; M. D. Petković; Paul Barry (2025). *Hankel transform of linear combination of three consecutive Catalan numbers*. DOI: [10.15672/hujms.1564485](https://doi.org/10.15672/hujms.1564485).

*Commentary.*

The scalar u(n) is S(P(n)). Its exact initial values and source-specific recurrence are included in the bridge theorem below.

**Theorem 1.10 (Literal determinant equals the signed kernel).**

$$\begin{aligned}\forall n \in \mathbb{N},\\H_{n} = \prod_{k = 0}^{n} (-1)^{k} \cdot \sum_{k = 0}^{n} (-1)^{k} p_{k} u_{k} \land\\p_{0} = 1 \land p_{1} = -4 \land\\(\forall m \in \mathbb{N}, p_{m + 2} = -a_{m + 1} \cdot p_{m + 1} + p_{m}) \land\\u_{0} = 1 \land u_{1} = -1 \land u_{2} = 1 \land\\\forall m \in \mathbb{N}, 2 \leq m \Rightarrow u_{m + 1} = -(a_{m} + 1) \cdot u_{m} + u_{m - 1}.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Constants/Moments/A331474HankelBridge.literal_hankel_eq_signed_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul Barry (2020). *OEIS A331474, Hankel transform of A331473*. URL: <https://oeis.org/A331474>.

*Acknowledgement.* Radica Bojičić; M. D. Petković; Paul Barry (2025). *Hankel transform of linear combination of three consecutive Catalan numbers*. DOI: [10.15672/hujms.1564485](https://doi.org/10.15672/hujms.1564485).

*Commentary.*

The Catalan derivative coefficients first give two period-two power-series tails. Their continuant error identity yields signed monomial orthogonality, which extends to polynomial orthogonality. The resulting monic coefficient matrix diagonalizes the Gram matrix with diagonal entries (-1)^k. Negative entries are intentional, so no positive-real Gram argument is used.

A division-free adjugate identity then replaces matrix inversion. For the actual adjacent-column coefficient c=-1, the Hankel determinant is converted to a Cramer determinant and then to the signed reproducing kernel. The same proof derives p(0)=1, p(1)=-4 and its recurrence, and u(0)=1, u(1)=-1, u(2)=1 and its quantified recurrence. No finite-prefix certificate or positivity hypothesis carries any part of the result.

## References

- Truth anchor: `D5/S3/Constants/Moments/A331474HankelBridge.B`
- Truth anchor: `D5/S3/Constants/Moments/A331474HankelBridge.H`
- Truth anchor: `D5/S3/Constants/Moments/A331474HankelBridge.P`
- Truth anchor: `D5/S3/Constants/Moments/A331474HankelBridge.S`
- Truth anchor: `D5/S3/Constants/Moments/A331474HankelBridge.a`
- Truth anchor: `D5/S3/Constants/Moments/A331474HankelBridge.b`
- Truth anchor: `D5/S3/Constants/Moments/A331474HankelBridge.literal_hankel_eq_signed_kernel`
- Truth anchor: `D5/S3/Constants/Moments/A331474HankelBridge.p`
- Truth anchor: `D5/S3/Constants/Moments/A331474HankelBridge.s`
- Truth anchor: `D5/S3/Constants/Moments/A331474HankelBridge.u`
