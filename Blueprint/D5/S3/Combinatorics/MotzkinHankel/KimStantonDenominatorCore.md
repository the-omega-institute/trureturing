# KimStantonDenominatorCore

## Abstract

Integer polynomial denominators of contiguous basic hypergeometric coefficients.

**Definition 1.1 (a).**

$$a = (\operatorname{algebraMap}\left((\operatorname{MvPolynomial}\left((\operatorname{Fin}\left(4\right)), \mathbb{Z}\right)), (\operatorname{FractionRing}\left((\operatorname{MvPolynomial}\left((\operatorname{Fin}\left(4\right)), \mathbb{Z}\right))\right)), (\operatorname{MvPolynomial.X}\left(0\right))\right))$$

*Formalization.* `D5/S3/Combinatorics/MotzkinHankel/KimStantonDenominatorCore.a` (`✓ std3`).

*Citation.* Jang Soo Kim and Dennis Stanton (2021). *Three families of q-Lommel polynomials*. DOI: [10.48550/arXiv.2105.10096](https://doi.org/10.48550/arXiv.2105.10096). URL: <https://arxiv.org/abs/2105.10096v3>.

*Commentary.*

The image of polynomial variable 0 in the fraction field of the four-variable integer polynomial ring.

**Definition 1.2 (b).**

$$b = (\operatorname{algebraMap}\left((\operatorname{MvPolynomial}\left((\operatorname{Fin}\left(4\right)), \mathbb{Z}\right)), (\operatorname{FractionRing}\left((\operatorname{MvPolynomial}\left((\operatorname{Fin}\left(4\right)), \mathbb{Z}\right))\right)), (\operatorname{MvPolynomial.X}\left(1\right))\right))$$

*Formalization.* `D5/S3/Combinatorics/MotzkinHankel/KimStantonDenominatorCore.b` (`✓ std3`).

*Citation.* Jang Soo Kim and Dennis Stanton (2021). *Three families of q-Lommel polynomials*. DOI: [10.48550/arXiv.2105.10096](https://doi.org/10.48550/arXiv.2105.10096). URL: <https://arxiv.org/abs/2105.10096v3>.

*Commentary.*

The image of polynomial variable 1 in the fraction field of the four-variable integer polynomial ring.

**Definition 1.3 (c).**

$$c = (\operatorname{algebraMap}\left((\operatorname{MvPolynomial}\left((\operatorname{Fin}\left(4\right)), \mathbb{Z}\right)), (\operatorname{FractionRing}\left((\operatorname{MvPolynomial}\left((\operatorname{Fin}\left(4\right)), \mathbb{Z}\right))\right)), (\operatorname{MvPolynomial.X}\left(2\right))\right))$$

*Formalization.* `D5/S3/Combinatorics/MotzkinHankel/KimStantonDenominatorCore.c` (`✓ std3`).

*Citation.* Jang Soo Kim and Dennis Stanton (2021). *Three families of q-Lommel polynomials*. DOI: [10.48550/arXiv.2105.10096](https://doi.org/10.48550/arXiv.2105.10096). URL: <https://arxiv.org/abs/2105.10096v3>.

*Commentary.*

The image of polynomial variable 2 in the fraction field of the four-variable integer polynomial ring.

**Definition 1.4 (q).**

$$q = (\operatorname{algebraMap}\left((\operatorname{MvPolynomial}\left((\operatorname{Fin}\left(4\right)), \mathbb{Z}\right)), (\operatorname{FractionRing}\left((\operatorname{MvPolynomial}\left((\operatorname{Fin}\left(4\right)), \mathbb{Z}\right))\right)), (\operatorname{MvPolynomial.X}\left(3\right))\right))$$

*Formalization.* `D5/S3/Combinatorics/MotzkinHankel/KimStantonDenominatorCore.q` (`✓ std3`).

*Citation.* Jang Soo Kim and Dennis Stanton (2021). *Three families of q-Lommel polynomials*. DOI: [10.48550/arXiv.2105.10096](https://doi.org/10.48550/arXiv.2105.10096). URL: <https://arxiv.org/abs/2105.10096v3>.

*Commentary.*

The image of polynomial variable 3 in the fraction field of the four-variable integer polynomial ring.

**Definition 1.5 (qShiftedFactorial).**

$$\forall u \in (\operatorname{FractionRing}\left((\operatorname{MvPolynomial}\left((\operatorname{Fin}\left(4\right)), \mathbb{Z}\right))\right)),\; \forall v \in (\operatorname{FractionRing}\left((\operatorname{MvPolynomial}\left((\operatorname{Fin}\left(4\right)), \mathbb{Z}\right))\right)),\; \forall r \in \mathbb{N},\; \operatorname{qShiftedFactorial}\left(u, v, r\right) = (\prod_{j \in \operatorname{Finset.range}\left(r\right)} (1 - u \cdot v^{j}))$$

*Formalization.* `D5/S3/Combinatorics/MotzkinHankel/KimStantonDenominatorCore.qShiftedFactorial` (`✓ std3`).

*Citation.* Jang Soo Kim and Dennis Stanton (2021). *Three families of q-Lommel polynomials*. DOI: [10.48550/arXiv.2105.10096](https://doi.org/10.48550/arXiv.2105.10096). URL: <https://arxiv.org/abs/2105.10096v3>.

*Commentary.*

The finite q-shifted factorial includes the empty product at degree zero.

**Definition 1.6 (F).**

$$\forall A \in (\operatorname{FractionRing}\left((\operatorname{MvPolynomial}\left((\operatorname{Fin}\left(4\right)), \mathbb{Z}\right))\right)),\; \forall B \in (\operatorname{FractionRing}\left((\operatorname{MvPolynomial}\left((\operatorname{Fin}\left(4\right)), \mathbb{Z}\right))\right)),\; \forall C \in (\operatorname{FractionRing}\left((\operatorname{MvPolynomial}\left((\operatorname{Fin}\left(4\right)), \mathbb{Z}\right))\right)),\; \forall Q \in (\operatorname{FractionRing}\left((\operatorname{MvPolynomial}\left((\operatorname{Fin}\left(4\right)), \mathbb{Z}\right))\right)),\; F\left(A, B, C, Q\right) = (\operatorname{PowerSeries.mk}\left((r: \mathbb{N}\mapsto \frac{\operatorname{qShiftedFactorial}\left(A, Q, r\right) \cdot \operatorname{qShiftedFactorial}\left(B, Q, r\right)}{(\operatorname{qShiftedFactorial}\left(C, Q, r\right) \cdot \operatorname{qShiftedFactorial}\left(Q, Q, r\right))})\right))$$

*Formalization.* `D5/S3/Combinatorics/MotzkinHankel/KimStantonDenominatorCore.F` (`✓ std3`).

*Citation.* Jang Soo Kim and Dennis Stanton (2021). *Three families of q-Lommel polynomials*. DOI: [10.48550/arXiv.2105.10096](https://doi.org/10.48550/arXiv.2105.10096). URL: <https://arxiv.org/abs/2105.10096v3>.

*Commentary.*

The standard Gasper–Rahman series includes both lower q-shifted factorials, including the one whose parameter equals q.

**Definition 1.7 (D).**

$$\forall n \in \mathbb{N},\; D\left(n\right) = (\prod_{k \in \operatorname{Finset.range}\left((n + 1)\right)} (1 - c \cdot q^{k})^{(\operatorname{Nat.div}\left((n + 1), (k + 1)\right))})$$

*Formalization.* `D5/S3/Combinatorics/MotzkinHankel/KimStantonDenominatorCore.D` (`✓ std3`).

*Citation.* Jang Soo Kim and Dennis Stanton (2021). *Three families of q-Lommel polynomials*. DOI: [10.48550/arXiv.2105.10096](https://doi.org/10.48550/arXiv.2105.10096). URL: <https://arxiv.org/abs/2105.10096v3>.

*Commentary.*

The natural-number quotient Nat.div is floor division; the product includes k = n.

**Definition 1.8 (p).**

$$\forall k \in \mathbb{N},\; p\left(k\right) = (1 - \operatorname{MvPolynomial.X}\left(2\right) \cdot \operatorname{MvPolynomial.X}\left(3\right)^{k})$$

*Formalization.* `D5/S3/Combinatorics/MotzkinHankel/KimStantonDenominatorCore.p` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The polynomial factor at index k is 1 minus the product of the lower parameter and the kth power of q.

**Theorem 1.9 (nonzeroFamily).**

$$\forall r \in (\operatorname{MvPolynomial}\left((\operatorname{Fin}\left(4\right)), \mathbb{Z}\right)),\; (r \in \operatorname{Set.range}\left(p\right)) \Rightarrow r \ne 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/MotzkinHankel/KimStantonDenominatorCore.nonzeroFamily` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every polynomial in the family of lower-parameter factors is nonzero.

**Theorem 1.10 (one_sub_q_pow_ne_zero).**

$$\forall n \in \mathbb{N},\; (n \ne 0) \Rightarrow 1 - q^{n} \ne 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/MotzkinHankel/KimStantonDenominatorCore.one_sub_q_pow_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A nonzero natural power of the indeterminate q differs from one.

**Theorem 1.11 (variable_factor_ne_zero).**

$$\forall i \in \operatorname{Fin}\left(4\right),\; \forall j \in \operatorname{Fin}\left(4\right),\; \forall m \in \mathbb{N},\; 1 - \operatorname{algebraMap}\left((\operatorname{MvPolynomial}\left((\operatorname{Fin}\left(4\right)), \mathbb{Z}\right)), (\operatorname{FractionRing}\left((\operatorname{MvPolynomial}\left((\operatorname{Fin}\left(4\right)), \mathbb{Z}\right))\right)), (\operatorname{MvPolynomial.X}\left(i\right))\right) \cdot \operatorname{algebraMap}\left((\operatorname{MvPolynomial}\left((\operatorname{Fin}\left(4\right)), \mathbb{Z}\right)), (\operatorname{FractionRing}\left((\operatorname{MvPolynomial}\left((\operatorname{Fin}\left(4\right)), \mathbb{Z}\right))\right)), (\operatorname{MvPolynomial.X}\left(j\right))\right)^{m} \ne 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/MotzkinHankel/KimStantonDenominatorCore.variable_factor_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed factor is nonzero for every pair of polynomial variables and every natural exponent.

**Theorem 1.12 (closureLeNonzero).**

$$\forall R \in \operatorname{Type},\; [\operatorname{CommRing}\left(R\right)] [\operatorname{IsDomain}\left(R\right)] \forall s \in \operatorname{Set}\left(R\right),\; (\forall p \in s,\; p \ne 0) \Rightarrow \operatorname{Submonoid.closure}\left(s\right) \le \operatorname{nonZeroDivisors}\left(R\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/MotzkinHankel/KimStantonDenominatorCore.closureLeNonzero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The multiplicative closure of a set of nonzero elements of a domain contains no zero divisor.

**Theorem 1.13 (quotient_coefficients_mem).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] \forall T \in \operatorname{Subring}\left(K\right),\; \forall u \in \mathbb{N} \to \operatorname{PowerSeries}\left(K\right),\; \forall b \in \mathbb{N} \to K,\; \forall alpha \in \mathbb{N} \to K,\; \forall ell \in \mathbb{N} \to K,\; (\forall m \in \mathbb{N},\; \operatorname{constantCoeff}\left((u\left(m\right))\right) = 1) \Rightarrow \left((\forall m \in \mathbb{N},\; b\left(m\right) \in T) \Rightarrow \left((\forall m \in \mathbb{N},\; alpha\left(m\right) \in T) \Rightarrow \left((\forall m \in \mathbb{N},\; ell\left(m\right) \in T) \Rightarrow \left((\forall m \in \mathbb{N},\; u\left(m\right) = (1 - C\left((b\left(m\right))\right) \cdot X) \cdot u\left((m + 1)\right) - (C\left((alpha\left(m\right))\right) \cdot X + C\left((ell\left(m\right))\right) \cdot X^{2}) \cdot u\left((m + 2)\right)) \Rightarrow \left(\forall n \in \mathbb{N},\; \forall m \in \mathbb{N},\; \operatorname{coeff}\left(n, (u\left((m + 1)\right) \cdot (u\left(m\right))^{-1})\right) \in T\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/MotzkinHankel/KimStantonDenominatorCore.quotient_coefficients_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A normalized three-term series recurrence whose scalar weights lie in a subring gives adjacent quotient coefficients in that subring.

**Theorem 1.14 (F_constant).**

$$\forall A \in (\operatorname{FractionRing}\left((\operatorname{MvPolynomial}\left((\operatorname{Fin}\left(4\right)), \mathbb{Z}\right))\right)),\; \forall B \in (\operatorname{FractionRing}\left((\operatorname{MvPolynomial}\left((\operatorname{Fin}\left(4\right)), \mathbb{Z}\right))\right)),\; \forall C \in (\operatorname{FractionRing}\left((\operatorname{MvPolynomial}\left((\operatorname{Fin}\left(4\right)), \mathbb{Z}\right))\right)),\; \forall Q \in (\operatorname{FractionRing}\left((\operatorname{MvPolynomial}\left((\operatorname{Fin}\left(4\right)), \mathbb{Z}\right))\right)),\; \operatorname{constantCoeff}\left((F\left(A, B, C, Q\right))\right) = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/MotzkinHankel/KimStantonDenominatorCore.F_constant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formal basic hypergeometric series has constant coefficient one.

**Theorem 1.15 (coeff_F_succ).**

$$\forall A \in (\operatorname{FractionRing}\left((\operatorname{MvPolynomial}\left((\operatorname{Fin}\left(4\right)), \mathbb{Z}\right))\right)),\; \forall B \in (\operatorname{FractionRing}\left((\operatorname{MvPolynomial}\left((\operatorname{Fin}\left(4\right)), \mathbb{Z}\right))\right)),\; \forall C \in (\operatorname{FractionRing}\left((\operatorname{MvPolynomial}\left((\operatorname{Fin}\left(4\right)), \mathbb{Z}\right))\right)),\; \forall Q \in (\operatorname{FractionRing}\left((\operatorname{MvPolynomial}\left((\operatorname{Fin}\left(4\right)), \mathbb{Z}\right))\right)),\; \forall n \in \mathbb{N},\; \operatorname{coeff}\left((n + 1), (F\left(A, B, C, Q\right))\right) = \frac{\operatorname{coeff}\left(n, (F\left(A, B, C, Q\right))\right) \cdot ((1 - A \cdot Q^{n}) \cdot (1 - B \cdot Q^{n}))}{((1 - C \cdot Q^{n}) \cdot (1 - Q^{(n + 1)}))}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/MotzkinHankel/KimStantonDenominatorCore.coeff_F_succ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The next coefficient is obtained by multiplying the current coefficient by the displayed rational factor.

**Theorem 1.16 (coeff_shift_abc).**

$$\forall A \in (\operatorname{FractionRing}\left((\operatorname{MvPolynomial}\left((\operatorname{Fin}\left(4\right)), \mathbb{Z}\right))\right)),\; \forall B \in (\operatorname{FractionRing}\left((\operatorname{MvPolynomial}\left((\operatorname{Fin}\left(4\right)), \mathbb{Z}\right))\right)),\; \forall C \in (\operatorname{FractionRing}\left((\operatorname{MvPolynomial}\left((\operatorname{Fin}\left(4\right)), \mathbb{Z}\right))\right)),\; \forall Q \in (\operatorname{FractionRing}\left((\operatorname{MvPolynomial}\left((\operatorname{Fin}\left(4\right)), \mathbb{Z}\right))\right)),\; \forall n \in \mathbb{N},\; (1 - A \ne 0) \Rightarrow \left((1 - B \ne 0) \Rightarrow \left((\forall m \in \mathbb{N},\; 1 - C \cdot Q^{m} \ne 0) \Rightarrow \left((\forall m \in \mathbb{N},\; 1 - Q^{(m + 1)} \ne 0) \Rightarrow \operatorname{coeff}\left(n, (F\left((A \cdot Q), (B \cdot Q), (C \cdot Q), Q\right))\right) = \frac{\operatorname{coeff}\left(n, (F\left(A, B, C, Q\right))\right) \cdot ((1 - A \cdot Q^{n}) \cdot (1 - B \cdot Q^{n}) \cdot (1 - C))}{((1 - A) \cdot (1 - B) \cdot (1 - C \cdot Q^{n}))}\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/MotzkinHankel/KimStantonDenominatorCore.coeff_shift_abc` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiplying all three parameters by q gives the displayed coefficient identity when its denominator factors are nonzero.

**Theorem 1.17 (heine_contiguous).**

$$\forall A \in (\operatorname{FractionRing}\left((\operatorname{MvPolynomial}\left((\operatorname{Fin}\left(4\right)), \mathbb{Z}\right))\right)),\; \forall B \in (\operatorname{FractionRing}\left((\operatorname{MvPolynomial}\left((\operatorname{Fin}\left(4\right)), \mathbb{Z}\right))\right)),\; \forall C \in (\operatorname{FractionRing}\left((\operatorname{MvPolynomial}\left((\operatorname{Fin}\left(4\right)), \mathbb{Z}\right))\right)),\; \forall Q \in (\operatorname{FractionRing}\left((\operatorname{MvPolynomial}\left((\operatorname{Fin}\left(4\right)), \mathbb{Z}\right))\right)),\; (1 - A \ne 0) \Rightarrow \left((1 - B \ne 0) \Rightarrow \left((\forall m \in \mathbb{N},\; 1 - C \cdot Q^{m} \ne 0) \Rightarrow \left((\forall m \in \mathbb{N},\; 1 - Q^{(m + 1)} \ne 0) \Rightarrow F\left((A \cdot Q), B, (C \cdot Q), Q\right) - F\left(A, B, C, Q\right) = \operatorname{PowerSeries.C}\left((\frac{((1 - B) \cdot (A - C))}{((1 - C) \cdot (1 - C \cdot Q))})\right) \cdot X \cdot F\left((A \cdot Q), (B \cdot Q), (C \cdot Q^{2}), Q\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/MotzkinHankel/KimStantonDenominatorCore.heine_contiguous` (`✓ std3`). ∎

*Citation.* Jang Soo Kim and Dennis Stanton (2021). *Three families of q-Lommel polynomials*. DOI: [10.48550/arXiv.2105.10096](https://doi.org/10.48550/arXiv.2105.10096). URL: <https://arxiv.org/abs/2105.10096v3>.

*Commentary.*

Heine’s contiguous identity relates the unshifted series, the first upper and lower shift, and the next simultaneous upper shift.

**Definition 1.18 (S).**

$$S = (\operatorname{Localization.subalgebra.ofField}\left((\operatorname{FractionRing}\left((\operatorname{MvPolynomial}\left((\operatorname{Fin}\left(4\right)), \mathbb{Z}\right))\right)), (\operatorname{Submonoid.closure}\left((\operatorname{Set.range}\left(p\right))\right)), (\operatorname{closureLeNonzero}\left((\operatorname{Set.range}\left(p\right)), \operatorname{nonzeroFamily}\right))\right))$$

*Formalization.* `D5/S3/Combinatorics/MotzkinHankel/KimStantonDenominatorCore.S` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This subalgebra localizes the integer polynomial ring by the multiplicative closure of the lower-parameter factors.

**Theorem 1.19 (S_inv_p).**

$$\forall k \in \mathbb{N},\; (1 - c \cdot q^{k})^{-1} \in S$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/MotzkinHankel/KimStantonDenominatorCore.S_inv_p` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The reciprocal of every lower-parameter factor belongs to the displayed localization.

**Definition 1.20 (ratio).**

$$\forall A \in (\operatorname{MvPolynomial}\left((\operatorname{Fin}\left(4\right)), \mathbb{Z}\right)),\; \forall B \in (\operatorname{MvPolynomial}\left((\operatorname{Fin}\left(4\right)), \mathbb{Z}\right)),\; \forall Aprime \in (\operatorname{MvPolynomial}\left((\operatorname{Fin}\left(4\right)), \mathbb{Z}\right)),\; \forall Bprime \in (\operatorname{MvPolynomial}\left((\operatorname{Fin}\left(4\right)), \mathbb{Z}\right)),\; \operatorname{ratio}\left(A, B, Aprime, Bprime\right) = (F\left((\operatorname{algebraMap}\left((\operatorname{MvPolynomial}\left((\operatorname{Fin}\left(4\right)), \mathbb{Z}\right)), (\operatorname{FractionRing}\left((\operatorname{MvPolynomial}\left((\operatorname{Fin}\left(4\right)), \mathbb{Z}\right))\right)), Aprime\right)), (\operatorname{algebraMap}\left((\operatorname{MvPolynomial}\left((\operatorname{Fin}\left(4\right)), \mathbb{Z}\right)), (\operatorname{FractionRing}\left((\operatorname{MvPolynomial}\left((\operatorname{Fin}\left(4\right)), \mathbb{Z}\right))\right)), Bprime\right)), (c \cdot q), q\right) \cdot (F\left((\operatorname{algebraMap}\left((\operatorname{MvPolynomial}\left((\operatorname{Fin}\left(4\right)), \mathbb{Z}\right)), (\operatorname{FractionRing}\left((\operatorname{MvPolynomial}\left((\operatorname{Fin}\left(4\right)), \mathbb{Z}\right))\right)), A\right)), (\operatorname{algebraMap}\left((\operatorname{MvPolynomial}\left((\operatorname{Fin}\left(4\right)), \mathbb{Z}\right)), (\operatorname{FractionRing}\left((\operatorname{MvPolynomial}\left((\operatorname{Fin}\left(4\right)), \mathbb{Z}\right))\right)), B\right)), c, q\right))^{-1})$$

*Formalization.* `D5/S3/Combinatorics/MotzkinHankel/KimStantonDenominatorCore.ratio` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two upper parameters are polynomial expressions, and the numerator series shifts the lower parameter once by q.

**Theorem 1.21 (denominator_from_localization).**

$$\forall A \in (\operatorname{MvPolynomial}\left((\operatorname{Fin}\left(4\right)), \mathbb{Z}\right)),\; \forall B \in (\operatorname{MvPolynomial}\left((\operatorname{Fin}\left(4\right)), \mathbb{Z}\right)),\; \forall Aprime \in (\operatorname{MvPolynomial}\left((\operatorname{Fin}\left(4\right)), \mathbb{Z}\right)),\; \forall Bprime \in (\operatorname{MvPolynomial}\left((\operatorname{Fin}\left(4\right)), \mathbb{Z}\right)),\; (\forall n \in \mathbb{N},\; \operatorname{coeff}\left(n, (\operatorname{ratio}\left(A, B, Aprime, Bprime\right))\right) \in S) \Rightarrow \left(\forall n \in \mathbb{N},\; \exists P \in (\operatorname{MvPolynomial}\left((\operatorname{Fin}\left(4\right)), \mathbb{Z}\right)),\; \frac{\operatorname{coeff}\left(n, (\operatorname{ratio}\left(A, B, Aprime, Bprime\right))\right)}{(1 - c)} = \frac{\operatorname{algebraMap}\left((\operatorname{MvPolynomial}\left((\operatorname{Fin}\left(4\right)), \mathbb{Z}\right)), (\operatorname{FractionRing}\left((\operatorname{MvPolynomial}\left((\operatorname{Fin}\left(4\right)), \mathbb{Z}\right))\right)), P\right)}{D\left(n\right)}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/MotzkinHankel/KimStantonDenominatorCore.denominator_from_localization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If every ratio coefficient lies in the displayed localization, the floor exponent product clears its denominator and gives an integer polynomial numerator.

## References

- Truth anchor: `D5/S3/Combinatorics/MotzkinHankel/KimStantonDenominatorCore.D`
- Truth anchor: `D5/S3/Combinatorics/MotzkinHankel/KimStantonDenominatorCore.F`
- Truth anchor: `D5/S3/Combinatorics/MotzkinHankel/KimStantonDenominatorCore.F_constant`
- Truth anchor: `D5/S3/Combinatorics/MotzkinHankel/KimStantonDenominatorCore.S`
- Truth anchor: `D5/S3/Combinatorics/MotzkinHankel/KimStantonDenominatorCore.S_inv_p`
- Truth anchor: `D5/S3/Combinatorics/MotzkinHankel/KimStantonDenominatorCore.a`
- Truth anchor: `D5/S3/Combinatorics/MotzkinHankel/KimStantonDenominatorCore.b`
- Truth anchor: `D5/S3/Combinatorics/MotzkinHankel/KimStantonDenominatorCore.c`
- Truth anchor: `D5/S3/Combinatorics/MotzkinHankel/KimStantonDenominatorCore.closureLeNonzero`
- Truth anchor: `D5/S3/Combinatorics/MotzkinHankel/KimStantonDenominatorCore.coeff_F_succ`
- Truth anchor: `D5/S3/Combinatorics/MotzkinHankel/KimStantonDenominatorCore.coeff_shift_abc`
- Truth anchor: `D5/S3/Combinatorics/MotzkinHankel/KimStantonDenominatorCore.denominator_from_localization`
- Truth anchor: `D5/S3/Combinatorics/MotzkinHankel/KimStantonDenominatorCore.heine_contiguous`
- Truth anchor: `D5/S3/Combinatorics/MotzkinHankel/KimStantonDenominatorCore.nonzeroFamily`
- Truth anchor: `D5/S3/Combinatorics/MotzkinHankel/KimStantonDenominatorCore.one_sub_q_pow_ne_zero`
- Truth anchor: `D5/S3/Combinatorics/MotzkinHankel/KimStantonDenominatorCore.p`
- Truth anchor: `D5/S3/Combinatorics/MotzkinHankel/KimStantonDenominatorCore.q`
- Truth anchor: `D5/S3/Combinatorics/MotzkinHankel/KimStantonDenominatorCore.qShiftedFactorial`
- Truth anchor: `D5/S3/Combinatorics/MotzkinHankel/KimStantonDenominatorCore.quotient_coefficients_mem`
- Truth anchor: `D5/S3/Combinatorics/MotzkinHankel/KimStantonDenominatorCore.ratio`
- Truth anchor: `D5/S3/Combinatorics/MotzkinHankel/KimStantonDenominatorCore.variable_factor_ne_zero`
