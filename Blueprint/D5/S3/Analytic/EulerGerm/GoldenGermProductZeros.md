# Golden Germ Product Zeros

## Abstract

The golden germ product has exactly the prime-2 zeros on its convergence half-plane, and any such zeros are isolated.

**Theorem 1.1 (Golden germ zeros localize at prime 2 and are isolated).**

$$\begin{aligned}\frac{1}{\varphi^{2}} < \Re(1) \land \prod_{p\in \operatorname{Primes}(\mathbb{N})}\sum_{v\in \mathbb{N}}p^{-1 \times \operatorname{o5Beta}(v)} \neq 0 \land\\(\forall s\in \mathbb{C}, \frac{1}{\varphi^{2}} < \Re(s) \Rightarrow (\prod_{p\in \operatorname{Primes}(\mathbb{N})}\sum_{v\in \mathbb{N}}p^{-s \times \operatorname{o5Beta}(v)} \neq 0 \Leftrightarrow \sum_{v\in \mathbb{N}}2^{-s \times \operatorname{o5Beta}(v)} \neq 0)) \land\\(\forall z\in \mathbb{C}, \frac{1}{\varphi^{2}} < \Re(z) \Rightarrow \operatorname{Eventually}(w \mapsto \prod_{p\in \operatorname{Primes}(\mathbb{N})}\sum_{v\in \mathbb{N}}p^{-w \times \operatorname{o5Beta}(v)} \neq 0, \operatorname{nhdsNE}(z))) \land\\(\forall z\in \mathbb{C}, \frac{1}{\varphi^{2}} < \Re(z) \Rightarrow \operatorname{Eventually}(w \mapsto \sum_{v\in \mathbb{N}}2^{-w \times \operatorname{o5Beta}(v)} \neq 0, \operatorname{nhdsNE}(z))).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/EulerGerm/GoldenGermProductZeros.golden_germ_product_zeros` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The domain inequality points to the right: the real part is strictly greater than one over phi squared. At every point of this open half-plane, the full prime product is nonzero exactly when the explicit prime-2 scalar series is nonzero.

The theorem exhibits s = 1 inside the half-plane with nonzero product. Thus the domain is nonempty and the analytic product is not identically zero before the identity theorem is used.

Every point in the half-plane has a punctured ambient neighborhood free of product zeros and prime-2 local-factor zeros. The known unconditional region has real part greater than or equal to two thirds. Whether any zero exists in the strip where one over phi squared is strictly less than the real part and the real part is strictly less than two thirds remains open.

## References

- Truth anchor: `D5/S3/Analytic/EulerGerm/GoldenGermProductZeros.golden_germ_product_zeros`
