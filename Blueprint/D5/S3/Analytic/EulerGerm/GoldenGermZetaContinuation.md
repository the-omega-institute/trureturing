# Golden Germ Zeta Continuation

## Abstract

The zeta-normalized product canonically continues the golden germ to its larger half-plane and remains positive on the real ray.

**Theorem 1.1 (The normalized product gives the unique larger-half-plane continuation).**

$$\begin{aligned}G: \mathbb{C} \to \mathbb{C},\\\forall s\in \mathbb{C}, \operatorname{G}(s) := \prod_{p\in \operatorname{Primes}(\mathbb{N})}(1 - p^{-s \times \varphi^{2}}) \times \sum_{v\in \mathbb{N}}p^{-s \times \operatorname{o5Beta}(v)},\\(\exists! Zqc: \{s\in \mathbb{C} \mid \frac{1}{\varphi^{3}} < \Re(s)\} \to \mathbb{C},\\(\forall s\in \mathbb{C}, \frac{1}{\varphi^{2}} < \Re(s) \Rightarrow \operatorname{Zqc}(s) = \prod_{p\in \operatorname{Primes}(\mathbb{N})}\sum_{v\in \mathbb{N}}p^{-s \times \operatorname{o5Beta}(v)}) \land (\forall s\in \mathbb{C}, \frac{1}{\varphi^{3}} < \Re(s) \Rightarrow \operatorname{Zqc}(s) = \operatorname{riemannZeta}(\varphi^{2} \times s) \times \operatorname{G}(s))) \land\\(\forall s\in \mathbb{C}, \frac{1}{\varphi^{3}} < \Re(s) \Rightarrow \operatorname{Summable}(p: \operatorname{Primes}(\mathbb{N}) \mapsto \lvert (1 - p^{-s \times \varphi^{2}}) \times \sum_{v\in \mathbb{N}}p^{-s \times \operatorname{o5Beta}(v)} - 1 \rvert)) \land (\forall sigma\in \mathbb{R}, \frac{1}{\varphi^{3}} < sigma \Rightarrow 0 < \Re(\operatorname{G}(sigma)) \land \operatorname{Im}(\operatorname{G}(sigma)) = 0).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/EulerGerm/GoldenGermZetaContinuation.golden_germ_zeta_continuation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The continued function is quantified on the full normalized-product half-plane rather than defined as the desired factorization.

The frozen factorization proves that this function agrees with the canonical germ prime product on its original convergence domain. The displayed computation rule then determines it uniquely on the larger half-plane.

The same frozen estimates supply absolute convergence of the normalized prime factors and positivity on the real ray. The source's numerical window certificate is an empirical remark outside the named theorem.

## References

- Truth anchor: `D5/S3/Analytic/EulerGerm/GoldenGermZetaContinuation.golden_germ_zeta_continuation`
- Dependency: [D5/S3/Analytic/EulerGerm/GoldenGermZetaFactorization](GoldenGermZetaFactorization.md)
