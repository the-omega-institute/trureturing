# Exact Prime-Two Majorant Threshold

## Abstract

The prime-2 majorant has a unique unit crossing below three fifths, and the prime-2 factor and full golden Euler product are nonzero above it.

**Theorem 1.1 (The majorant threshold gives a sharper zero-free half-plane).**

$$\begin{aligned}\forall sigma\in \mathbb{R}, \operatorname{f}(sigma) := (2)^{-sigma \times \varphi^{2}} + (2)^{-sigma},\\sigmaStar := primeTwoThreshold,\\\operatorname{ContinuousOn}(f, (0, \infty)) \land\\\operatorname{StrictAntiOn}(f, (0, \infty)) \land\\(sigmaStar\in (\frac{1}{\varphi^{2}}, \frac{3}{5}) \land \operatorname{f}(sigmaStar) = 1 \land \forall tau\in (\frac{1}{\varphi^{2}}, \frac{3}{5}), \operatorname{f}(tau) = 1 \Rightarrow tau = sigmaStar) \land\\(\forall s\in \mathbb{C}, sigmaStar < \Re(s) \Rightarrow \sum_{v\in \mathbb{N}}2^{-s \times \operatorname{o5Beta}(v)} \neq 0) \land\\(\forall s\in \mathbb{C}, sigmaStar < \Re(s) \Rightarrow \prod_{p\in \operatorname{Primes}(\mathbb{N})}\sum_{v\in \mathbb{N}}p^{-s \times \operatorname{o5Beta}(v)} \neq 0).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/EulerGerm/GermProductNonvanishingExactThreshold.germ_product_nonvanishing_exact_threshold` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This theorem sits in the golden Euler-germ extraction ladder of OACTC Parts 580 and 581, on the RH-route O-5 control line. It replaces the rational endpoint three fifths by the unique unit crossing of the explicit two-term prime-2 majorant.

The majorant is continuous and strictly decreasing on the positive ray. Exact endpoint estimates put its crossing strictly between one over phi squared and three fifths. Above that crossing, the parameterized geometric-tail estimate has norm below one, so it cannot cancel the vacuum term of the prime-2 local factor.

Odd-prime local factors are already nonzero throughout the open convergence half-plane. The frozen infinite-product bridge then turns pointwise local nonvanishing into nonvanishing of the full t-product; convergence is carried by its separate frozen input.

The threshold here belongs only to this explicit majorant method. The theorem does not identify the actual boundary of the local zero set, does not assert a zero below the threshold, and does not establish O-5 or the Riemann hypothesis.

## References

- Truth anchor: `D5/S3/Analytic/EulerGerm/GermProductNonvanishingExactThreshold.germ_product_nonvanishing_exact_threshold`
- Dependency: [D5/S3/Analytic/EulerGerm/GermProductNonvanishingAboveThreeFifths](GermProductNonvanishingAboveThreeFifths.md)
