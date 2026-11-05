# FiniteSlitCompositionMoments

## Abstract

Actual normalized Xu--Zhao reciprocal branches have a finite bank contribution that eventually dominates every outer geometric error, for all positive compositions and powers.

**Definition 1.1 (The origin-correct reciprocal branch).**

Lean statement: `D5/S3/AnalyticClosure/Polylogarithm/FiniteSlitCompositionMoments.reciprocal`

*Formalization.* `D5/S3/AnalyticClosure/Polylogarithm/FiniteSlitCompositionMoments.reciprocal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ce Xu and Jianqiang Zhao (2026). *Rational Approximations for Reciprocals of Multiple Zeta Values and Trivariate Cauchy Numbers*. DOI: [10.48550/arXiv.2609.11072](https://doi.org/10.48550/arXiv.2609.11072). URL: <https://arxiv.org/html/2609.11072v1>.

*Commentary.*

For head : PNat, tail : List PNat and ell : PNat, reciprocal is the ell-th power of the inverse of CompositionZeroFreeCollar.normalizedContinuation. At zero it uses CompositionDisk.normalized, preserving the removable source value rather than taking total division in the unnormalized quotient.

**Theorem 1.2 (The literal same-power bank integral).**

Lean statement: `D5/S3/AnalyticClosure/Polylogarithm/FiniteSlitCompositionMoments.result`

*Proof.* Machine-checked in Lean as `D5/S3/AnalyticClosure/Polylogarithm/FiniteSlitCompositionMoments.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ce Xu and Jianqiang Zhao (2026). *Rational Approximations for Reciprocals of Multiple Zeta Values and Trivariate Cauchy Numbers*. DOI: [10.48550/arXiv.2609.11072](https://doi.org/10.48550/arXiv.2609.11072). URL: <https://arxiv.org/html/2609.11072v1>.

*Commentary.*

For every positive head, every finite positive-entry tail, and every positive reciprocal power ell, there are R0>1, 0<rho<1, 1<R<min(R0,1+rho), and an upper bank. The actual reciprocal is analytic on omega intersect norm(z)<R0, agrees with the disk reciprocal on norm(z)<1, and has its correct value at zero. The upper bank is continuous on the closed upper half-collar and agrees there with the reciprocal at every point of omega. At one its value is zeta(head,tail)^(-ell) for head>1 and zero for head=1. There is also a nonnegative constant bounding the norm of the actual reciprocal at every point of omega on the fixed circle of radius R.

For every real B, B/R^n plus (1/pi) times the integral from 1 to R of Im upper(x)/x^(n+1) is strictly negative eventually. CompositionBanks.result is used at this same ell, and CompositionZeroFreeCollar.result supplies the actual zero-free radius. The radius R is 1+min(R0-1,rho)/2. The bank density h(x)=-Im upper(x) is continuous, zero at one and strictly positive inside the interval. FiniteSlitBankMoments.bank_dominance then supplies the strict geometric comparison. For the outer norm bound, separate the circle by a distance delta strictly between R-1 and rho from one. Its far part is a compact subset of omega. On the near part, the upper or lower closed half-collar gives the bound according to the sign of Im z.

The positive compositions use the original largest strict index and depth(tail)=1+length(tail). Every finite leading-one block and every positive ell is included. No global nonvanishing premise is imposed. The Cauchy coefficient identity and shrinking connector limits remain to be established, together with the geometric bound for the actual outer coefficient integral. Taylor coefficients must also be identified with the exact ordinary formal inverse, followed by the all-j finite-prefix and strict admissible lower-bound argument. Consequently this result does not prove eventual coefficient negativity or resolve Xu--Zhao Conjecture 1.3.

## References

- Truth anchor: `D5/S3/AnalyticClosure/Polylogarithm/FiniteSlitCompositionMoments.reciprocal`
- Truth anchor: `D5/S3/AnalyticClosure/Polylogarithm/FiniteSlitCompositionMoments.result`
- Dependency: [D5/S3/AnalyticClosure/Polylogarithm/FiniteSlitBankMoments](FiniteSlitBankMoments.md)
