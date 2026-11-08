# A complete signed Gaussian endpoint

## Abstract

A complete signed Gaussian endpoint

GaussianWindow, CountableResolvent and SpectralAverage are the sole owners of the Gaussian, complete countable spectrum, resolvent and complex average estimate. This module adds the bounded real correction, the closed-window weighted mass and the strict mean-to-point argument. Every supplied spectral occurrence is retained.

For C measurable on the positive half-line with 0<=C(v)<=1, signedQ(v)=-Re(spectralSeries(v))+(C(v)-log(2*pi))*exp(-v). Its W-weighted tail is signedG. The correction average is at most 8*exp(-H)/H. Combining the existing spectral average gives the loose bound 1000*exp(-H)/H, with all integrability proved.

For H>=20000, the Gaussian has at least half its mass in [H,4*(H+20)^2], and the integral of R over that window is at least 1/(8*(H+20)^2). The cubic Taylor term proves the strict scalar gap needed to force a point with signedG(y)/R(y)>-1/(2*sqrt(A)) when A>=10000 and A<=exp(H). This is the new signed endpoint step, not a restatement of old positive-peak mathematics. These are uniform analytic proofs, not certified finite instances or an assertion of literature novelty.

**Theorem 1.1 (A complete signed Gaussian endpoint).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/SignedGaussianEndpoint.full_summed_average_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/SignedGaussianEndpoint.full_summed_average_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The full signed mean bound follows from canonical spectral cancellation plus the bounded correction.

**Theorem 1.2 (A complete signed Gaussian endpoint).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/SignedGaussianEndpoint.signedG_window_integrable`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/SignedGaussianEndpoint.signedG_window_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The signed tail is integrable on the closed Gaussian window; this is consumed by the actual-source instantiation.

**Theorem 1.3 (A complete signed Gaussian endpoint).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/SignedGaussianEndpoint.endpoint_of_complete_representation`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/SignedGaussianEndpoint.endpoint_of_complete_representation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An exact complete representation q(v)=signedQ(v) on v>=H yields a strict signed endpoint at some y in the original closed window.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/SignedGaussianEndpoint.endpoint_of_complete_representation`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/SignedGaussianEndpoint.full_summed_average_bound`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/SignedGaussianEndpoint.signedG_window_integrable`
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/SpectralAverage](SpectralAverage.md)
