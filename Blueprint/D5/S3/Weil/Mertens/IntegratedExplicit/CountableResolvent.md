# Countable W-weighted spectral resolvents

## Abstract

A dominated complete-series exchange through the positive W-weighted Laplace resolvent.

CountableSpectrum carries zero and coefficient sequences indexed by all natural numbers. Each zero satisfies 0<Re(z)<1 and abs(Im(z))>10. The coefficient norms are summable and their total is at most 2. No beta cap below 1, symmetry quotient, finite truncation, integral budget or signed-tail hypothesis is included.

The literal spectral tail is the integral over v>y of W(v) times the complete sum of c_k*exp((z_k-1)*v), where W(v)=(v+2)/v^3. The resolvent denominator is s+1-z, its numerator is s*(1+s), and each mode integrates the resolvent kernel over s>0. A private R(v)=(v+1)/v^2 supplies integrability of W through its derivative and its limit at infinity.

**Theorem 1.1 (The complete countable resolvent identity).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/CountableResolvent.countable_resolvent_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/CountableResolvent.countable_resolvent_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive y, spectralTail(S,y) equals the complete sum of c_k*resolventMode(z_k,y). The common positive s,v kernel is proved product integrable before Fubini. Per-mode integration then gives the literal resolvent, and dominated convergence with bound norm(c_k)*W(v) exchanges the whole series with the weighted tail. SpectralAverage.spectral_average_bound uses the identity to obtain its pointwise HasSum; the identity is on the active average proof path.

**Lemma 1.2 (Integrable positive Laplace weight).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/CountableResolvent.laplace_weight_integrable`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/CountableResolvent.laplace_weight_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every y>0, s*(1+s)*exp(-s*y) is integrable on s>0. The proof directly reuses TwoScaleEndpointMoments.exponential_moment at rate y for n=1,2. Its integrability and equality components supply the private real moments and exact W moment. SpectralAverage.window_kernel_integrable and high_tail_integrable require this fact.

**Lemma 1.3 (Nonnegative Laplace polynomial).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/CountableResolvent.laplacePolynomial_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/CountableResolvent.laplacePolynomial_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The polynomial s*(1+s) is nonnegative for s>=0. This consumed algebraic helper is used by the product majorants and the low and high frequency bounds in SpectralAverage.

**Lemma 1.4 (The W weight decreases on the positive axis).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/CountableResolvent.W_antitone`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/CountableResolvent.W_antitone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 0<x<=y, W(y)<=W(x). Its reciprocal-power proof supplies the uniform window majorant in spectral_average_bound.

**Lemma 1.5 (Ordinate separation controls every denominator).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/CountableResolvent.denominator_norm`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/CountableResolvent.denominator_norm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If abs(Im(z))>=10 then norm(s+1-z)>=10 for every real s. The low-frequency averaged kernel uses the imaginary-part bound without an inverse distance to Re(z)=1.

**Lemma 1.6 (Nonvanishing denominator).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/CountableResolvent.denominator_ne`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/CountableResolvent.denominator_ne` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same height condition makes s+1-z nonzero for every real s. SpectralAverage.window_kernel_integrable uses this fact in the continuity proof for the product kernel.

**Lemma 1.7 (The pointwise positive resolvent majorant).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/CountableResolvent.resolventKernel_norm_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/CountableResolvent.resolventKernel_norm_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For Re(z)<=1, abs(Im(z))>=10, s>=0 and y>=0, the kernel norm is at most s*(1+s)*exp(-s*y)/10. SpectralAverage uses it to prove window product integrability and window_kernel_bound.

**Lemma 1.8 (Uniform modulus of a complete mode).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/CountableResolvent.resolventMode_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/CountableResolvent.resolventMode_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For y>0 under the same strip and height bounds, the full mode norm is at most W(y)/10. Together with W_antitone it gives the coefficient-summable window majorant used in spectral_average_bound.

**Lemma 1.9 (Mode continuity on a positive half-axis).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/CountableResolvent.resolventMode_continuousOn`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/CountableResolvent.resolventMode_continuousOn` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For Re(z)<1 and H>0, the mode is continuous on [H,infinity). The proof identifies it with the integrable W-weighted tail primitive. spectral_average_bound uses it for the actual measurability hypothesis of countable dominated convergence.

The existing CompleteCoefficientLaplace.complete_coefficient_laplace concerns the R-weight (1+x)/x^2 and numerator (1+t), so it is not the W-weight identity here. The generic real-moment supplier TwoScaleEndpointMoments.exponential_moment is reused instead of reproved; importing the instance-level LiCausalTrichotomy would violate this generic module’s import layer. ActualZeroLaplace and TrivialZeroLaplace provide actual occurrence and correction facts for a later application; this generic unit imports neither. The arithmetic relation to Q(exp(v)) and the original Robin5040 endpoint remain separate obligations.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/CountableResolvent.W_antitone`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/CountableResolvent.countable_resolvent_identity`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/CountableResolvent.denominator_ne`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/CountableResolvent.denominator_norm`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/CountableResolvent.laplacePolynomial_nonneg`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/CountableResolvent.laplace_weight_integrable`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/CountableResolvent.resolventKernel_norm_bound`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/CountableResolvent.resolventMode_bound`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/CountableResolvent.resolventMode_continuousOn`
- Dependency: [D5/S3/Analytic/ExponentialSum/TwoScaleEndpointMoments](../../../Analytic/ExponentialSum/TwoScaleEndpointMoments.md)
