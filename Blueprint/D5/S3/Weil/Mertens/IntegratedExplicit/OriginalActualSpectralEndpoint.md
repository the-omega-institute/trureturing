# The genuine spectral endpoint closes the original J identity

## Abstract

The genuine spectral endpoint closes the original J identity

**Theorem 1.1 (Absolute Fourier Fubini).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/OriginalActualSpectralEndpoint.triple_integrable`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/OriginalActualSpectralEndpoint.triple_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complex integrand on frequency times the spatial square is absolutely integrable for each measurable L1 function A. Its norm is exactly weight(w)*norm(A(u))*norm(A(v)), with weight(w)=1/(1+4*w^2). The proof uses the integrable product majorant. Forward and conjugate Fourier factors are L1, so their product expansion uses genuine product integration.

**Theorem 1.2 (The normalized angular resolvent).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/OriginalActualSpectralEndpoint.complex_resolvent_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/OriginalActualSpectralEndpoint.complex_resolvent_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fubini interchanges frequency and the two spatial variables. OriginalAngularResolvent.angular_resolvent supplies the exact normalized inverse transform exp(-abs(s)/2)/4. The Fourier transform and its modulus square remain the literal integral expressions.

**Theorem 1.3 (The L1 correlation resolvent).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/OriginalActualSpectralEndpoint.spectral_correlation_convolution`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/OriginalActualSpectralEndpoint.spectral_correlation_convolution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every measurable integrable complex A and every real t, spectralS(rho A)(t) is one quarter of the full-line integral of exp(-abs(t-s)/2)*Re(integral conj(A(u+s))*A(u) du). The measure-preserving shear (s,u) -> (u,u+s) transports both the unweighted complex coefficient and the weighted real spatial kernel. Complex Fubini supplies integrability of the correlation slices almost everywhere; only on those slices does Re commute with integration. Real Fubini then gives the outer identity. No L2, parity or every-slice integrability premise is imposed.

**Theorem 1.4 (The literal spectral convolution).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/OriginalActualSpectralEndpoint.actual_spectral_square`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/OriginalActualSpectralEndpoint.actual_spectral_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the original finite atoms and every real t, S(t) equals one quarter of the double integral over [0,D]^2 of Re(conj(A(v))*A(u))*exp(-abs(t+u-v)/2). Taking real parts and swapping u,v supplies this sign of the lag. No evenness of rho is assumed.

**Theorem 1.5 (The actual endpoint factorization).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/OriginalActualSpectralEndpoint.actual_spectral_endpoint`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/OriginalActualSpectralEndpoint.actual_spectral_endpoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The closed-window moments are Iplus=integral exp(u/2)*A(u) and Iminus=integral exp(-u/2)*A(u), and Z=Re(conj(Iplus)*Iminus). Since D+u-v>=0 on the square, the endpoint kernel separates and S(D)=exp(-D/2)*Z/4. The hypotheses allow D=0 and an empty atom type.

**Theorem 1.6 (The original test endpoint).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/OriginalActualSpectralEndpoint.original_test_endpoint`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/OriginalActualSpectralEndpoint.original_test_endpoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The test is literally f=c-S for the original prefix and actual Fourier density. The correlation endpoint theorem gives c(D)=0; the actual spectral endpoint therefore gives f(D)=-exp(-D/2)*Z/4. No endpoint hypothesis is supplied by the caller.

**Theorem 1.7 (Absolute continuity of the actual test).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/OriginalActualSpectralEndpoint.original_test_ac`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/OriginalActualSpectralEndpoint.original_test_ac` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual finite-measure proof instantiates the spectralS_ac theorem. Combining it with c_ac proves absolute continuity of f on [0,D], including the zero-length interval.

**Theorem 1.8 (The complete original J identity).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/OriginalActualSpectralEndpoint.actual_fullR_eq_original_J`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/OriginalActualSpectralEndpoint.actual_fullR_eq_original_J` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite atom type, arbitrary complex coefficients with zero total mass, D>=0 and nodes in [0,D], fullR(D,Z,f)=-2*EulerGamma*f(0)-J(D,f,deriv(f)). Absolute continuity supplies the actual a.e. derivative, and original_test_endpoint discharges the endpoint in OriginalSignedJ.fullR_eq_original_J. The independently defined J, the inclusive prime-power cutoff and all degeneracies are retained.

For the actual prefix A, prefix_measurable and the L1 component of prefix_L1_L2 instantiate spectral_correlation_convolution. ActualKernelMomentResolvent.S_global identifies the actual finite-window S_D(t) with this same full-line convolution for every real t. Thus S_D=spectralS(rho A), and actual_spectral_endpoint identifies 4*exp(D/2)*S_D(D) with the original Z=Re(conj(Iplus)*Iminus). No exponential-null or endpoint-S-zero assumption is used. At zero the correlation integral is the prefix energy E, so originalTest(0)=E-W.

Both arithmetic cutoffs are Finset.Icc 2 floor(exp D), and their b functions agree by rearranging the finite sum. Absolute continuity of c and originalTest makes their exponentially weighted functions integrable on the compact interval; subtraction also gives integrability of the weighted S_D. For D>=0 the oriented integral equals the integral over [0,D], including D=0. Expanding f=c-S_D in the original fullR functional gives primeQuadratic-continuum-V, with a minus sign on the entire V. Substitution in actual_fullR_eq_original_J therefore gives signedJExpression=OriginalSignedJ.J(D,originalTest,deriv(originalTest)). These are applications of the existing results, not additional library declarations.

The inclusive endpoint n=exp D is retained: c(D)=0, and its contribution 2*Lambda(n)*S_D(D)/sqrt(n) to V cancels the contribution -Lambda(n)*Z/(2*n) from b(D). This uses Z=4*exp(D/2)*S_D(D), without requiring S_D(D)=0. Empty, repeated and cancelling atom families remain in scope. Applying actual_signed_expression_compensation transports its unchanged D>0, node and moments-through-order(pnt,D) hypotheses to (log(2*pi)-1-EulerGamma)*(E-W)-Re(quadratic(x,a,P))+E <= OriginalSignedJ.J(D,originalTest,deriv(originalTest)). The actual PNT constants and the existing order are unchanged. Global positivity of the original K and the sublinear N(D)=o(D) estimate remain open.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/OriginalActualSpectralEndpoint.actual_fullR_eq_original_J`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/OriginalActualSpectralEndpoint.actual_spectral_endpoint`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/OriginalActualSpectralEndpoint.actual_spectral_square`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/OriginalActualSpectralEndpoint.complex_resolvent_identity`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/OriginalActualSpectralEndpoint.original_test_ac`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/OriginalActualSpectralEndpoint.original_test_endpoint`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/OriginalActualSpectralEndpoint.spectral_correlation_convolution`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/OriginalActualSpectralEndpoint.triple_integrable`
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/OriginalActualFourier](OriginalActualFourier.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/OriginalAngularResolvent](OriginalAngularResolvent.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/OriginalSignedJ](OriginalSignedJ.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/OriginalTestRegularity](OriginalTestRegularity.md)
