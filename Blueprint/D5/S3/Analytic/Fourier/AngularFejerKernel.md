# Angular Fejer kernels

## Abstract

Angular Fejer kernels, their Fourier transforms, tail bounds, and logarithmic averages.

**Theorem 1.1 (Convolution with a cosine).**

Lean statement: `D5/S3/Analytic/Fourier/AngularFejerKernel.cosine_convolution`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/AngularFejerKernel.cosine_convolution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If g is integrable and its angular Fourier transform is the real-valued function w, then convolution of g with cos(gamma u) equals w(gamma) cos(gamma y). Translation of the complex exponential integral gives the identity after taking real parts.

**Theorem 1.2 (Continuity of the tent weight).**

Lean statement: `D5/S3/Analytic/Fourier/AngularFejerKernel.phi_continuous`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/AngularFejerKernel.phi_continuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Fejer tent Fourier weight is continuous for every real bandwidth.

**Theorem 1.3 (Vanishing outside the bandwidth).**

Lean statement: `D5/S3/Analytic/Fourier/AngularFejerKernel.phi_eq_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/AngularFejerKernel.phi_eq_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive b, the Fejer tent weight vanishes at every t with absolute value at least b.

**Theorem 1.4 (The height of the Fejer kernel).**

Lean statement: `D5/S3/Analytic/Fourier/AngularFejerKernel.K_cap`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/AngularFejerKernel.K_cap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive b, K(b,v) is at most b/(2*pi) at every real v.

**Theorem 1.5 (Continuity of the Fejer kernel).**

Lean statement: `D5/S3/Analytic/Fourier/AngularFejerKernel.K_continuous`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/AngularFejerKernel.K_continuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The angular Fejer kernel is continuous for every real bandwidth.

**Theorem 1.6 (Continuity of the notched kernel).**

Lean statement: `D5/S3/Analytic/Fourier/AngularFejerKernel.H_continuous`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/AngularFejerKernel.H_continuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The notched Fejer kernel is continuous for every real bandwidth and notch location.

**Theorem 1.7 (Angular and cyclic Fourier conventions).**

Lean statement: `D5/S3/Analytic/Fourier/AngularFejerKernel.aft_fourier`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/AngularFejerKernel.aft_fourier` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The angular Fourier transform at t equals the cyclic Fourier transform at t/(2*pi).

**Theorem 1.8 (Nonnegativity of the logarithmic envelope).**

Lean statement: `D5/S3/Analytic/Fourier/AngularFejerKernel.log_ell_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/AngularFejerKernel.log_ell_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nonnegative u, log(exp(1)+u) is nonnegative.

**Theorem 1.9 (The angular Fejer kernel).**

Lean statement: `D5/S3/Analytic/Fourier/AngularFejerKernel.fejer_law`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/AngularFejerKernel.fejer_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive bandwidth b, the angular Fejer kernel K(b,v) is nonnegative and integrable with total mass one. Its angular Fourier transform is the triangular function max(0,1-abs(t)/b). For every positive y, its integral over v at least y is at most 2/(pi*b*y).

**Theorem 1.10 (The notched Fejer kernel).**

Lean statement: `D5/S3/Analytic/Fourier/AngularFejerKernel.notched_fejer_law`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/AngularFejerKernel.notched_fejer_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive b and U greater than 2*b, the notched kernel H(b,U,v)=K(b,v)*(1-cos(U*v)) lies between zero and 2*K(b,v), is integrable, and has total mass one. Its angular Fourier transform is phi(b,t)-phi(b,t-U)/2-phi(b,t+U)/2. Its integral over v at least a positive y is at most 4/(pi*b*y).

**Theorem 1.11 (Uniform logarithmic averages).**

Lean statement: `D5/S3/Analytic/Fourier/AngularFejerKernel.fejer_log_average`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/AngularFejerKernel.fejer_log_average` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There is a nonnegative constant C independent of M and y such that, for M and y at least one, K(M,y-u)*log(exp(1)+u) is integrable on the nonnegative half-line and its integral is at most log(exp(1)+y)+C. The bound follows from the finite logarithmic moment of K(1,.) and dilation of the kernel.

**Theorem 1.12 (Logarithmic averages for notched kernels).**

Lean statement: `D5/S3/Analytic/Fourier/AngularFejerKernel.notched_log_average`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/AngularFejerKernel.notched_log_average` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each positive b, there is a nonnegative constant depending only on b such that, whenever U is greater than 2*b and y is at least one, H(b,U,y-u)*log(exp(1)+u) is integrable on the nonnegative half-line and its integral is at most log(exp(1)+y) plus that constant. Positivity and unit mass give coefficient one for the logarithm; comparison with 2*K(b,.) bounds the remaining logarithmic moment uniformly in U.

## References

- Truth anchor: `D5/S3/Analytic/Fourier/AngularFejerKernel.H_continuous`
- Truth anchor: `D5/S3/Analytic/Fourier/AngularFejerKernel.K_cap`
- Truth anchor: `D5/S3/Analytic/Fourier/AngularFejerKernel.K_continuous`
- Truth anchor: `D5/S3/Analytic/Fourier/AngularFejerKernel.aft_fourier`
- Truth anchor: `D5/S3/Analytic/Fourier/AngularFejerKernel.cosine_convolution`
- Truth anchor: `D5/S3/Analytic/Fourier/AngularFejerKernel.fejer_law`
- Truth anchor: `D5/S3/Analytic/Fourier/AngularFejerKernel.fejer_log_average`
- Truth anchor: `D5/S3/Analytic/Fourier/AngularFejerKernel.log_ell_nonneg`
- Truth anchor: `D5/S3/Analytic/Fourier/AngularFejerKernel.notched_fejer_law`
- Truth anchor: `D5/S3/Analytic/Fourier/AngularFejerKernel.notched_log_average`
- Truth anchor: `D5/S3/Analytic/Fourier/AngularFejerKernel.phi_continuous`
- Truth anchor: `D5/S3/Analytic/Fourier/AngularFejerKernel.phi_eq_zero`
- Dependency: [D5/S3/TotalVariation/Asymptotics/StatLeanFourierCore](../../TotalVariation/Asymptotics/StatLeanFourierCore.md)
