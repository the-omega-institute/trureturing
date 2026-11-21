# The log-density estimate and the two-cutoff error bound

## Abstract

Square and cube corrections to the prime-only tail under RH

Write Qtheta for the prime-only tail, D for squareDensity, A(x) for squarePrimitive, and W(a,B) for the integral of rootWindowDensity over [log(a),log(B)]. The square-cutoff coefficients and occurrence indexing are those of SquareSpectrum.

**Theorem 1.1 (The normalized square and cube terms).**

$$RH \Rightarrow \left(\exists K \in \mathbb{R},\; 0 < K \land \left(\forall x \in \mathbb{R},\; 8 \le x \Rightarrow \left|\operatorname{sqrt}\left(x\right) \cdot \left(\operatorname{Q}\left(x\right) - \operatorname{Qtheta}\left(x\right)\right) - 2 - \frac{3}{2} \cdot x^{-\frac{1}{6}} - \operatorname{D}\left(\operatorname{log}\left(x\right)\right)\right| \le K \cdot x^{-\frac{3}{10}}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/RHRootCorrection.rh_prime_power_density` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tianyu Zhao (2025). *On the mean values of the error terms in Mertens' theorems*. DOI: [10.1007/s40993-025-00640-y](https://doi.org/10.1007/s40993-025-00640-y). URL: <https://arxiv.org/abs/2411.18903v2>.

*Commentary.*

Zhao's equation (14) uses the same prime-only tail. The integrated complete formula bounds the difference between Q and its signed zero contribution by a constant times x^(-1). The centered square transform therefore has error of order x^(-1/2). The normalized cube error has order x^(-1/3) because Q(y) is of order y^(-1/2) at y=x^(1/3). The leading uncentered root terms are 2 and (3/2)x^(-1/6). The fifth-root majorant gives the final x^(-3/10) envelope.

**Definition 1.2 (The root correction with the complete-tail residual).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/RHRootCorrection.rootWindowDensity`

*Formalization.* `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/RHRootCorrection.rootWindowDensity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At x=exp(u), add the complete normalized tail residual to the square-root-scaled prime-power bias after subtracting its constant main term 2.

**Theorem 1.3 (The cube primitive and the shrinking endpoint error).**

$$RH \Rightarrow \left(\exists T \in \mathbb{R},\; \exists K \in \mathbb{R},\; 8 \le T \land \left(0 < K \land \left(\left(\forall x \in \mathbb{R},\; T \le x \Rightarrow 0 < \operatorname{sqrt}\left(x\right) \cdot \left(-\operatorname{Qtheta}\left(x\right)\right)\right) \land \left(\forall a \in \mathbb{R},\; \forall B \in \mathbb{R},\; T \le a \Rightarrow \left(a \le B \Rightarrow \left|\operatorname{W}\left(a, B\right) - 9 \cdot \left(a^{-\frac{1}{6}} - B^{-\frac{1}{6}}\right) - \operatorname{A}\left(B\right) + \operatorname{A}\left(a\right)\right| \le K \cdot \left(a^{-\frac{3}{10}} - B^{-\frac{3}{10}}\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/RHRootCorrection.rh_root_correction_window` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The prime-power bias tends to 2 in the square-root scaling. Under RH the normalized complete tail is eventually bounded in absolute value by firstLiMass plus 1/2, which is strictly below 3/2. These bounds give a strictly positive prime-only density on the whole late half-axis.

Integrate the cube term over [log(a),log(B)] to obtain 9(a^(-1/6)-B^(-1/6)). Use the same endpoints for the square primitive and integrate the residual majorant on that interval to retain a^(-3/10)-B^(-3/10). Equal endpoints are included. The statement uses the full actual zero occurrences and requires no independence of ordinates.

**Theorem 1.4 (The actual prime-only window with both zero primitives).**

$$RH \Rightarrow \left(\exists T \in \mathbb{R},\; \exists K \in \mathbb{R},\; 2 \le T \land \left(0 < K \land \left(\forall a \in \mathbb{R},\; \forall B \in \mathbb{R},\; T \le a \Rightarrow \left(a \le B \Rightarrow \left|\operatorname{N}\left(a, B\right) - 2 \cdot \operatorname{log}\left(\frac{B}{a}\right) - \operatorname{p}\left(\operatorname{log}\left(B\right)\right) + \operatorname{p}\left(\operatorname{log}\left(a\right)\right) - 9 \cdot \left(a^{-\frac{1}{6}} - B^{-\frac{1}{6}}\right) - \operatorname{A}\left(B\right) + \operatorname{A}\left(a\right)\right| \le K \cdot \left(a^{-\frac{3}{10}} - B^{-\frac{3}{10}}\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/RHRootCorrection.prime_window_cube_and_square_of_rh` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tianyu Zhao (2025). *On the mean values of the error terms in Mertens' theorems*. DOI: [10.1007/s40993-025-00640-y](https://doi.org/10.1007/s40993-025-00640-y). URL: <https://arxiv.org/abs/2411.18903v2>.

*Commentary.*

Let N(a,B) be the integral of max(-Qtheta(x),0)/sqrt(x) from a to B. Let p(u) be the real part of the sum of exp(i Im(rho) u)/[rho(1-rho)i Im(rho)] over the actual nontrivial zero occurrences with multiplicity.

The exact ordinary endpoint identity of RHPrimeWindowRemainder expresses the discrepancy after subtraction of the logarithm and the first primitive as an integral of windowError. Eventual positivity identifies windowError with rootWindowDensity on the same closed log window. Apply the integrated estimate with cube coefficient 9 and the square primitive A at both endpoints.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/RHRootCorrection.prime_window_cube_and_square_of_rh`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/RHRootCorrection.rh_prime_power_density`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/RHRootCorrection.rh_root_correction_window`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/RHRootCorrection.rootWindowDensity`
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/RootTail](RootTail.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SquareSpectrum](SquareSpectrum.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/RHPrimeWindowRemainder](../RHPrimeWindowRemainder.md)
- Dependency: [D5/S3/Weil/Mertens/ZeroAbscissaPower](../../ZeroAbscissaPower.md)
