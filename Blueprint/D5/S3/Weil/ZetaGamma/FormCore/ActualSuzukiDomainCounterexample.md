# Sharp Sixth-Moment Threshold for Simultaneous Gamma-Domain Escape

## Abstract

Exactly K>1 admits one real original physical H6 source with positive physical mass, strict sixth-moment ratio below K, and simultaneous escape from every Gamma form domain whose constant-shifted weight is at least one. The same source retains full theta, actual profile L1 and L2, and all exponential position moments.

**Definition 1.1 (Original physical sixth-moment domain).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiDomainCounterexample.originalPhysicalH6`

*Formalization.* `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiDomainCounterexample.originalPhysicalH6` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The original half-line is x>pi. The predicate requires physical MemLp 2 and genuine integrability of (x/pi)^6 times norm(F(x))^2 on that half-line. It is not a coefficient-space condition.

**Definition 1.2 (Complete physical theta transform).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiDomainCounterexample.fullTheta`

*Formalization.* `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiDomainCounterexample.fullTheta` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The sum includes every integer n>=1 with term n^4 F(n^2 x), using n=k+1. For the constructed source every n>=2 term is proved zero on x>=pi by exact support, and a full HasSum proof gives TF=F. No theta cutoff is imposed as a definition or premise.

**Definition 1.3 (Actual zero-extended theta profile).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiDomainCounterexample.actualGammaProfile`

*Formalization.* `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiDomainCounterexample.actualGammaProfile` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For t>=0 the profile is (pi exp(t))^(9/4) times TF(pi exp(t)); for t<0 it is zero. There is no B operator. The same actual profile is identified pointwise with a time compression of the centered tent times the real lacunary cosine series used in the Fourier proof: u(t)=counterProfile(t/kappa).

**Definition 1.4 (Literal reference Gamma weight).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiDomainCounterexample.gammaWeight`

*Formalization.* `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiDomainCounterexample.gammaWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Write p0(xi)=gammaWeight(xi). Its literal value is (2/sqrt(pi))*((xi^2+1/16)/(xi^2+25/16)) *(Re digamma(1/4+i*xi)-log(pi))+1+4*sqrt(pi). The construction proves p0(xi)>1 and max(log(abs(xi)),0)<=C0*p0(xi) with a fixed finite nonnegative C0. Thus the relative shift c=0 is admissible.

**Definition 1.5 (Literal constant-shifted Gamma form domain).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiDomainCounterexample.originalGammaFormDomain`

*Formalization.* `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiDomainCounterexample.originalGammaFormDomain` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a real relative shift c and source F, originalGammaFormDomain(c,F) means genuine integrability of (p0(xi)+c) times the squared norm of the actual profile's unitary positive angular Fourier transform. The theorem calls c admissible precisely when p0(xi)+c>=1 for every xi. This permits negative c whenever the same bound holds.

For every admissible c, p0<=p0+c+abs(c) <=(1+abs(c))*(p0+c). Consequently max(log(abs(xi)),0) <=C0*(1+abs(c))*(p0(xi)+c). Finiteness of the shifted Gamma density alone would imply finiteness of the nonnegative positive-log density. This uses the literal weight; no identification with a separate formal V structure is asserted.

**Theorem 1.6 (The exact cap range is K>1).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiDomainCounterexample.actual_h6_gamma_domain_escape_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiDomainCounterexample.actual_h6_gamma_domain_escape_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real K, the following complete source existence statement is equivalent to 1<K. The real original physical H6 source F has H=integral over x>pi of norm(F(x))^2 strictly positive and M=integral over x>pi of (x/pi)^6*norm(F(x))^2 strictly below K*H. No normalization H=1 is asserted.

The same witness has complete theta HasSum equal to F(x) for every x>=pi. Its actual profile belongs to L1 and L2, has every real exponential position moment finite, has strictly positive squared mass, and has a finite strictly positive first position moment. Its actual extended positive-log Fourier integral equals infinity. This one F fails originalGammaFormDomain(c,F) simultaneously for every real c whose shifted weight is at least one everywhere. The witness F is chosen before c and does not vary with the shift.

For K>1, compress the explicit centered-tent lacunary cosine profile into a sufficiently short positive logarithmic window. The physical source remains x^(-9/4) times the compressed profile at log(x/pi) for x>=pi, zero otherwise. The physical support directly bounds the literal sixth moment by a factor strictly smaller than K times H. The Fourier scaling argument retains log-plus divergence.

Conversely, the pointwise weight (x/pi)^6 is at least one on x>pi. Genuine integrability gives H<=M. Together with H>0 and M<K*H this forces 1<K, excluding every K<=1 including the boundary. No extra positivity assumption on K is used.

The uncompressed seed Fourier transform has common phase exp(i*xi/2). Both cosine channels remain in the nonnegative amplitude, each using the concrete tent transform sinc(xi/8)^2/(4*sqrt(2*pi)). An integrable coefficient-times-tent majorant justifies the infinite series interchange.

For the seed, the bands of radius one around exp(4^(n+1)) are pairwise disjoint. On every band the positive-log Fourier density is at least 1/(4096*pi); each band has measure two. The genuinely extended nonnegative integral is therefore infinite. Fourier compression preserves this divergence, and each admissible shifted Gamma comparison transfers it to nonintegrability on the same compressed actual source.

This theorem is an infinite analytic source-domain obstruction. It asserts neither a negative complete Weil energy nor RH or a Robin conclusion. The conclusion concerns the literal simultaneous Gamma-domain obstruction on the original physical source.

**Theorem 1.7 (Continuity of the actual reference Gamma weight).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiDomainCounterexample.finiteGammaWeight_continuous`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiDomainCounterexample.finiteGammaWeight_continuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The literal gammaWeight is continuous on the real frequency line. The proof rewrites its density through the existing smooth mu function and uses the nonsingular rational factor.

**Theorem 1.8 (A global quadratic upper bound for the actual Gamma weight).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiDomainCounterexample.finiteGammaWeight_quadratic_upper`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiDomainCounterexample.finiteGammaWeight_quadratic_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There is a real G>0 such that gammaWeight(xi)<=G*(1+xi^2) for every real xi. The proof consumes the existing digamma strip estimate and the actual rational factor bounds. The finite cosine construction consumes this estimate with its proved Fourier decay to obtain a genuinely integrable Cauchy-kernel majorant; the growth bound alone asserts no energy finiteness for arbitrary H6 sources.

## References

- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiDomainCounterexample.actualGammaProfile`
- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiDomainCounterexample.actual_h6_gamma_domain_escape_iff`
- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiDomainCounterexample.finiteGammaWeight_continuous`
- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiDomainCounterexample.finiteGammaWeight_quadratic_upper`
- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiDomainCounterexample.fullTheta`
- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiDomainCounterexample.gammaWeight`
- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiDomainCounterexample.originalGammaFormDomain`
- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiDomainCounterexample.originalPhysicalH6`
- Dependency: [D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiLacunaryProfile](ActualSuzukiLacunaryProfile.md)
