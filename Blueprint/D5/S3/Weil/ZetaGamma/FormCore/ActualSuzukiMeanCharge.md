# The original actual Suzuki mean

## Abstract

The original actual Suzuki mean

Here mu(F) is the integral over the full real line of actualSuzukiEvenBProfile(F), exactly the original H6 mean constraint. It is distinct from the positive-half-line Gaussian central Mellin charge used by the weighted coefficient core. These are source-relative analytic consequences of the existing original physical domain and complete-theta constructions, with no RH-resolution or literature-priority claim.

An application of the existing exponential-moment, translation, H6 theta-summability and dominated-convergence results gives a concrete source with nonzero original mean. For every real p>=2, E_p(x)=exp(-p x) is original H6, mu(E_p) has zero imaginary part and its real part is strictly positive.

To see the sign, put U=fullTheta(E_p), M0=integral_(x>pi) Re(U(x)) and M5=integral_(x>pi) x^(5/4) Re(U(x)). Every physical mode is n^4 exp(-p n^2 x), n>=1. H6 supplies the actual L1 domains and almost-everywhere summability, so dominated convergence exchanges the complete positive mode series with its zeroth and second moment integrals. The first mode makes M0>0. The rate q=p n^2 is at least 2, and the exact exponential moments give M2<=(pi^2+pi+1/2) M0. Since x^(5/4)<=x^2 for x>pi, M5<=M2. The original mean formula then gives Re(mu(E_p))=(6 pi^(5/4) M0-M5)/5>0, because pi^2+pi+1/2<6 pi^(5/4). All these moments are genuine integrals of the same complete theta source.

The positive original mean provides a nonzero direction for source corrections. Original Gamma Fourier form-domain membership for this exponential source and density of a corrected Gaussian core remain separate obligations. The H6 conditions of the source-linearity interface below must still be paid when forming a correction.

The reflected Gaussian source also satisfies the original mean constraint. For every real a, put g_a(x)=exp(9a/2-exp(2a)x) and F_a=g_a+g_-a-2g_0. These are actual original H6 sources, and mu(F_a)=0. The conclusion survives arbitrary complex scalar multiplication, so it includes the normalization by 1/(2 gaussianSiteAmplitude(a)) used by the existing physical-synthesis representative. It does not identify the original mean with the central Mellin charge on general sources.

For the exact application, let D(p)=thetaSeries(2,p), S4(p)=thetaSeries(4,p), T(p)=integral_(t>p) t^(5/4) S4(t), and G(p)=(6/5) pi^(5/4) p^(5/4) D(p)-(1/5) pi^(9/4) T(p), for p>0. Original H6 supplies the genuine physical-moment domains. Dominated convergence gives the complete-theta zeroth moment D(p)/p, and positive physical scaling gives the weighted tail T(p), hence mu(g_a)=G(exp(2a)). The existing theta-series derivative, local FTC for the difference of two integrable tails, and omega_eq_series give d/da G(exp(2a))=-(pi^(1/4)/2) romikPhi(a). The existing evenness of romikPhi makes G(exp(2a))+G(exp(-2a)) constant, with value 2G(1). Source linearity then gives mu(F_a)=0, including negative a. No derivative exchange with an improper integral is assumed.

The same atom is exactly the physical source map in Library/Weil/suzuki2026screw.md, W255. On that account's finite-source mixed-form interface, oddness of the complete kernel L0 in either site makes delta_a+delta_-a-2 delta_0 pair to zero with every finite source. W360 gives the equivalent zero-sum interpretation v_-a(gamma)=-v_a(gamma), with v_0(gamma)=0 at every zero. Thus that source account places the reflected family in the radical of the complete form on this interface. Its cap475 lower bound controls physical moments of a null family; it does not establish positivity on the remaining source sector. This complete-form interpretation uses the cited paper-level interfaces; the exact Lean application here checks original H6 and mu. Original Gamma form-domain membership and density in the full original domain are not inferred.

There is also a physical-source kernel formula on the entire original H6 space. For y>pi define Kphys(y)=sum_(n>=1, pi*n^2<y) (6*pi^(5/4)*n^2-y^(5/4)/sqrt(n)). Each y has only finitely many active modes. For every originalPhysicalH6 source F, Kphys*F is genuinely integrable on y>pi and 5*mu(F)=integral_(y>pi) Kphys(y)*F(y). This physical-source kernel differs from the bounded profile kernel K(t) below.

For the exact application, original H6 gives the weighted L1 domains of F and of the complete theta source. Positive physical scaling rewrites each moment integral as an integral over y>pi*n^2. Apply the same weighted physical-mode interchange to the original H6 source norm(F). Its nonnegative real mode integrals are exactly the integrals of the norms of the source-tail modes. This proves summability of the source-tail L1 mode series before interchange. Dominated convergence and uniqueness of the integral series then give the displayed formula for the literal physical source, rather than assuming its convergence or its integral representation.

The finite kernel is strictly positive at every y>pi. Put r=sqrt(y/pi) and N=ceil(r)-1; the strict active modes are exactly n=1,...,N, including when y/pi is an integer square. After division by pi^(5/4), the sign reduces to 6*sum_(n=1)^N n^2-r^2*sqrt(r)*sum_(n=1)^N 1/sqrt(n)>0 for N>=1 and 0<=r<=N+1. The exact application uses Mathlib's antitone sum-integral bound for the reciprocal-square-root sum and its Bernoulli/Faulhaber square-sum formula. It pays the finite inequality and square-shell endpoints; no sign hypothesis on Kphys is supplied.

Consequently, if F is original H6, Re(F)>=0 almost everywhere on y>pi, and integral_(y>pi) Re(F)>0, then Re(mu(F))>0. The imaginary part of F has no additional restriction. This follows from the same integrable physical-kernel formula and strict positivity of Kphys; positive real source mass cannot have zero weighted integral. These are checked applications of the existing analytic and finite-sum results, not new mathematical declarations or a claim of complete Weil-form positivity. In particular they do not establish original Gamma form-domain membership, density, or RH.

**Theorem 1.1 (The actual original mean has a bounded kernel).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiMeanCharge.actual_h6_suzuki_mean_charge_formula`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiMeanCharge.actual_h6_suzuki_mean_charge_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original H6 source F, the full-line even-B profile is genuinely integrable. Its original mean mu(F) equals the positive-half-line integral of K(t) actualGammaProfile(F,t), with K(t)=(6 exp(-5t/4)-1)/5. The even doubling formula, genuine L1 tail mass and Bochner integral algebra retain the endpoint contribution.

**Theorem 1.2 (The original mean has an L1 bound).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiMeanCharge.actual_h6_suzuki_mean_charge_norm_le`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiMeanCharge.actual_h6_suzuki_mean_charge_norm_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The kernel lies between -1/5 and 1 on the positive half-line. Consequently the norm of the original mean is at most the L1 norm of the same actual complete-theta profile; no coefficient-charge reinterpretation enters.

**Theorem 1.3 (A real actual profile gives a real original mean).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiMeanCharge.actual_h6_suzuki_mean_charge_im_eq_zero_of_profile_ae`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiMeanCharge.actual_h6_suzuki_mean_charge_im_eq_zero_of_profile_ae` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An almost-everywhere real actual complete-theta profile gives a real original mean. The original H6 hypothesis supplies the true integral domain; this theorem does not assume pointwise real behavior at the boundary.

**Theorem 1.4 (The original mean respects actual profile relations).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiMeanCharge.actual_h6_suzuki_mean_charge_linear_of_profile_ae`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiMeanCharge.actual_h6_suzuki_mean_charge_linear_of_profile_ae` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For three original H6 sources whose actual complete-theta profiles satisfy the stated almost-everywhere complex linear relation, the original means satisfy that relation. This conditional interface retains its profile hypothesis.

**Theorem 1.5 (The original mean is linear on actual H6 source combinations).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiMeanCharge.actual_h6_suzuki_mean_charge_linear`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiMeanCharge.actual_h6_suzuki_mean_charge_linear` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary complex a,b and original H6 sources F,G such that H(x)=a F(x)+b G(x) is also original H6, mu(H)=a mu(F)+b mu(G). There is no additional assumption about the profiles. The proof uses the existing almost-everywhere summability of the literal physical-mode series, derives actual fullTheta linearity, and transports it through the genuine physical moments of orders 0 and 5/4. It then reconstructs the original full-line even-B mean from those moments. No stronger endpoint convergence or Gamma Fourier form-domain is inferred.

## References

- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiMeanCharge.actual_h6_suzuki_mean_charge_formula`
- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiMeanCharge.actual_h6_suzuki_mean_charge_im_eq_zero_of_profile_ae`
- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiMeanCharge.actual_h6_suzuki_mean_charge_linear`
- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiMeanCharge.actual_h6_suzuki_mean_charge_linear_of_profile_ae`
- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiMeanCharge.actual_h6_suzuki_mean_charge_norm_le`
- Dependency: [D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiMeanZeroTrace](ActualSuzukiMeanZeroTrace.md)
