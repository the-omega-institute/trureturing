# Actual source Jensen fixed window

## Abstract

The normalized all-mode theta source has a fixed-window actual-node target and an original-disk occurrence target.

**Theorem 1.1 (Fixed windows and arbitrary-order isolating disks).**

$$\begin{aligned}0<Z, 0<\frac{2}{Z}, F=\frac{2}{Z}f\\\forall T>0, \exists nzero, \forall n\ge nzero, n\ge 1\land \forall t,\\0<t\le T \land \operatorname{originalJ}\left(n, t\right)=0\implies DG\ge \frac{D^2}{2}>0 \land \operatorname{NodeResponse}\left(n, t\right)\\\forall tzero>0, \operatorname{F}\left(tzero\right)=0, \forall m\ge 1,\\\forall delta, \operatorname{IsExactRealOrder}\left(F, tzero, m\right) \land \operatorname{IsolatingDisk}\left(F, tzero, delta\right)\implies \operatorname{LocalConclusion}\left(tzero, delta, m\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Jensen/ActualSourceJensenFixedWindow.actual_source_jensen_fixed_window` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Dan Romik (2021). *Orthogonal polynomial expansions for the Riemann xi function in the Hermite, Meixner–Pollaczek, and continuous Hahn bases*. URL: <https://doi.org/10.4064/aa200515-10-3>.

*Acknowledgement.* NIST Digital Library of Mathematical Functions (2026). *DLMF Section 18.2, General Orthogonal Polynomials*. URL: <https://dlmf.nist.gov/18.2>.

*Commentary.*

Let F be the cosine-square transform of the normalized full theta density, and let f be half the transform of the raw full kernel. Then Z=fullZ>0, 2/Z>0 and F=(2/Z)f at every complex argument. The polynomial p_n is sourceP(n) at the negative argument, complexified. On the real line p_n(t)=originalJ(n,t), and D=fullD(n,t)=-sourceP(n)'(-t).

For every T>0 there is n0 such that every n>=n0 satisfies n>=1, and for every t with 0<t<=T AND originalJ(n,t)=0, D*G>=D^2/2>0. All actual nodes are included; the threshold may depend on T.

At such a node D and G are nonzero and (2n+1)G=2nD-M/2, where M=fullM2(n,t). At ell*t, ell=(n+1)/n, originalJ(n+1) has derivative G with respect to its real argument and value (t/n)*G, which is nonzero. sourceQ(n) has a simple zero at 1/t and a nonzero simple cofactor.

For xi=n/(n+1)/t and q=sourceQ(n+1), xi>0, q'(xi)=0, (n+1)q(xi)=xi^n*G and xi^2*q''(xi)=-n*xi^n*D. Their product is -(n/(n+1))*xi^(2n-2)*D*G. Both q(xi) and q''(xi) are nonzero. The guarded coupling satisfies coupling*D^2=(xi^2/n)*D*G>0.

For every positive zero t0 of F, every exact finite order m>=1 and every original isolating radius delta>0, there are C,d>0 and N such that every n>=N satisfies n>=1 and has injectively indexed positive real nodes nodes:Fin(m)->Real. Each node is an actual originalJ(n) zero and a simple p_n zero strictly inside the original delta disk; |nodes(i)-t0|<=C/sqrt(n), |D(n,nodes(i))|>=d/(sqrt(n))^(m-1), and |M(n,nodes(i))|<=n*|D(n,nodes(i))| for EVERY index.

The original boundary has no polynomial zero. The filtered polynomial root multiset equals the multiset map of all Fin(m) indices under nodes, has cardinality m, and has count one at every nodes(i). Each simple cofactor is nonzero. Every signed, adjacent and reflected consequence is evaluated at nodes(i) for the same n.

The normalized coefficients are a(j)=(-1)^j*mu(j)/(2j)!, where mu(j) is the full theta moment. The coefficients of H=-4z*F''-2F' are (-1)^j*mu(j+1)/(2j)!. Integrating the actual finite polynomial term by term proves that its coefficient polynomial is exactly fullM2, with the same fullZ normalization as F.

The affine polynomial P(n)(t0*(1+u/sqrt(n))) is divided by its actual nonzero real leading Taylor normalizer. Uniform complex convergence to the monic Hermite polynomial gives all m real simple nodes and one derivative margin. For m>=2, H has exact order m-2, and its own scaled estimate bounds fullM2. At m=2 this is order zero. For m=1 a uniform coefficient norm bounds fullM2 directly, without an order or nonvanishing premise on H.

Local Taylor uses sigma=min(delta/2,t0/2,1), while the boundary comparison uses the positive minimum of |F| on the caller's original delta sphere. F(0)=1 rules out every locally zero analytic branch. Its complete real zero set in [0,T] is finite; local disks cover those zeros, and uniform approximation excludes polynomial zeros on the compact remainder. The exact root multiset equality then identifies every arbitrary actual node with a local node.

The full theta source follows Romik's theta/Fourier representation. The Hermite normalization and real simple roots are classical; Mathlib supplies the coefficient convention and the positive-recurrence argument supplies root reality. The analytic-unit and logarithmic-derivative disk argument is the classical argument-principle comparison, proved here with the root multiset and its repetitions. These attributions do not assert a literature originality result.

The unit/logarithm disk comparison retains multiset multiplicities. No RH, simple limiting zero, global hyperbolicity, chosen actual root list, count premise or error premise is included. The threshold is not uniform over growing windows and establishes neither RH nor strict Robin beyond 5040.

## References

- Truth anchor: `D5/S3/Zeros/Jensen/ActualSourceJensenFixedWindow.actual_source_jensen_fixed_window`
- Dependency: [D5/S3/Analytic/Fourier/EvenGaussianMomentSeries](../../Analytic/Fourier/EvenGaussianMomentSeries.md)
- Dependency: [D5/S3/Analytic/Fourier/ThetaDifferentialKernel](../../Analytic/Fourier/ThetaDifferentialKernel.md)
- Dependency: [D5/S3/Analytic/Fourier/XiThetaTransform](../../Analytic/Fourier/XiThetaTransform.md)
- Dependency: [D5/S3/Zeros/Jensen/JensenDiskMultiplicityComparison](JensenDiskMultiplicityComparison.md)
- Dependency: [D5/S3/Zeros/Jensen/JensenHermiteScaling](JensenHermiteScaling.md)
- Dependency: [D5/S3/Zeros/Jensen/JensenSimpleRealStability](JensenSimpleRealStability.md)
- Dependency: [D5/S3/Zeros/Jensen/OriginalTailDerivativeVectorSources](OriginalTailDerivativeVectorSources.md)
- Dependency: [D5/S3/Zeros/Jensen/PositiveThreeTermRootReality](PositiveThreeTermRootReality.md)
- Dependency: [D5/S3/Zeros/Jensen/SourceJensenIntegralExtension](SourceJensenIntegralExtension.md)
- Dependency: [D5/S3/Zeros/Jensen/SourceJensenPositiveExtension](SourceJensenPositiveExtension.md)
- Dependency: [D5/S3/Zeros/Jensen/SourceThetaMomentBounds](SourceThetaMomentBounds.md)
