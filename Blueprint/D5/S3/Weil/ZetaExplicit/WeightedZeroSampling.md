# Weighted zero sampling

## Abstract

Supported complex L2 profiles admit convolution reproduction and two multiplicity-weighted zero sampling bounds.

**Definition 1.1 (Angular convolution kernel).**

Lean statement: `D5/S3/Weil/ZetaExplicit/WeightedZeroSampling.stripKernel`

*Formalization.* `D5/S3/Weil/ZetaExplicit/WeightedZeroSampling.stripKernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For an even smooth compactly supported complex test function b and real beta,u, define stripKernel(b,beta,u) as paperFT(b,u+i*beta)/(2*pi). The paper transform has the PLUS angular exponent exp(+i*z*x). The inverse transform uses exp(-i*u*x) and the factor 1/(2*pi).

**Theorem 1.2 (Pointwise reproduction on the closed strip).**

Lean statement: `D5/S3/Weil/ZetaExplicit/WeightedZeroSampling.support_convolution_reproduction`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaExplicit/WeightedZeroSampling.support_convolution_reproduction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let b be an even smooth compactly supported complex cutoff, equal to one on Ioc(-a,a). Let f be a complex MemLp profile of exponent two on the real line, zero almost everywhere outside that literal half-open interval. For every real t and beta with |beta|<=1/2, the integral of K_beta(t-s)*paperFT(f,s) equals paperFT(f,t+i*beta). Here paperFT uses exp(+i*z*x), with no prefactor, and K_beta(u)=paperFT(b,u+i*beta)/(2*pi).

Finite support first gives integrability of f. The existing closed-strip two-jet budget bounds K_beta by C/(1+u^2), with C=closedStripJetBudget(b,1/2)/(2*pi). The cutoff multiplied by exp(-beta*x) is smooth and compactly supported. Its Fourier inversion has negative angular exponent and prefactor 1/(2*pi). The norm of the double integrand for reproduction is |K_beta(t-s)|*|f(x)|, an integrable product. Fubini therefore holds without requiring the real-line transform of f to be L1. The cutoff plateau is applied only where the actual profile is supported. The resulting identity holds at every strip point.

**Theorem 1.3 (Both original zero sample families).**

Lean statement: `D5/S3/Weil/ZetaExplicit/WeightedZeroSampling.weighted_zero_sampling_Ioc`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaExplicit/WeightedZeroSampling.weighted_zero_sampling_Ioc` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every a>0 there is a finite nonnegative real C_a, chosen before Z, A, and f. Let Z be the original ZeroConfig, A>=1, and assume Z.N(t,t+1)<=A*log(|t|+3) for every real t, with the original natural multiplicities. Let f be an arbitrary complex L2 profile zero almost everywhere outside Ioc(-a,a), and assume integrability of log(|s|+3)*normSq(paperFT(f,s)). Then f is L1. Each of the families m(rho)*normSq(paperFT(f,gammaOf(rho))) and m(rho)*normSq(paperFT(f,conj(gammaOf(rho)))) is summable, and each sum is at most C_a*A*totalWeight times that same log-weighted integral.

Choose an even smooth bump equal to one on [-a,a], with outer radius a+1. Weighted Cauchy-Schwarz applied to the reproducing convolution bounds the squared value at t+i*beta by pi*C^2 times the integral of normSq(paperFT(f,s))/(1+(t-s)^2). The logarithmic integrability assumption ensures these nonnegative integrals are finite. The existing WindowZero shifted kernel theorem, instantiated with Im(rho), Z.mult, and the original local count, bounds finite zero kernel sums by 8*A*totalWeight*log(|s|+3). Integrate each finite sum and then pass to the summable nonnegative family. Thus C_a=8*pi*C^2 works for both signs of the imaginary part of gammaOf.

No zero spacing, RH, smoothness, parity, or boundary trace is assumed for f. The two actual complex sample maps remain distinct. This theorem supplies an upper sampling estimate; it does not identify an explicit-formula form domain, prove a lower sampling estimate or global positivity, or prove RH.

## References

- Truth anchor: `D5/S3/Weil/ZetaExplicit/WeightedZeroSampling.stripKernel`
- Truth anchor: `D5/S3/Weil/ZetaExplicit/WeightedZeroSampling.support_convolution_reproduction`
- Truth anchor: `D5/S3/Weil/ZetaExplicit/WeightedZeroSampling.weighted_zero_sampling_Ioc`
- Dependency: [D5/S3/Weil/ZeroInfinitude/WindowZero](../ZeroInfinitude/WindowZero.md)
