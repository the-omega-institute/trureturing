# The complete arithmetic kernel

## Abstract

Global strict Gram positivity of the complete arithmetic kernel under RH

**Theorem 1.1 (RH gives strict positivity at arbitrary distinct real nodes).**

$$\operatorname{RiemannHypothesis} \Rightarrow \left(\forall n \in \mathbb{N},\; \forall x \in \operatorname{Fin}\left(n\right) \to \mathbb{R},\; \operatorname{Injective}\left(x\right) \Rightarrow \operatorname{PosDef}\left(i, j \mapsto \operatorname{ofReal}\left(\operatorname{K}\left(x\left(j\right) - x\left(i\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelGlobalStrictPositivity.actual_kernel_strict_gram_of_rh` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume the Riemann hypothesis. For every natural number n and injective real-node map x from Fin n, the complex matrix with entry K(x_j-x_i) is positive definite. Here K is the original real arithmetic kernel from ActualKernelLocalPositivity: K(t)=exp(-|t|/2)*(U(exp(|t|))-log(2*pi)+trivialT(|t|)). The original U(x) is x times the inclusive sum of Lambda(m)/m over 0<m<=floorNat(x), minus Chebyshev psi(x), minus x*log(x), plus (1+gammaE)*x. Lambda is the full von Mangoldt function and gammaE is the Euler-Mascheroni constant. The full trivial correction is trivialT(y)=sum_{j>=1} exp(-2*j*y)/(2*j*(2*j+1)). All prime powers and all trivial zeros are retained.

The only arithmetic hypothesis is RH. There is no assumed global Fourier representation, positive semidefinite conclusion or regularity conclusion. No simplicity, linear independence, ordinate gap, multiplicity bound or density statement about distinct ordinates is required. Nodes have arbitrary diameter; the empty configuration is included.

For the exhaustive actual analytic occurrence family write rho_k=1/2+i*gamma_k under RH. Each occurrence carries its full multiplicity. Algebra gives 1/(rho_k*(1-rho_k))=1/(1/4+gamma_k^2), a strictly positive real number. The public actual coefficient mass and absolute convergence of the actual H series apply to this entire family. At positive y the complete integrated explicit formula identifies H(y) with U(exp(y))-log(2*pi)+trivialT(y). At zero the coefficient mass gives H(0)=firstLiMass, while K(0)=firstLiMass. Consequently exp(-|t|/2)*H(|t|) equals the real number K(t), also at t=0.

Taking real parts term by term in the absolutely convergent normalized series gives K(t)=sum_k cos(gamma_k*t)/(1/4+gamma_k^2). The factors exp(-|t|/2) and exp(|t|/2) cancel exactly. Evenness of cosine replaces |t| by t for each term, so no occurrence permutation is needed. Each cosine kernel is half the sum of the characters at opposite frequencies. For arbitrary complex coefficients its Gram energy is half the sum of the two squared moduli, one at each frequency. Each finite partial sum is therefore a sum of nonnegative multiples of positive semidefinite cosine kernels. Entrywise limits preserve every finite positive semidefinite Gram inequality, giving positive semidefinite Gram matrices for the original K.

Fix a nonzero base point r. Choose a natural N strictly greater than exp(|r|); continuity keeps exp(|t|)<N near r. The complete ramp identities then give U(exp(|t|))=sum_{m<N} Lambda(m)*max(exp(|t|)/m-1,0)-exp(|t|)*|t|+(1+gammaE)*exp(|t|) on that neighborhood. The terms m=0 and m=1 vanish. The inequality |max(a,0)-max(b,0)|<=|a-b| transfers the pointwise derivative increment bound of exp(|t|)/m-1 to each ramp, including every prime-power activation point. The remaining elementary terms are differentiable at r. The full trivial correction is differentiable at |r|>0, with trivialT'(y)=trivialT(y)+(1/2)*log(1-exp(-2*y)). Finite sums and multiplication by the smooth exponential therefore give K(r+h)-K(r)=O(h). No floor derivative or truncated correction enters this argument.

At the origin K is continuous, including the endpoint. For 0<t<log(2), its public derivative is D1(t)=K(t)/2-exp(t/2)+exp(-t/2)*(log(2*pi)+(1/2)*log(1-exp(-2*t))). The public limit D1(t) tends to negative infinity as t decreases to zero. If |K(t)-K(0)|<=C*t held for all sufficiently small positive t, choose a smaller interval on which D1<-(C+1). The mean value theorem on [0,t], using endpoint continuity and differentiability throughout (0,t), would give (K(t)-K(0))/t<-(C+1), contradicting that bound. Thus no O(h) increment bound exists at zero. Applying the isolated-singularity theorem gives strictness for every finite injective configuration.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelGlobalStrictPositivity.actual_kernel_strict_gram_of_rh`
- Dependency: [D5/S3/Analytic/Fourier/PositiveDefinite/IsolatedSingularity](../../../Analytic/Fourier/PositiveDefinite/IsolatedSingularity.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelLocalPositivity](ActualKernelLocalPositivity.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/WholeFormula](WholeFormula.md)
- Dependency: [D5/S3/Weil/ZetaBridge/RhLocatesZeroData](../../ZetaBridge/RhLocatesZeroData.md)
