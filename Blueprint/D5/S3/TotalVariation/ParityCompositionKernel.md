# Parity Composition Kernels

## Abstract

The composition parity mass and a biased Bernoulli mass have the same prescribed terminal parity.

**Definition 1.1 (Composition parity mass).**

$$\operatorname{R}\left(d, M, \xi\right) = \operatorname{ite}\left((\operatorname{mod}\left(h, 2\right) = \operatorname{mod}\left(M, 2\right)) \land (h \leq M), \frac{\operatorname{choose}\left(\frac{M - h}{2} + d - 1, d - 1\right)}{\operatorname{choose}\left(M + d - 1, d - 1\right)}, 0\right)$$

*Formalization.* `D5/S3/TotalVariation/ParityCompositionKernel.R` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The parameters d and M are natural numbers, xi : Fin d -> Bool, and h is the sum of the Boolean digits. The guard requires h <= M and h mod 2 = M mod 2. The mass is zero when either test fails; the binomial coefficient in the nonzero branch is evaluated only for the resulting natural parameters. Its numerator counts the weak compositions after subtracting the parity vector and dividing each part by two.

**Definition 1.2 (Conditioned Bernoulli mass).**

$$\operatorname{Q}\left(d, M, \xi\right) = \operatorname{ite}\left(\operatorname{mod}\left(h, 2\right) = \operatorname{mod}\left(M, 2\right), \frac{\nu^{h} \cdot (1 - \nu)^{d - h}}{p_{e}}, 0\right)$$

*Formalization.* `D5/S3/TotalVariation/ParityCompositionKernel.Q` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Here nu = M/(2M+d), eta = d/(2M+d), and p_e = (1+(-1)^M eta^d)/2. The mass is zero when h mod 2 differs from M mod 2. For positive d and M, this formula describes independent Bernoulli(nu) bits conditioned on the terminal parity. The conditioned bits are not asserted to be independent.

**Definition 1.3 (Logarithmic profile).**

$$\operatorname{logProfile}\left(d, M, x\right) = \sum_{j=1}^{d - 1} \operatorname{log}\left(M - x + 2 \cdot j\right) - x \cdot \operatorname{log}\left(\frac{M}{M + d}\right)$$

*Formalization.* `D5/S3/TotalVariation/ParityCompositionKernel.logProfile` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The continuous profile is the sum of the logarithms of all d-1 composition factors, minus x log(tau), where tau = M/(M+d). The center m = dM/(2M+d) is the mean of the unconditioned Bernoulli total, rather than the conditional mean.

**Theorem 1.4 (Centered endpoint error).**

$$\forall d,M \in \mathbb{N}, ((2 \leq d) \land (3 \cdot d \leq M)) \Rightarrow (0 \leq s) \land (s \leq \frac{1}{M - d})$$

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/ParityCompositionKernel.profile_endpoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For d >= 2 and M >= 3d, the centered reciprocal error is s = -sum_{j=1}^{d-1} 1/(M-m+2j) - log(tau). The integral of 1/(M-m+2y) from zero to d is exactly -log(tau). The function is positive and decreasing. Comparing its complete reciprocal sum with the two shifted integrals leaves an error between zero and the integral from zero to one, which is at most 1/(M-d).

**Theorem 1.5 (Full interval profile bound).**

$$\forall d,M \in \mathbb{N}, ((2 \leq d) \land (3 \cdot d \leq M)) \Rightarrow \forall x \in [0,d], (|\operatorname{logProfile}\left(d, M, x\right) - \operatorname{logProfile}\left(d, M, m\right)| \leq \frac{|x - m|}{M - d} + \frac{\left(d - 1\right) \cdot (x - m)^{2}}{(M - \frac{d}{2}) \cdot (M - d)}) \land (\operatorname{logProfile}\left(d, M, x\right) - \operatorname{logProfile}\left(d, M, m\right) \leq \frac{1}{2})$$

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/ParityCompositionKernel.profile_estimate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Put Delta = x-m, T = M-d and L = M-d/2. Since m <= d/2, each centered factor a_j = M-m+2j satisfies a_j >= L and a_j-|Delta| >= T. The logarithm-series remainder bounds |log(1-Delta/a_j)+Delta/a_j| by Delta^2/(L T). Summing all d-1 remainders and using the centered endpoint error gives the absolute profile bound. The logarithm tangent inequality gives the signed upper bound, and d/(M-d) <= 1/2 gives the final cap. Both bounds cover the whole interval, including both sides of m.

**Theorem 1.6 (Prescribed parity composition count).**

$$\forall d,M \in \mathbb{N}, 1 \leq d \Rightarrow \forall \xi, \operatorname{card}\left(\operatorname{parityFiber}\left(d, M, \xi\right)\right) = \operatorname{ite}\left((\operatorname{mod}\left(h, 2\right) = \operatorname{mod}\left(M, 2\right)) \land (h \leq M), \operatorname{choose}\left(\frac{M - h}{2} + d - 1, d - 1\right), 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/ParityCompositionKernel.composition_parity_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In every positive dimension, a legal parity vector has choose((M-h)/2+d-1,d-1) weak compositions. The coordinatewise substitution r_i=2t_i+xi_i is bijective. An illegal parity vector has no preimage.

**Theorem 1.7 (Composition mass normalization).**

$$\forall d,M \in \mathbb{N}, 1 \leq d \Rightarrow \sum_{\xi} \operatorname{R}\left(d, M, \xi\right) = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/ParityCompositionKernel.actual_normalization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive dimension d and every natural total M, the composition parity masses sum to one. The sum runs over all Boolean vectors xi : Fin d -> Bool. The weak compositions of M partition according to their complete parity vector. A legal vector with h occupied coordinates has exactly choose((M-h)/2+d-1,d-1) preimages, through the bijection r_i = 2t_i + xi_i. An illegal vector has no preimages. Summing these fiber counts and dividing by the total choose(M+d-1,d-1) proves normalization.

**Theorem 1.8 (Conditional centered moments).**

$$\forall d,M \in \mathbb{N}, ((1 \leq d) \land (d \leq M)) \Rightarrow (\sum_{\xi} \operatorname{Q}\left(d, M, \xi\right) = 1) \land ((\frac{1}{3} \leq p_{e}) \land ((\sum_{\xi} \operatorname{Q}\left(d, M, \xi\right) \cdot (h - m)^{2} \leq \frac{3 \cdot d}{4}) \land (\sum_{\xi} \operatorname{Q}\left(d, M, \xi\right) \cdot |h - m| \leq \frac{\operatorname{sqrt}\left(3 \cdot d\right)}{2})))$$

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/ParityCompositionKernel.reference_moments` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The independent Bernoulli vector has generating function (1-nu+nu z)^d. Its value at z=-1 gives the parity event probability; differentiating twice at z=1 gives the centered second moment d nu (1-nu). For d >= 1 and M >= d, eta <= 1/3 and p_e >= 1/3. Restricting the nonnegative squared deviation to the parity event and dividing by p_e bounds its conditional expectation by 3d/4. Weighted Cauchy-Schwarz then gives the absolute deviation bound sqrt(3d)/2. Both moments are centered at m=d nu.

**Theorem 1.9 (Finite total variation bound).**

$$(\forall d,M \in \mathbb{N}, ((2 \leq d) \land (3 \cdot d \leq M)) \Rightarrow \operatorname{totalVariation}\left(\operatorname{R}\left(d, M\right), \operatorname{Q}\left(d, M\right)\right) \leq \operatorname{min}\left(1, 5 \cdot (\frac{\operatorname{sqrt}\left(d\right)}{M} + \frac{d \cdot \left(d - 1\right)}{M^{2}})\right)) \land (\forall M \in \mathbb{N}, 1 \leq M \Rightarrow \operatorname{R}\left(1, M\right) = \operatorname{Q}\left(1, M\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/ParityCompositionKernel.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all natural d >= 2 and M >= 3d, one half of the sum over every Boolean vector of the absolute mass difference is at most min(1,5(sqrt(d)/M+d(d-1)/M^2)). For d=1 and every M>=1 the two mass functions coincide. On the prescribed parity support, the binomial product expansion makes the density ratio proportional to exp(logProfile(h)). Centering at m gives X=logProfile(h)-logProfile(m). The interval estimate and the conditional moments bound its absolute expectation by D=sqrt(3d)/(2(M-d))+3d(d-1)/(4(M-d/2)(M-d)), with D<=1/2. Finite Jensen gives the normalization bound exp(-D), and the derivative bound for exp on (-infinity,1/2] bounds the mean absolute exponential error. The normalized total variation is at most exp(1/2+D)D<=3D, which is bounded by the displayed expression. The unit bound follows from normalization and nonnegativity of both finite mass functions.

## References

- Truth anchor: `D5/S3/TotalVariation/ParityCompositionKernel.Q`
- Truth anchor: `D5/S3/TotalVariation/ParityCompositionKernel.R`
- Truth anchor: `D5/S3/TotalVariation/ParityCompositionKernel.actual_normalization`
- Truth anchor: `D5/S3/TotalVariation/ParityCompositionKernel.composition_parity_count`
- Truth anchor: `D5/S3/TotalVariation/ParityCompositionKernel.logProfile`
- Truth anchor: `D5/S3/TotalVariation/ParityCompositionKernel.profile_endpoint`
- Truth anchor: `D5/S3/TotalVariation/ParityCompositionKernel.profile_estimate`
- Truth anchor: `D5/S3/TotalVariation/ParityCompositionKernel.reference_moments`
- Truth anchor: `D5/S3/TotalVariation/ParityCompositionKernel.result`
- Dependency: [D5/S3/TotalVariation/Metric](Metric.md)
