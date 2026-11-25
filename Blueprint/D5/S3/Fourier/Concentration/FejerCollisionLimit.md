# Hard collision limits from differentiable ramp profiles

## Abstract

A differentiable limit of normalized triangular collision moments determines the normalized closed-band mass.

Let the data vary over an arbitrary filter ell on an index type. At each index n, let S(n) be a finite set of real-frequency data with frequencies x(n,i) and real weights c(n,i). Write L_n(r) for the finite weighted collision ramp and E_n(r) for the ordered closed-band mass. Let B and eta be real-valued normalizing factors and radius scales. EventualPairNonnegative(ell,c) means eventually all pair products c(n,i)c(n,j) are nonnegative for i,j in S(n). EventuallyNonnegative(ell,B) and EventuallyPositive(ell,eta) mean eventually B(n)>=0 and eta(n)>0, respectively. Set F(t) to the function n -> B(n)L_n(t eta(n)) and H(a) to the function n -> B(n)eta(n)E_n(a eta(n)). Let f be a real profile, a and d real numbers and R a positive neighborhood radius. HasDerivAt(f,d,a) means that f is differentiable at a with derivative d.

**Theorem 1.1 (Recovery at a differentiable limiting profile).**

$$\left(\operatorname{EventualPairNonnegative}\left(ell, c\right) \land \left(\operatorname{EventuallyNonnegative}\left(ell, B\right) \land \left(\operatorname{EventuallyPositive}\left(ell, eta\right) \land \left(0 < R \land \left(\operatorname{HasDerivAt}\left(f, d, a\right) \land \left(\forall t \in \mathbb{R},\; \operatorname{Abs}\left(t - a\right) < R \Rightarrow \operatorname{Tendsto}\left(\operatorname{F}\left(t\right), ell, \operatorname{nhds}\left(\operatorname{f}\left(t\right)\right)\right)\right)\right)\right)\right)\right)\right) \Rightarrow \operatorname{Tendsto}\left(\operatorname{H}\left(a\right), ell, \operatorname{nhds}\left(d\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/FejerCollisionLimit.collision_ramp_tendsto_hard` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For fixed 0<delta<R, apply the finite collision secants at radius a eta(n) with spacing delta eta(n) and multiply by B(n). Eventually the resulting left and right differences of F bracket delta H(a). Differentiability provides, for each lower or upper comparison with d, a fixed spacing for which the corresponding limiting secant is strictly beyond that comparison. Pointwise convergence at the two endpoints transfers this strict bound to the finite data eventually. These bounds characterize convergence of H(a) to d. The spacings are chosen independently of n.

For varying degree-n frequency families with nonnegative original weights, positive eta(n) eventually and B(n)>=0 eventually, the Fourier identity identifies L_n(r) for r>0 with r times the whole-line angular Fejer moment. If for every fixed t>0 the normalized ramp at radius t eta(n) tends to k t², take a=1, R=1 and f(t)=k t². Then B(n)eta(n)E_n(eta(n)) tends to 2k. In particular, with B(n)=sqrt(n V(n))/(eta(n)^2 W(n)^(2n)) where the total mass W(n), resolution and variance budget are positive eventually, k=1/(2 sqrt(pi)) yields the normalized hard-band coefficient 1/sqrt(pi). The actual zeta-tail upper estimate and control of noncentral contributions at neighboring radii are additional arithmetic obligations.

## References

- Truth anchor: `D5/S3/Fourier/Concentration/FejerCollisionLimit.collision_ramp_tendsto_hard`
- Dependency: [D5/S3/Fourier/Concentration/FejerCollisionSecants](FejerCollisionSecants.md)
