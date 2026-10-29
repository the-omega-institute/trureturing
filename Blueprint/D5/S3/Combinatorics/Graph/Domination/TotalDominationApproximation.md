# Joint logarithmic power-root approximation

## Abstract

The same integer exponent approximates both logarithmic coordinates of a complex target.

The complex exponential is the existing Mathlib exponential. No graph or density hypothesis enters this analytic lemma. The conclusion chooses a single natural exponent for both the modulus and angle; it does not combine separately optimal branches.

**Theorem 1.1 (Joint radial and angular approximation).**

$$\forall (xi:\mathbb{C}), (\operatorname{re}\left(xi\right) \ne 0) \Rightarrow (\forall (epsilon:\mathbb{R}), (0 < epsilon) \Rightarrow (\exists (N:\mathbb{N}), \forall (t:\mathbb{R}), \forall (alpha:\mathbb{R}), ((N:\mathbb{R}) + 2 < \frac{t}{\operatorname{re}\left(xi\right)}) \Rightarrow (\exists (k:\mathbb{N}), \exists (w:\mathbb{C}), (0 < k) \land (((w)^{k} = \operatorname{exp}\left((t:\mathbb{C}) + (alpha:\mathbb{C}) \cdot \operatorname{I}\right)) \land (\Vert w - \operatorname{exp}\left(xi\right)\Vert < epsilon)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/TotalDominationApproximation.joint_power_root_approximation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every complex xi with nonzero real part and every positive real epsilon there is a natural N such that, for all real t and alpha with N+2<t/xi.re, there exist a positive natural k and a complex w satisfying w^k=exp(t+alpha*I) and norm(w-exp(xi))<epsilon. Let p=t/xi.re and k=floor(p). The same k obeys k>N and abs(t/k-xi.re)<=abs(xi.re)/k. Round (k*xi.im-alpha)/(2*pi) to an integer j and set v=t/k+((alpha+2*pi*j)/k)*I. Exact exponential periodicity gives (exp(v))^k=exp(t+alpha*I), while abs(v.im-xi.im)<=pi/k. Thus norm(v-xi)<delta for the continuity radius delta of exp at xi. The bound on N is chosen before t and alpha. This is an elementary logarithmic approximation ingredient, with all rounding, powers and continuity checked in Lean; no literature-priority claim is made.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/TotalDominationApproximation.joint_power_root_approximation`
- Dependency: [D5/S3/Combinatorics/Graph/Domination/TotalDominationBlowup](TotalDominationBlowup.md)
