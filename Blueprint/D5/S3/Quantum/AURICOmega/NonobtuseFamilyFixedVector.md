# A fixed vector for a nonobtuse family of unit vectors

## Abstract

A nonempty set of unit vectors with pairwise nonnegative inner products in a finite-dimensional real inner product space has a nonzero least-norm point in its closed convex hull, and every linear isometry equivalence mapping the set into itself fixes that point.

**Theorem 1.1 (The least-norm point of the closed convex hull is nonzero and fixed).**

$$\forall E: \operatorname{Type}*, [\operatorname{NormedAddCommGroup}\left(E\right)], [\operatorname{InnerProductSpace}\left(\mathbb{R}, E\right)], [\operatorname{FiniteDimensional}\left(\mathbb{R}, E\right)], \forall S: \operatorname{Set}\left(E\right), \operatorname{Nonempty}\left(S\right) \Rightarrow (\forall s \in S, \left\lVert s \right\rVert = 1) \Rightarrow (\forall s \in S, \forall t \in S, 0 \leq \langle s, t \rangle_{\mathbb{R}}) \Rightarrow \exists m: E, m \neq 0 \land m \in \operatorname{closure}\left(\operatorname{convexHull}\left(\mathbb{R}, S\right)\right) \land (\forall x \in \operatorname{closure}\left(\operatorname{convexHull}\left(\mathbb{R}, S\right)\right), \left\lVert m \right\rVert \leq \left\lVert x \right\rVert) \land (\forall x \in \operatorname{closure}\left(\operatorname{convexHull}\left(\mathbb{R}, S\right)\right), \left\lVert m \right\rVert^{2} \leq \langle x, m \rangle_{\mathbb{R}}) \land (\forall U: \operatorname{LinearIsometryEquiv}\left(\mathbb{R}, E, E\right), \operatorname{image}\left(U, S\right) \subseteq S \Rightarrow U\left(m\right) = m)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/NonobtuseFamilyFixedVector.exists_fixed_ne_zero_of_pairwise_inner_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let E be a finite-dimensional real inner product space and S a nonempty set of unit vectors of E with <s, t> >= 0 for all s and t in S. Write K for the closure of the convex hull of S. Then K contains a point m with m different from 0, ||m|| <= ||x|| and ||m||^2 <= <x, m> for every x in K, and U m = m for every linear isometry equivalence U of E onto itself whose image of S is contained in S. By Caratheodory's theorem every point x of the convex hull of S is a convex combination of at most finrank E + 1 members of S with positive weights w_i. Since all cross terms are nonnegative and the members have norm one, ||x||^2 is at least the sum of the squares of the weights, which by the Cauchy-Schwarz inequality is at least 1 / (finrank E + 1). This bound passes to the closure, so K does not contain 0. The set K is nonempty, closed and convex in a complete space, so it has a point m of least norm, which is therefore nonzero. The variational characterization of the nearest point to 0 gives <0 - m, x - m> <= 0 for x in K, that is ||m||^2 <= <x, m>; together with <x, m> <= ||x|| ||m|| and ||m|| > 0 it gives ||m|| <= ||x||. If x lies in K and ||x|| = ||m||, then ||x - m||^2 = 2 ||m||^2 - 2 <x, m> <= 0, so x = m. A linear isometry equivalence U with image of S inside S maps the convex hull of S into itself by linearity and, being continuous, maps K into K. Hence U m lies in K and has the norm of m, so U m = m.

## References

- Truth anchor: `D5/S3/Quantum/AURICOmega/NonobtuseFamilyFixedVector.exists_fixed_ne_zero_of_pairwise_inner_nonneg`
