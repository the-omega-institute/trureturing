# Projective Strong Duality

## Abstract

Finite attained dual minima converge exactly to the full primal value.

**Theorem 1.1 (The finite strong-duality tower has no projective gap).**

$$\begin{aligned}\forall Point: \operatorname{Type}, Test: \mathbb{N} \to \operatorname{Type},\\Gamma: \operatorname{DependentMap}(N: \mathbb{N}, Test(N), Point \to \mathbb{R}),\\e0: \operatorname{DependentMap}(N: \mathbb{N}, Test(N), \mathbb{R}), W: \operatorname{DependentMap}(N: \mathbb{N}, Test(N), \mathbb{R}),\\a: \mathbb{R}, C: \mathbb{R}, Lambda: \mathbb{N} \to \mathbb{R}, Lambda_{\infty}: \mathbb{R},\\\operatorname{let}(D: \mathbb{N} \to \operatorname{Set}(\mathbb{R}), \forall N: \mathbb{N}, D_{N} = \{x\in \mathbb{R} \mid \exists phi: Test(N), \exists theta: \mathbb{R}, 0 \leq theta \land (\forall z: Point, 0 \leq Gamma(N, phi, z) + theta) \land 2a \leq 2ae0(N, phi) + theta \land x = W(N, phi) + thetaC\})\;\\(\forall N: \mathbb{N}, 0 \leq Lambda(N)) \land \operatorname{Antitone}(Lambda) \land\\\operatorname{Tendsto}(Lambda, \operatorname{atTop}(\mathbb{N}), \operatorname{nhds}(Lambda_{\infty})) \land (\forall N: \mathbb{N}, \operatorname{IsLeast}(D_{N}, Lambda(N)))\\\Rightarrow Lambda_{\infty} = \operatorname{inf}_{N\in\mathbb{N}} \operatorname{sInf}(D_{N}) \land\\\forall N: \mathbb{N}, \exists phi: Test(N), \exists theta: \mathbb{R}, 0 \leq theta \land (\forall z: Point, 0 \leq Gamma(N, phi, z) + theta) \land 2a \leq 2ae0(N, phi) + theta \land \operatorname{sInf}(D_{N}) = W(N, phi) + thetaC.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Budget/ProjectiveStrongDuality.projective_strong_duality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The point carrier and the dependent family of finite test spaces are public. The circle slack, evaluation at zero, pairing, budget, finite primal values, and full primal value are all supplied on those carriers.

Every finite dual-value set is constructed from a nonnegative pressure, the pointwise circle-slack inequality, the Haar-floor inequality, and the affine pairing-plus-budget objective. Finite strong duality states that the corresponding primal value is its least element.

Nonnegativity bounds the decreasing primal tower below. Pinned Mathlib monotone convergence identifies its infimum with the supplied full limit, while each finite least-element certificate rewrites that infimum as the attained finite dual minimum.

The public conclusion also returns a feasible minimizer at every finite stage. It makes no assertion that one test and pressure pair attains the full infinite-dimensional dual.

## References

- Truth anchor: `D5/S3/Observer/Budget/ProjectiveStrongDuality.projective_strong_duality`
