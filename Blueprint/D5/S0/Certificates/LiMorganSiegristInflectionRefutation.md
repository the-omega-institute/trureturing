# Nonuniqueness of the fractional concavity transition

## Abstract

An admissible polynomial forcing produces two distinct zeros of the second derivative.

**Definition 1.1 (The fractional integral).**

$$\forall \alpha: \mathbb{R}, \forall u: \mathbb{R} \to \mathbb{R}, \forall x: \mathbb{R}, \operatorname{rlIntegral}\left(\alpha, u, x\right) = \operatorname{Real.Gamma}\left(\alpha\right)^{-1} \cdot \int_{0}^{x} (x - t)^{\alpha - 1} \cdot u\left(t\right) dt$$

*Formalization.* `D5/S0/Certificates/LiMorganSiegristInflectionRefutation.rlIntegral` (`✓ std3`).

*Citation.* Yulong Li; Rachel Morgan; Michael Siegrist (2026). *Concavity structure of fractional differential equations and zeros of Mittag–Leffler functions*. DOI: [10.1007/s41478-026-01192-9](https://doi.org/10.1007/s41478-026-01192-9). URL: <https://link.springer.com/article/10.1007/s41478-026-01192-9>.

*Commentary.*

Definition 1.1, PDF p. 2: “For α > 0, the left-sided Riemann–Liouville fractional integral of a locally integrable function u is defined by I^α_{a+}u(x) = (1/Γ(α)) ∫_a^x (x − t)^{α−1} u(t) dt, x > a, whenever the integral is finite.” The formula specializes a to zero. Real powers and the interval integral are Lean's Real.rpow and intervalIntegral.integral. Lean defines the integral for all real parameters; its interpretation here uses positive order and positive x.

**Definition 1.2 (The integral representation of the solution).**

$$\forall \alpha: \mathbb{R}, \forall f: \mathbb{R} \to \mathbb{R}, \forall x: \mathbb{R}, \operatorname{solution}\left(\alpha, f, x\right) = \operatorname{rlIntegral}\left(\alpha, f, x\right) - \operatorname{rlIntegral}\left(\alpha, f, 1\right) \cdot x^{\alpha - 1}$$

*Formalization.* `D5/S0/Certificates/LiMorganSiegristInflectionRefutation.solution` (`✓ std3`).

*Citation.* Yulong Li; Rachel Morgan; Michael Siegrist (2026). *Concavity structure of fractional differential equations and zeros of Mittag–Leffler functions*. DOI: [10.1007/s41478-026-01192-9](https://doi.org/10.1007/s41478-026-01192-9). URL: <https://link.springer.com/article/10.1007/s41478-026-01192-9>.

*Commentary.*

Section 3, equation (7), PDF p. 11: the weak solution “is equivalently represented by u(x) = (I^α_{0+}f)(x) + c x^{α−1}, c = −(I^α_{0+}f)(1), x ∈ [0, 1]. (7) Conversely, the function defined by this formula is the unique weak solution”. The displayed expression substitutes the value of c. The representation defines solution; equivalence with the fractional Sobolev weak formulation is supplied by the source.

**Definition 1.3 (The assumptions on the forcing).**

$$\forall \alpha: \mathbb{R}, \forall f: \mathbb{R} \to \mathbb{R}, (\operatorname{Hypotheses}\left(\alpha, f\right)) \Leftrightarrow ((\operatorname{ContinuousOn}\left(f, \operatorname{Set.Icc}\left(0, 1\right)\right)) \land ((\operatorname{ContDiffOn}\left(\mathbb{R}, 1, f, \operatorname{Set.Ioc}\left(0, 1\right)\right)) \land ((f\left(1\right) = 0) \land ((\forall x: \mathbb{R}, (x \in \operatorname{Set.Icc}\left(0, 1\right)) \Rightarrow (0 \le f\left(x\right))) \land ((\exists x: \mathbb{R}, (x \in \operatorname{Set.Icc}\left(0, 1\right)) \land (f\left(x\right) \ne 0)) \land (\operatorname{Tendsto}\left((\lambda x: \mathbb{R} \mapsto x^{\frac{3 - \alpha}{2 - \alpha}} \cdot \operatorname{deriv}\left(f, x\right)), \operatorname{nhdsWithin}\left(0, \operatorname{Set.Ioi}\left(0\right)\right), \operatorname{nhds}\left(0\right)\right)))))))$$

*Formalization.* `D5/S0/Certificates/LiMorganSiegristInflectionRefutation.Hypotheses` (`✓ std3`).

*Citation.* Yulong Li; Rachel Morgan; Michael Siegrist (2026). *Concavity structure of fractional differential equations and zeros of Mittag–Leffler functions*. DOI: [10.1007/s41478-026-01192-9](https://doi.org/10.1007/s41478-026-01192-9). URL: <https://link.springer.com/article/10.1007/s41478-026-01192-9>.

*Commentary.*

Theorem 5.2, PDF p. 27: “Let f ∈ C([0, 1]) ∩ C¹((0, 1]) satisfy f(1) = 0 and f ≥ 0 on [0, 1], with f ≢ 0. Assume, in addition, that lim_{x→0+} x^{(3−α)/(2−α)} f′(x) = 0.” ContinuousOn and ContDiffOn express the two regularity requirements on Set.Icc 0 1 and Set.Ioc 0 1. The right-sided limit uses nhdsWithin 0 (Set.Ioi 0), and deriv f is the derivative occurring in that limit.

**Definition 1.4 (Conjecture 6.1).**

$$(claim) \Leftrightarrow (\forall \alpha: \mathbb{R}, (1 < \alpha) \Rightarrow ((\alpha < 2) \Rightarrow (\forall f: \mathbb{R} \to \mathbb{R}, (\operatorname{Hypotheses}\left(\alpha, f\right)) \Rightarrow (\exists \xi: \mathbb{R}, (\xi \in \operatorname{Set.Ioo}\left(0, 1\right)) \land ((\operatorname{iteratedDeriv}\left(2, \operatorname{solution}\left(\alpha, f\right), \xi\right) = 0) \land ((\forall eta: \mathbb{R}, (eta \in \operatorname{Set.Ioo}\left(0, 1\right)) \Rightarrow ((\operatorname{iteratedDeriv}\left(2, \operatorname{solution}\left(\alpha, f\right), eta\right) = 0) \Rightarrow (eta = \xi))) \land (\exists \delta: \mathbb{R}, (0 < \delta) \land (\forall y: \mathbb{R}, \forall z: \mathbb{R}, (\xi - \delta < y) \Rightarrow ((y < \xi) \Rightarrow ((\xi < z) \Rightarrow ((z < \xi + \delta) \Rightarrow (\operatorname{iteratedDeriv}\left(2, \operatorname{solution}\left(\alpha, f\right), y\right) \cdot \operatorname{iteratedDeriv}\left(2, \operatorname{solution}\left(\alpha, f\right), z\right) < 0))))))))))))$$

*Formalization.* `D5/S0/Certificates/LiMorganSiegristInflectionRefutation.claim` (`✓ std3`).

*Citation.* Yulong Li; Rachel Morgan; Michael Siegrist (2026). *Concavity structure of fractional differential equations and zeros of Mittag–Leffler functions*. DOI: [10.1007/s41478-026-01192-9](https://doi.org/10.1007/s41478-026-01192-9). URL: <https://link.springer.com/article/10.1007/s41478-026-01192-9>.

*Commentary.*

Conjecture 6.1, PDF p. 43: “Let 1 < α < 2. Under the hypotheses of Theorem 5.2, the second derivative F″ has exactly one zero in (0, 1). Moreover, F″ changes sign at this zero, so that this point is the unique inflection point of F.” The source adds: “At present, even the uniqueness of the inflection point remains open”. The solution is represented by equation (7); iteratedDeriv 2 is its second derivative. Uniqueness quantifies over all zeros in Set.Ioo 0 1. Sign change means a negative product at every pair of points sufficiently close on opposite sides of the zero.

**Theorem 1.5 (Conjecture 6.1 is false).**

$$\neg(\forall \alpha: \mathbb{R}, (1 < \alpha) \Rightarrow ((\alpha < 2) \Rightarrow (\forall f: \mathbb{R} \to \mathbb{R}, (\operatorname{Hypotheses}\left(\alpha, f\right)) \Rightarrow (\exists \xi: \mathbb{R}, (\xi \in \operatorname{Set.Ioo}\left(0, 1\right)) \land ((\operatorname{iteratedDeriv}\left(2, \operatorname{solution}\left(\alpha, f\right), \xi\right) = 0) \land ((\forall eta: \mathbb{R}, (eta \in \operatorname{Set.Ioo}\left(0, 1\right)) \Rightarrow ((\operatorname{iteratedDeriv}\left(2, \operatorname{solution}\left(\alpha, f\right), eta\right) = 0) \Rightarrow (eta = \xi))) \land (\exists \delta: \mathbb{R}, (0 < \delta) \land (\forall y: \mathbb{R}, \forall z: \mathbb{R}, (\xi - \delta < y) \Rightarrow ((y < \xi) \Rightarrow ((\xi < z) \Rightarrow ((z < \xi + \delta) \Rightarrow (\operatorname{iteratedDeriv}\left(2, \operatorname{solution}\left(\alpha, f\right), y\right) \cdot \operatorname{iteratedDeriv}\left(2, \operatorname{solution}\left(\alpha, f\right), z\right) < 0))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/LiMorganSiegristInflectionRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/li-morgan-siegrist-2026-inflection-points-conjecture-6-1` (refuted) by `D5/S0/Certificates/LiMorganSiegristInflectionRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"li-morgan-siegrist-2026-inflection-points-conjecture-6-1","declaration_gid":"D5/S0/Certificates/LiMorganSiegristInflectionRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Yulong Li; Rachel Morgan; Michael Siegrist (2026). *Concavity structure of fractional differential equations and zeros of Mittag–Leffler functions*. DOI: [10.1007/s41478-026-01192-9](https://doi.org/10.1007/s41478-026-01192-9). URL: <https://link.springer.com/article/10.1007/s41478-026-01192-9>.

*Commentary.*

Take α = 3/2 and f(x) = (1 − x)(1 + 5x¹²). This polynomial satisfies all six assumptions in Hypotheses. Multiplying the second derivative by the positive factor x^(3/2) Γ(3/2) gives the polynomial 180640483/1764461790 + x/2 − x² + (10485760/676039)x¹³ − (4194304/260015)x¹⁴. Its signs at 7/10, 3/4 and 4/5 are positive, negative and positive. Continuity gives one zero in each of the disjoint intervals (7/10, 3/4) and (3/4, 4/5), contradicting uniqueness. This proves nonuniqueness; an exact count of three zeros and simplicity of those zeros are not conclusions of this theorem. The at-least-one conclusion of Theorem 5.2 is compatible with this example, and the principal-eigenfunction Mittag–Leffler zero question is unaffected.

## References

- Truth anchor: `D5/S0/Certificates/LiMorganSiegristInflectionRefutation.Hypotheses`
- Truth anchor: `D5/S0/Certificates/LiMorganSiegristInflectionRefutation.claim`
- Truth anchor: `D5/S0/Certificates/LiMorganSiegristInflectionRefutation.result`
- Truth anchor: `D5/S0/Certificates/LiMorganSiegristInflectionRefutation.rlIntegral`
- Truth anchor: `D5/S0/Certificates/LiMorganSiegristInflectionRefutation.solution`
