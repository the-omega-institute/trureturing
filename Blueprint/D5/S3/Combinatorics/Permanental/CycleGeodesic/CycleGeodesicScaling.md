# CycleGeodesicScaling

## Abstract

The permanent rate tends to the closed cotangent expression, with the odd midpoint limit one.

**Definition 1.1 (delta).**

$$\forall t \in \mathbb{R},\; \operatorname{delta}\left(t\right) = \operatorname{min}\left(t, 1 - t\right)$$

*Formalization.* `D5/S3/Combinatorics/Permanental/CycleGeodesic/CycleGeodesicScaling.delta` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Igor Rivin (2026). *Permanents of matrix ensembles: computation, distribution, and geometry*. URL: <https://arxiv.org/abs/2602.10141v3>.

*Commentary.*

Reflection selects the distance to the nearer endpoint.

**Definition 1.2 (rate).**

$$\forall n \in \mathbb{N},\; \forall t \in \mathbb{R},\; \operatorname{rate}\left(n, t\right) = -\frac{1}{(n:\mathbb{R})} \cdot \operatorname{Real.log}\left(\left\lVert \operatorname{Matrix.permanent}\left(\operatorname{gamma}\left(n, t\right)\right) \right\rVert\right)$$

*Formalization.* `D5/S3/Combinatorics/Permanental/CycleGeodesic/CycleGeodesicScaling.rate` (`✓ std3`).

*Citation.* Igor Rivin (2026). *Permanents of matrix ensembles: computation, distribution, and geometry*. URL: <https://arxiv.org/abs/2602.10141v3>.

*Commentary.*

Page 7, Observation 4: "Define f(t) = -(1/n) ln|perm(γ(t)).|. Then f(t) converges to a universal function of t as n → ∞, with the properties:" Here rate n t is the finite-dimensional quantity; the printed period inside the absolute value is a typographical artifact.

**Definition 1.3 (universal).**

$$\forall t \in \mathbb{R},\; \operatorname{universal}\left(t\right) = 1 - \operatorname{Real.pi} \cdot \operatorname{delta}\left(t\right) \cdot \operatorname{Real.cot}\left(\operatorname{Real.pi} \cdot \operatorname{delta}\left(t\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Permanental/CycleGeodesic/CycleGeodesicScaling.universal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Igor Rivin (2026). *Permanents of matrix ensembles: computation, distribution, and geometry*. URL: <https://arxiv.org/abs/2602.10141v3>.

*Commentary.*

This expression gives the closed form on the interior. Reflection symmetry, the continuous zero endpoint values and the quadratic Gaussian onset follow from the cotangent expression; the midpoint value is one. These analytic consequences explain the relation to Observation 4, while the settling theorem states the interior limit and the odd-dimensional midpoint limit.

**Definition 1.4 (claim3).**

$$claim3 \Leftrightarrow \left((\forall t \in \mathbb{R},\; 0 < t \Rightarrow \left(t < 1 \Rightarrow \left(t \ne \frac{1}{2} \Rightarrow \operatorname{Tendsto}\left(fun (n:\mathbb{N}) \mapsto \operatorname{rate}\left(n, t\right), \operatorname{Filter.atTop}, \operatorname{nhds}\left(\operatorname{universal}\left(t\right)\right)\right)\right)\right)) \land (\operatorname{Tendsto}\left(fun (m:\mathbb{N}) \mapsto \operatorname{rate}\left(2 \cdot m + 1, \frac{1}{2}\right), \operatorname{Filter.atTop}, \operatorname{nhds}\left(1\right)\right))\right)$$

*Formalization.* `D5/S3/Combinatorics/Permanental/CycleGeodesic/CycleGeodesicScaling.claim3` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Igor Rivin (2026). *Permanents of matrix ensembles: computation, distribution, and geometry*. URL: <https://arxiv.org/abs/2602.10141v3>.

*Commentary.*

Page 19, Section 8.4, Open Problem 3: "Find a closed form for the universal function f(t)." The encoding identifies this function by the all-dimension rate limit at every t in (0,1) except 1/2, and by the odd-dimensional limit at 1/2. The endpoint values refer to continuous extension.

**Theorem 1.5 (result3).**

$$(\forall t \in \mathbb{R},\; 0 < t \Rightarrow \left(t < 1 \Rightarrow \left(t \ne \frac{1}{2} \Rightarrow \operatorname{Tendsto}\left(fun (n:\mathbb{N}) \mapsto \operatorname{rate}\left(n, t\right), \operatorname{Filter.atTop}, \operatorname{nhds}\left(\operatorname{universal}\left(t\right)\right)\right)\right)\right)) \land (\operatorname{Tendsto}\left(fun (m:\mathbb{N}) \mapsto \operatorname{rate}\left(2 \cdot m + 1, \frac{1}{2}\right), \operatorname{Filter.atTop}, \operatorname{nhds}\left(1\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permanental/CycleGeodesic/CycleGeodesicScaling.result3` (`✓ std3`). ∎

*Resolves.* `Problems/rivin-2026-cycle-geodesic-universal-function` (proved) by `D5/S3/Combinatorics/Permanental/CycleGeodesic/CycleGeodesicScaling.result3`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"rivin-2026-cycle-geodesic-universal-function","declaration_gid":"D5/S3/Combinatorics/Permanental/CycleGeodesic/CycleGeodesicScaling.result3","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Igor Rivin (2026). *Permanents of matrix ensembles: computation, distribution, and geometry*. URL: <https://arxiv.org/abs/2602.10141v3>.

*Commentary.*

The exact product turns the logarithmic rate into a left Riemann sum. Uniform continuity gives convergence away from the midpoint, and an elementary quadratic-logarithm integral gives 1 - pi delta cot(pi delta). The explicit odd midpoint estimate supplies the remaining limit.

## References

- Truth anchor: `D5/S3/Combinatorics/Permanental/CycleGeodesic/CycleGeodesicScaling.claim3`
- Truth anchor: `D5/S3/Combinatorics/Permanental/CycleGeodesic/CycleGeodesicScaling.delta`
- Truth anchor: `D5/S3/Combinatorics/Permanental/CycleGeodesic/CycleGeodesicScaling.rate`
- Truth anchor: `D5/S3/Combinatorics/Permanental/CycleGeodesic/CycleGeodesicScaling.result3`
- Truth anchor: `D5/S3/Combinatorics/Permanental/CycleGeodesic/CycleGeodesicScaling.universal`
- Dependency: [D5/S3/Combinatorics/Permanental/CycleGeodesic/CycleGeodesicMidpoint](CycleGeodesicMidpoint.md)
