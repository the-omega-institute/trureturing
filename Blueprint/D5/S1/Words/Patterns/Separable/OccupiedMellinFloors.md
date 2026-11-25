# Integer cutoffs for paired Mellin quadrature

## Abstract

Natural floor cutoffs give a uniform algebraic rate for the shifted Mellin quadrature.

**Theorem 1.1 (Uniform error at the natural mesh resolution).**

$$\begin{gathered}\forall \beta\in \mathbb{R}, n\in \mathbb{N},\\{}0\le\beta\le\frac{3}{4} \land 4^{20}\le n\longrightarrow\\{}\operatorname{Summable}\left(i\mapsto\left\lvert \operatorname{sample}\left(\beta, \frac{2}{n}, \frac{i+1}{n}\right)\right\rvert\right) \land \operatorname{IntegrableOn}\left(s\mapsto\operatorname{sample}\left(\beta, 0, s\right), (0,\infty)\right) \land\\{}\left\lvert \int_{(0,\infty)}\operatorname{sample}\left(\beta, 0, s\right)\,ds-\frac{1}{n}\sum_{i=0}^{\infty}\operatorname{sample}\left(\beta, \frac{2}{n}, \frac{i+1}{n}\right)\right\rvert\le1232\cdot n^{-\frac{1}{80}}\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Patterns/Separable/OccupiedMellinFloors.global_mesh_rate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All ratios and variable powers are real; the threshold is the natural number four to the twentieth. The integral is unshifted and uses Lebesgue measure on the positive half-line. The mesh starts at index one and uses the exact shift 2/n.

Write q for n to the power minus one twentieth. The two integer cutoffs are the natural floors of n times q and n divided by q. Floor inequalities bound the first normalized cutoff between q/2 and q, and the far cutoff after subtracting one by q inverse divided by two from below. The resulting mesh budget has each term bounded by a multiple of n to the power minus one eightieth.

## References

- Truth anchor: `D5/S1/Words/Patterns/Separable/OccupiedMellinFloors.global_mesh_rate`
- Dependency: [D5/S1/Words/Patterns/Separable/OccupiedMellinGlobalMesh](OccupiedMellinGlobalMesh.md)
