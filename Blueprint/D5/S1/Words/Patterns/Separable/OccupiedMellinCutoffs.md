# Cutoffs of the paired Mellin sample

## Abstract

Absolute integral bounds control the intervals omitted from the regular Mellin quadrature.

**Theorem 1.1 (The origin, the center, and the far tail).**

$$\begin{gathered}(\forall \beta,a,\delta\in \mathbb{R},\quad0\le\beta\le\frac{3}{4} \land 0\le a \land 0\le\delta\le\frac{1}{2}\longrightarrow\\{}\quad \operatorname{IntervalIntegrable}\left(F_{\beta,a}, 0, \delta\right) \land \int_{0}^{\delta}F_{\beta,a}(s)\,ds\le\frac{64}{3}\cdot \delta^{\frac{3}{2}}) \land\\{}(\forall \beta,\delta\in \mathbb{R},\quad0\le\beta\le\frac{3}{4} \land 0\le\delta\le\frac{1}{2}\longrightarrow\\{}\quad \operatorname{IntervalIntegrable}\left(F_{\beta,0}, 1-\delta, 1+\delta\right) \land \int_{1-\delta}^{1+\delta}F_{\beta,0}(s)\,ds\le32\cdot \delta^{\frac{1}{4}}) \land\\{}(\forall \beta,a,R\in \mathbb{R},\quad0\le\beta \land 0\le a \land 2\le R\longrightarrow\\{}\quad \operatorname{IntegrableOn}\left(F_{\beta,a}, (R,\infty)\right) \land \int_{(R,\infty)}F_{\beta,a}(s)\,ds\le4\cdot R^{-\frac{1}{2}}) \land\\{}(\forall \beta,a,s\in \mathbb{R},\quad0\le\beta\le\frac{3}{4} \land 0\le a \land 0<s\le\frac{1}{2}\longrightarrow\\{}\quad F_{\beta,a}(s)\le32\cdot s^{\frac{1}{2}}) \land\\{}(\forall \beta,a,s\in \mathbb{R},\quad0\le\beta \land 0\le a \land 2\le s\longrightarrow\\{}\quad F_{\beta,a}(s)\le2\cdot s^{-\frac{3}{2}})\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Patterns/Separable/OccupiedMellinCutoffs.mellin_cutoff_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write F with subscripts beta and a for the absolute value of the paired sample at exponent beta and shift a. Integrability and all integrals are relative to Lebesgue measure. The center bound uses precisely the unshifted sample; the origin and tail allow any nonnegative shift.

Near the origin, the first differences cancel and a uniform second-derivative estimate bounds the symmetric numerator by a multiple of the square of the position. Near the center, the absolute numerator is at most the singular power, which can be integrated after reflecting the left half onto the right. Beyond two, all three profile values lie between zero and one. The pointwise bounds at the origin and in the far tail also apply to shifted lattice samples.

## References

- Truth anchor: `D5/S1/Words/Patterns/Separable/OccupiedMellinCutoffs.mellin_cutoff_bounds`
- Dependency: [D5/S1/Words/Patterns/Separable/OccupiedMellinInterior](OccupiedMellinInterior.md)
