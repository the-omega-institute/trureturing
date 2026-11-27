# Discrete origin and far tails

## Abstract

The paired shifted Mellin mesh has controlled absolute mass at both integer ends.

**Theorem 1.1 (Two absolute bounds with exact mesh indices).**

$$\begin{gathered}(\forall \beta,a\in \mathbb{R}, n,K\in \mathbb{N},\quad0\le\beta\le\frac{3}{4} \land 0\le a \land 0<n \land \frac{K}{n}\le\frac{1}{2}\longrightarrow\\{}\quad \frac{1}{n}\sum_{0\le i<K}\left\lvert \operatorname{sample}\left(\beta, a, \frac{i+1}{n}\right)\right\rvert\le32\cdot \left(\frac{K}{n}\right)^{\frac{3}{2}}) \land\\{}(\forall \beta,a\in \mathbb{R}, n,M\in \mathbb{N},\quad0\le\beta \land 0\le a \land 0<n \land 2\le\frac{M}{n}\longrightarrow\\{}\quad \operatorname{Summable}\left(i\mapsto\left\lvert \operatorname{sample}\left(\beta, a, \frac{M+i+1}{n}\right)\right\rvert\right) \land \frac{1}{n}\sum_{i=0}^{\infty}\left\lvert \operatorname{sample}\left(\beta, a, \frac{M+i+1}{n}\right)\right\rvert\le4\cdot \left(\frac{M}{n}\right)^{-\frac{1}{2}})\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Patterns/Separable/OccupiedMellinDiscreteTails.discrete_mellin_tail_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The origin sum contains the points from 1/n through K/n and is empty for K equal to zero. The far sequence starts at (M+1)/n, strictly above M/n. Ratios are real and both estimates allow any nonnegative shift.

For the origin prefix the square-root pointwise bound can be evaluated at the last point and multiplied by the number of terms. For the far tail the summable power majorant decreases; comparison of its right-endpoint sum to its integral gives the displayed bound. No estimate at the central sample is used.

## References

- Truth anchor: `D5/S1/Words/Patterns/Separable/OccupiedMellinDiscreteTails.discrete_mellin_tail_bounds`
- Dependency: [D5/S1/Words/Patterns/Separable/OccupiedMellinCutoffs](OccupiedMellinCutoffs.md)
