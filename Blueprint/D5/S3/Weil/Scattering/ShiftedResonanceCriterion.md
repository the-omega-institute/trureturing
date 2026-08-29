# Shifted Resonance Horizontal Criterion

## Abstract

The shifted zero points lie on one horizontal line exactly when every zero has critical real part.

**Theorem 1.1 (Shifted resonances characterize the critical line).**

$$\forall Z: \operatorname{ZeroData}, \forall omega: \mathbb{R}, \frac{1}{2} \le omega \Rightarrow \left(\left(\forall n \in \mathbb {N},\; \Re(Z.zero(n)) = \operatorname{criticalAbscissa}\left(\right)\right) \Leftrightarrow \operatorname{rangeIntersectUpper}\left(\operatorname{resonance}\left(omega\right)\right) \subseteq \operatorname{horizontalLine}\left(omega\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Scattering/ShiftedResonanceCriterion.horizontal_resonance_line_iff_critical_line` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For supplied ZeroData and a real shift omega at least one half, the public resonance map sends index n to the complex point minus Im(Z.zero n) plus i times omega plus Re(Z.zero n) minus criticalAbscissa. The displayed inclusion is the range of this map intersected with the upper half-plane contained in the horizontal line of height omega.

Every enumerated zero is in the open strip, so the shifted points are automatically in the upper half-plane for the stated shift. The two directions then reduce the line condition to equality of each zero real part with the critical abscissa.

## References

- Truth anchor: `D5/S3/Weil/Scattering/ShiftedResonanceCriterion.horizontal_resonance_line_iff_critical_line`
