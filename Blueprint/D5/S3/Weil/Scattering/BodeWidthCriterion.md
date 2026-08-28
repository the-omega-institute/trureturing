# Bode-Width Criterion

## Abstract

Finite mirror-paired widths produce the same critical-line, area, and curvature defect.

**Theorem 1.1 (Finite width, displacement, and damping defects coincide).**

$$\forall I: Type, \operatorname{Fintype}\left(I\right), delta: I\to\mathbb{R},\\{}{\forall i\in I, 0\leq\operatorname{delta}\left(i\right) \land \operatorname{delta}\left(i\right)\leq\frac{1}{2} \Rightarrow \\{}\operatorname{let} C:=\forall i\in I, \frac{1}{2}+\operatorname{delta}\left(i\right)=\frac{1}{2} \land \frac{1}{2}-\operatorname{delta}\left(i\right)=\frac{1}{2},\\{}\operatorname{let} W(y):=\sum_{i\in I}\max(\operatorname{delta}\left(i\right)-\left|y-\frac{1}{2}\right|, 0),\\{}\operatorname{let} A:=\int_{0}^{\infty}\operatorname{W}\left(y\right)\,dy,\\{}\operatorname{let} S:=\sum_{i\in I}{{\frac{1}{2}+\operatorname{delta}\left(i\right)-\frac{1}{2}}^{2}+{\frac{1}{2}-\operatorname{delta}\left(i\right)-\frac{1}{2}}^{2}},\\{}\operatorname{let} R(tau):=\sum_{i\in I}2 \cdot {\operatorname{cosh}\left(tau \cdot \operatorname{delta}\left(i\right)\right)-1},\\{}{C \Leftrightarrow \forall y\in \mathbb{R}, y>0 \Rightarrow \operatorname{W}\left(y\right)=0} \land {\forall y\in \mathbb{R}, y>0 \Rightarrow \operatorname{W}\left(y\right)=0 \Leftrightarrow A=0} \land {A=\frac{1}{2} \cdot S} \land {A=\frac{1}{2} \cdot \operatorname{deriv}\left(\operatorname{deriv}\left(R\right), 0\right)}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Scattering/BodeWidthCriterion.bode_width_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source finite window is encoded by nonnegative mirror-pair widths delta bounded by one half. Each pair contributes the displayed triangular pulse. Its integral is delta squared, while the two mirrored real-part displacements contribute twice delta squared. Twice differentiating the finite cosh partition gives the same sum.

## References

- Truth anchor: `D5/S3/Weil/Scattering/BodeWidthCriterion.bode_width_criterion`
