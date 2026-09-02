# Golden Robust First Detection

## Abstract

The first golden observation layer below a simple local defect has a uniform normalized energy floor.

**Theorem 1.1 (The first crossing retains golden-scale energy).**

$$\forall omega0 \in \mathbb{R}, delta \in \mathbb{R}, E \in \mathbb{R} \to \mathbb{R},\; \left(0 < omega0 \land \left(0 < delta \land \left(delta < omega0 \land \left(\forall omega \in \mathbb{R},\; 0 < omega \Rightarrow \left(omega < delta \Rightarrow E\left(omega\right) = \frac{omega}{delta}^{2}\right)\right)\right)\right)\right) \Rightarrow \left(\exists m \in \mathbb{N},\; omega0 \times {{\varphi^{-1}}^{2}}^{m} < delta \land \left(\left(\forall n \in \mathbb{N},\; n < m \Rightarrow delta \le omega0 \times {{\varphi^{-1}}^{2}}^{n}\right) \land \varphi^{-4} \le E\left(omega0 \times {{\varphi^{-1}}^{2}}^{m}\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MeasureSeparation/GoldenRobustFirstDetection.golden_robust_first_detection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a positive initial scale and a positive defect depth below it, the displayed golden schedule is the literal local layer construction from the Lean statement. Its least layer below the defect exists and all earlier layers remain at or above the defect.

The local single-defect law converts the minimal crossing estimate into the fourth inverse golden-ratio lower bound. The statement exposes the crossing, its firstness, and the energy bound together.

## References

- Truth anchor: `D5/S3/Observer/MeasureSeparation/GoldenRobustFirstDetection.golden_robust_first_detection`
