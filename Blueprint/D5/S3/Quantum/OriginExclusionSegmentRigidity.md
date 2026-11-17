# XI origin exclusion: recentered quadratic constraint

## Abstract

XI origin exclusion: recentered quadratic constraint

**Lemma 1.1 (Recentered quadratic constraint).**

$$\forall t \in \mathbb{R},\; \forall b \in \mathbb{R},\; b^{2} \le t \cdot \left(1 - t\right) \Leftrightarrow \left(t - \frac{1}{2}\right)^{2} + b^{2} \le \frac{1}{2}^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/OriginExclusionSegmentRigidity.b_constraint_recenter` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The identity rewrites the XI auxiliary quadratic constraint as a translated closed-ball inequality. It is the algebraic step used before compactness and pure-locus analysis; the higher-dimensional effect and extremal-point claims remain outside this declaration.

## References

- Truth anchor: `D5/S3/Quantum/OriginExclusionSegmentRigidity.b_constraint_recenter`
