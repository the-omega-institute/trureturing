# Liouville Parity Holomorphy Criterion

## Abstract

Holomorphy of the Liouville parity quotient characterizes the zeta zero line.

**Theorem 1.1 (The Liouville parity quotient is holomorphic exactly on the zero-line criterion).**

$$\begin{aligned}\operatorname{let} observationHalfPlane: \operatorname{Set}\left(\mathbb{C}\right) := \{s\in \mathbb{C} \mid \frac{1}{2} < \Re(s)\},\\\operatorname{let} liouvilleParity: \mathbb{C} \to \mathbb{C} := (s: \mathbb{C} \mapsto \frac{\operatorname{riemannZeta}\left(2 \times s\right)}{\operatorname{riemannZeta}\left(s\right)}),\\\operatorname{let} hasHolomorphicParity: \operatorname{Prop} := \forall s \in \mathbb{C},\; \operatorname{Mem}\left(s, observationHalfPlane\right) \Rightarrow \left(\exists germ \in \mathbb{C} \to \mathbb{C},\; \operatorname{AnalyticAt}\left(\mathbb{C}, germ, s\right) \land \operatorname{EventuallyEq}\left(\operatorname{nhdsWithin}\left(s, \mathbb{C} \setminus \{s\}\right), liouvilleParity, germ\right)\right),\\\operatorname{RiemannHypothesis}\left(\right) \Leftrightarrow hasHolomorphicParity.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaObservation/LiouvilleParityHolomorphyCriterion.liouville_parity_holomorphy_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The observation region is the open half-plane to the right of one half. Holomorphy means that the literal quotient agrees on each punctured neighborhood with a local analytic germ, so the value assigned at an apparent singularity cannot hide a pole.

The Riemann hypothesis removes denominator zeros from the open half-plane, while the zeta residue factorization supplies an analytic germ at one. Conversely, an off-line zero contributes positive denominator multiplicity while the doubled numerator is nonzero, contradicting analyticity of the local germ.

## References

- Truth anchor: `D5/S3/Analytic/ZetaObservation/LiouvilleParityHolomorphyCriterion.liouville_parity_holomorphy_criterion`
- Dependency: [D5/S3/Weil/ZetaBridge/RightHalfStripRiemannReduction](../../Weil/ZetaBridge/RightHalfStripRiemannReduction.md)
