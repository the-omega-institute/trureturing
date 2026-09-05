# Parity Polarization Holomorphy Criterion

## Abstract

Holomorphy of the doubled parity quotient characterizes the zeta zero line.

**Theorem 1.1 (The parity quotient is holomorphic exactly on the zero-line criterion).**

$$\begin{aligned}\operatorname{let} observationHalfPlane: \operatorname{Set}\left(\mathbb{C}\right) := \{s\in \mathbb{C} \mid \frac{1}{2} < \Re(s)\},\\\operatorname{let} parityPolarization: \mathbb{C} \to \mathbb{C} := (s: \mathbb{C} \mapsto \frac{\operatorname{riemannZeta}\left(2 \times s\right)}{\operatorname{riemannZeta}\left(s\right)^{2}}),\\\operatorname{let} mobiusObserver: \mathbb{C} \to \mathbb{C} := (s: \mathbb{C} \mapsto \operatorname{riemannZeta}\left(s\right)^{-1}),\\\operatorname{let} hasHolomorphicPolarization: \operatorname{Prop} := \forall s \in \mathbb{C},\; \operatorname{Mem}\left(s, observationHalfPlane\right) \Rightarrow \left(\exists germ \in \mathbb{C} \to \mathbb{C},\; \operatorname{AnalyticAt}\left(\mathbb{C}, germ, s\right) \land \operatorname{EventuallyEq}\left(\operatorname{nhdsWithin}\left(s, \mathbb{C} \setminus \{s\}\right), parityPolarization, germ\right)\right),\\\left(\operatorname{RiemannHypothesis}\left(\right) \Leftrightarrow hasHolomorphicPolarization\right) \land \left(\forall rho \in \mathbb{C}, multiplicity \in \mathbb{N},\; \left(\operatorname{riemannZeta}\left(rho\right) = 0 \land \operatorname{zeroMult}\left(rho\right) = multiplicity\right) \Rightarrow \operatorname{meromorphicOrderAt}\left(mobiusObserver, rho\right) = -multiplicity\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaObservation/ParityPolarizationHolomorphyCriterion.parity_polarization_holomorphy_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The observation region is the open half-plane to the right of one half. Holomorphy means that the literal quotient agrees on each punctured neighborhood with a local analytic germ, so the value assigned at an apparent singularity cannot hide a pole.

Under the Riemann hypothesis, the zeta residue factorization supplies the required analytic germs, including at one. Conversely, an off-line zero makes the denominator contribute twice its positive multiplicity while the doubled numerator is nonzero, contradicting analyticity of the germ.

The reciprocal zeta observer has meromorphic order equal to the negative of zeroMult at every zero. This is stronger than limiting the conclusion to off-line zeros and introduces no unused location premise.

## References

- Truth anchor: `D5/S3/Analytic/ZetaObservation/ParityPolarizationHolomorphyCriterion.parity_polarization_holomorphy_criterion`
- Dependency: [D5/S3/Weil/ZetaBridge/RightHalfStripRiemannReduction](../../Weil/ZetaBridge/RightHalfStripRiemannReduction.md)
