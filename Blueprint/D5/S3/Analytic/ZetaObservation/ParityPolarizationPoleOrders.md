# Parity Polarization Pole Orders

## Abstract

The parity quotient criterion carries the exact orders of all three observers.

**Theorem 1.1 (Parity holomorphy and the three observer pole orders).**

$$\begin{aligned}\operatorname{let} observationHalfPlane: \operatorname{Set}\left(\mathbb{C}\right) := \{s\in \mathbb{C} \mid \frac{1}{2} < \Re(s)\},\\\operatorname{let} parityPolarization: \mathbb{C} \to \mathbb{C} := (s: \mathbb{C} \mapsto \frac{\operatorname{riemannZeta}\left(2 \times s\right)}{\operatorname{riemannZeta}\left(s\right)^{2}}),\\\operatorname{let} mobiusObserver: \mathbb{C} \to \mathbb{C} := (s: \mathbb{C} \mapsto \operatorname{riemannZeta}\left(s\right)^{-1}),\\\operatorname{let} liouvilleObserver: \mathbb{C} \to \mathbb{C} := (s: \mathbb{C} \mapsto \frac{\operatorname{riemannZeta}\left(2 \times s\right)}{\operatorname{riemannZeta}\left(s\right)}),\\\operatorname{let} hasHolomorphicPolarization: \operatorname{Prop} := \forall s \in \mathbb{C},\; \operatorname{Mem}\left(s, observationHalfPlane\right) \Rightarrow \left(\exists germ \in \mathbb{C} \to \mathbb{C},\; \operatorname{AnalyticAt}\left(\mathbb{C}, germ, s\right) \land \operatorname{EventuallyEq}\left(\operatorname{nhdsWithin}\left(s, \mathbb{C} \setminus \{s\}\right), parityPolarization, germ\right)\right),\\\left(\operatorname{RiemannHypothesis}\left(\right) \Leftrightarrow hasHolomorphicPolarization\right) \land \left(\forall rho \in \mathbb{C}, multiplicity \in \mathbb{N},\; \left(\operatorname{Mem}\left(rho, observationHalfPlane\right) \land \left(\operatorname{riemannZeta}\left(rho\right) = 0 \land \operatorname{zeroMult}\left(rho\right) = multiplicity\right)\right) \Rightarrow \left(\operatorname{meromorphicOrderAt}\left(mobiusObserver, rho\right) = -multiplicity \land \left(\operatorname{meromorphicOrderAt}\left(liouvilleObserver, rho\right) = -multiplicity \land \operatorname{meromorphicOrderAt}\left(parityPolarization, rho\right) = -2 \times multiplicity\right)\right)\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaObservation/ParityPolarizationPoleOrders.parity_polarization_holomorphy_and_pole_orders` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The normalized parity polarization is holomorphic throughout the open observation half-plane exactly when the Riemann hypothesis holds.

At a zeta zero in that half-plane, doubling moves the numerator into the zero-free half-plane. Meromorphic-order subtraction then gives the multiplicity orders for the reciprocal and Liouville observers and twice that order for the normalized polarization.

## References

- Truth anchor: `D5/S3/Analytic/ZetaObservation/ParityPolarizationPoleOrders.parity_polarization_holomorphy_and_pole_orders`
- Dependency: [D5/S3/Analytic/ZetaObservation/ParityPolarizationHolomorphyCriterion](ParityPolarizationHolomorphyCriterion.md)
