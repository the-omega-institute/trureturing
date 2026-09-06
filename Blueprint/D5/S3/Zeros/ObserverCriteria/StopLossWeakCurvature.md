# Stop-Loss Weak Curvature

## Abstract

The weak second derivative of a finite stop-loss profile is its weighted atomic divisor; tail integrals and depth derivatives describe transport.

**Theorem 1.1 (Weak curvature of one kink).**

$$\begin{aligned}\forall \delta: \mathbb{R}, \varphi: \mathbb{R} \to \mathbb{R},\\\operatorname{ContDiff}\left(\mathbb{R}, 2, \varphi\right) \land \operatorname{HasCompactSupport}\left(\varphi\right) \Rightarrow\\\int_{x \in \mathbb{R}} \operatorname{activePoleHeight}\left(\delta, x\right) \cdot \operatorname{deriv}\left(\operatorname{deriv}\left(\varphi\right)\right)\left(x\right) dx = \varphi\left(\delta\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/ObserverCriteria/StopLossWeakCurvature.active_pole_height_weak_curvature` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The primitive is the product of distance minus position with the first test derivative, plus the test itself. Its derivative cancels the first-derivative terms. Restricting the kink to its lower half-line and applying compact-support FTC leaves the test value at the pole.

**Theorem 1.2 (Weak curvature of the finite defect product).**

$$\begin{aligned}\forall I: \operatorname{Type}, [\operatorname{Fintype}\left(I\right)], \delta: I \to \mathbb{R}, m: I \to \mathbb{N},\\\forall \varphi: \mathbb{R} \to \mathbb{R}, \operatorname{ContDiff}\left(\mathbb{R}, 2, \varphi\right) \land \operatorname{HasCompactSupport}\left(\varphi\right) \Rightarrow\\\int_{x \in \mathbb{R}} \operatorname{remainingDepth}\left(\delta, m, x\right) \cdot \operatorname{deriv}\left(\operatorname{deriv}\left(\varphi\right)\right)\left(x\right) dx = \sum_{j: I} (m\left(j\right): \mathbb{R}) \cdot \varphi\left(\delta\left(j\right)\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/ObserverCriteria/StopLossWeakCurvature.remaining_depth_weak_curvature` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This finite-sum companion consumes the single-kink theorem. Compact support makes every weighted integrand integrable, so integral linearity gives the atomic evaluation sum for arbitrary C2 tests.

**Theorem 1.3 (Tail transport and weak curvature).**

$$\begin{aligned}\forall I: \operatorname{Type}, [\operatorname{Fintype}\left(I\right)], \delta: I \to \mathbb{R}, m: I \to \mathbb{N},\\\operatorname{let} R: \mathbb{R} \to \mathbb{R} := \operatorname{remainingDepth}\left(\delta, m\right),\\N: \mathbb{R} \to \mathbb{R} := (x: \mathbb{R} \mapsto (\operatorname{horizontalTailCount}\left(\delta, m, x\right): \mathbb{R})),\\A: \mathbb{R} \to \mathbb{R} \to \mathbb{R} := \operatorname{doubleDepthDecay}\left(\delta, m\right) \operatorname{in}\\(\forall \omega: \mathbb{R}, \operatorname{R}\left(\omega\right) = \int_{x \in \operatorname{Ioi}\left(\omega\right)} \operatorname{N}\left(x\right) dx) \land\\(\forall \omega y: \mathbb{R}, 0 \leq y \Rightarrow \operatorname{A}\left(\omega, y\right) = \operatorname{R}\left(\omega\right) - \operatorname{R}\left(\omega + y\right)) \land\\(\forall \omega y: \mathbb{R}, 0 \leq y \Rightarrow \operatorname{A}\left(\omega, y\right) = \int_{\omega}^{\omega + y} \operatorname{N}\left(x\right) dx) \land\\(\forall \omega y: \mathbb{R}, 0 < y \Rightarrow (\forall j: I, \omega + y \neq \delta\left(j\right)) \Rightarrow \operatorname{deriv}\left((t: \mathbb{R} \mapsto \operatorname{A}\left(\omega, t\right))\right)\left(y\right) = \operatorname{N}\left(\omega + y\right)) \land\\(\forall \omega y: \mathbb{R}, 0 \leq y \Rightarrow (\forall j: I, \omega \neq \delta\left(j\right)) \Rightarrow (\forall j: I, \omega + y \neq \delta\left(j\right)) \Rightarrow \operatorname{deriv}\left((t: \mathbb{R} \mapsto \operatorname{A}\left(t, y\right))\right)\left(\omega\right) = \operatorname{N}\left(\omega + y\right) - \operatorname{N}\left(\omega\right)) \land\\(\forall \omega y: \mathbb{R}, 0 < y \Rightarrow (\forall j: I, \omega \neq \delta\left(j\right)) \Rightarrow (\forall j: I, \omega + y \neq \delta\left(j\right)) \Rightarrow \operatorname{deriv}\left((t: \mathbb{R} \mapsto \operatorname{A}\left(t, y\right))\right)\left(\omega\right) - \operatorname{deriv}\left((t: \mathbb{R} \mapsto \operatorname{A}\left(\omega, t\right))\right)\left(y\right) = -\operatorname{N}\left(\omega\right)) \land\\(\forall \varphi: \mathbb{R} \to \mathbb{R}, \operatorname{ContDiff}\left(\mathbb{R}, 2, \varphi\right) \land \operatorname{HasCompactSupport}\left(\varphi\right) \Rightarrow \int_{x \in \mathbb{R}} \operatorname{R}\left(x\right) \cdot \operatorname{deriv}\left(\operatorname{deriv}\left(\varphi\right)\right)\left(x\right) dx = \sum_{j: I} (m\left(j\right): \mathbb{R}) \cdot \varphi\left(\delta\left(j\right)\right))\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/ObserverCriteria/StopLossWeakCurvature.stop_loss_transport_and_weak_curvature` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed local notation expands the canonical ObservationDepthStopLoss functions. Natural tail counts and multiplicities are cast to real numbers when integrated.

Source provenance: the observation-layer transport theorem in the observer-adelic-completion-constant-theory input. Its seven displayed identities are public here. Positive pole distances are not needed. This companion consumes the finite weak-curvature theorem. Recovery of arbitrary measures from distributions remains a separate prerequisite and is not a conclusion.

## References

- Truth anchor: `D5/S3/Zeros/ObserverCriteria/StopLossWeakCurvature.active_pole_height_weak_curvature`
- Truth anchor: `D5/S3/Zeros/ObserverCriteria/StopLossWeakCurvature.remaining_depth_weak_curvature`
- Truth anchor: `D5/S3/Zeros/ObserverCriteria/StopLossWeakCurvature.stop_loss_transport_and_weak_curvature`
- Dependency: [D5/S3/Zeros/ObservationDepthStopLoss](../ObservationDepthStopLoss.md)
