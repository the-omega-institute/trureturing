# Transverse Stop-Loss Tomography

## Abstract

Finite transverse stop-loss profiles satisfy exact transport identities and recover their weighted divisor from slope jumps.

**Definition 1.1 (Real tail count).**

Lean statement: `D5/S3/Zeros/TransverseStopLossTomography.tailCount`

*Formalization.* `D5/S3/Zeros/TransverseStopLossTomography.tailCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The real-valued sum of multiplicities whose transverse distance exceeds the observation depth.

**Definition 1.2 (Closed tail count).**

Lean statement: `D5/S3/Zeros/TransverseStopLossTomography.closedTailCount`

*Formalization.* `D5/S3/Zeros/TransverseStopLossTomography.closedTailCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The tail count retaining the multiplicity exactly at the observation depth.

**Definition 1.3 (Divisor multiplicity).**

Lean statement: `D5/S3/Zeros/TransverseStopLossTomography.divisorMultiplicity`

*Formalization.* `D5/S3/Zeros/TransverseStopLossTomography.divisorMultiplicity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The total multiplicity carried by one transverse distance.

**Definition 1.4 (Observation area).**

Lean statement: `D5/S3/Zeros/TransverseStopLossTomography.observationArea`

*Formalization.* `D5/S3/Zeros/TransverseStopLossTomography.observationArea` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The remaining-depth loss between omega and omega plus y.

**Theorem 1.5 (Finite transverse stop-loss tomography).**

$$\begin{aligned}\forall J, \operatorname{FiniteType}\left(J\right), \delta: J \to \mathbb{R}, m: J \to \mathbb{N},\\\forall \omega, y: \mathbb{R}, y \geq 0,\\(\forall j, \omega \neq \delta_{j} \land \omega + y \neq \delta_{j}) \Rightarrow\\N\left(u\right) = \sum_{j} m_{j} \cdot \operatorname{indicator}\left(u < \delta_{j}\right), R\left(x\right) = \sum_{j} m_{j} \cdot \operatorname{max}\left(\delta_{j} - x, 0\right), A\left(\omega, y\right) = R\left(\omega\right) - R\left(\omega + y\right),\\R\left(\omega\right) = \operatorname{setIntegral}\left(u, \operatorname{Ioi}\left(\omega\right), N\left(u\right)\right),\\A\left(\omega, y\right) = R\left(\omega\right) - R\left(\omega + y\right) = \operatorname{intervalIntegral}\left(u, \omega, \omega + y, N\left(u\right)\right),\\\operatorname{doubleDepthDecay}\left(\omega, y\right) = A\left(\omega, y\right),\\\left(partial_{y}\right)\left(A\left(\omega, y\right)\right) = N\left(\omega + y\right),\\\left(partial_{\omega}\right)\left(A\left(\omega, y\right)\right) = N\left(\omega + y\right) - N\left(\omega\right),\\(partial_{\omega} - partial_{y}) A\left(\omega, y\right) = -N\left(\omega\right),\\\forall x: \mathbb{R}, \operatorname{rightSlope}\left(R, x\right) - \operatorname{leftSlope}\left(R, x\right) = \sum_{\delta_{j} = x} m_{j}.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/TransverseStopLossTomography.transverse_stop_loss_tomography` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source's profile is formalized for an arbitrary finite family of transverse distances with natural multiplicities. No positivity assumption on the distances is needed for the transport laws.

The tail-count integral is evaluated termwise as the volume of a bounded open interval. Subtracting the two tail integrals gives the swept interval identity, and ordinary derivatives are taken only when both endpoints avoid the finite jump set.

The distributional second-derivative formula is represented without a choice of test-function convention: the right slope minus the left slope at every depth is exactly the total divisor multiplicity there. Thus the complete finite transverse divisor is recovered.

## References

- Truth anchor: `D5/S3/Zeros/TransverseStopLossTomography.closedTailCount`
- Truth anchor: `D5/S3/Zeros/TransverseStopLossTomography.divisorMultiplicity`
- Truth anchor: `D5/S3/Zeros/TransverseStopLossTomography.observationArea`
- Truth anchor: `D5/S3/Zeros/TransverseStopLossTomography.tailCount`
- Truth anchor: `D5/S3/Zeros/TransverseStopLossTomography.transverse_stop_loss_tomography`
- Dependency: [D5/S3/Zeros/ObservationDepthStopLoss](ObservationDepthStopLoss.md)
