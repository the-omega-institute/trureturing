# Observation-Depth Stop-Loss Profile

## Abstract

Finite stop-loss depth profiles satisfy sharp positivity, cutoff, saturation, and linear-regime bounds.

**Definition 1.1 (Active pole height).**

Lean statement: `D5/S3/Zeros/ObservationDepthStopLoss.activePoleHeight`

*Formalization.* `D5/S3/Zeros/ObservationDepthStopLoss.activePoleHeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The positive part of delta minus the observation depth.

**Definition 1.2 (Horizontal tail count).**

Lean statement: `D5/S3/Zeros/ObservationDepthStopLoss.horizontalTailCount`

*Formalization.* `D5/S3/Zeros/ObservationDepthStopLoss.horizontalTailCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The multiplicity sum over poles whose distance exceeds the observation depth.

**Definition 1.3 (Remaining depth).**

Lean statement: `D5/S3/Zeros/ObservationDepthStopLoss.remainingDepth`

*Formalization.* `D5/S3/Zeros/ObservationDepthStopLoss.remainingDepth` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The multiplicity-weighted sum of active pole heights.

**Definition 1.4 (Double-depth decay).**

Lean statement: `D5/S3/Zeros/ObservationDepthStopLoss.doubleDepthDecay`

*Formalization.* `D5/S3/Zeros/ObservationDepthStopLoss.doubleDepthDecay` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The multiplicity-weighted sum of the increment capped by each active height.

**Theorem 1.5 (Sharp finite stop-loss bounds).**

$$\begin{aligned}\forall j, \delta_{j} > 0, y \geq 0 \Rightarrow\\N\left(0\right) = \sum_{j} m_{j} \land R\left(0\right) = \sum_{j} m_{j} \cdot \delta_{j} \land A\left(\omega, 0\right) = 0,\\0 \leq R\left(\omega\right) \land 0 \leq A\left(\omega, y\right) \leq R\left(\omega\right),\\A\left(\omega, y\right) \leq y \cdot \sum_{j} m_{j},\\(\forall j, \delta_{j} \leq \omega) \Rightarrow R\left(\omega\right) = 0 \land A\left(\omega, y\right) = 0,\\(\forall j, h\left(j, \omega\right) \leq y) \Rightarrow A\left(\omega, y\right) = R\left(\omega\right),\\(\forall j, y \leq h\left(j, \omega\right)) \Rightarrow A\left(\omega, y\right) = y \cdot \sum_{j} m_{j}.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/ObservationDepthStopLoss.observation_depth_stop_loss` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source atom ends immediately after introducing the four displayed quantities. The formal statement therefore records their finite-sum well-formedness without importing the next atom's transport laws.

Positive transverse distances give the initial tail and remaining-depth values. A nonnegative increment makes the decay nonnegative and bounds it by both remaining depth and increment times total multiplicity.

Complete cutoff, complete saturation, and the linear regime provide exact equality cases for every displayed inequality.

**Theorem 1.6 (Nonpositive distance breaks initial activity).**

$$N\left(0\right) = 0 \neq 1 = \sum_{j} m_{j}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/ObservationDepthStopLoss.nonpositive_distance_breaks_initial_activity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

One pole at distance zero with multiplicity one has zero active tail count at depth zero, rather than total multiplicity one.

**Theorem 1.7 (Negative depth breaks decay nonnegativity).**

$$A\left(0, -1\right) = -1 < 0.$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/ObservationDepthStopLoss.negative_depth_breaks_decay_nonnegativity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For one unit-distance pole of unit multiplicity, increment minus one gives double-depth decay minus one. Thus y must be nonnegative.

## References

- Truth anchor: `D5/S3/Zeros/ObservationDepthStopLoss.activePoleHeight`
- Truth anchor: `D5/S3/Zeros/ObservationDepthStopLoss.doubleDepthDecay`
- Truth anchor: `D5/S3/Zeros/ObservationDepthStopLoss.horizontalTailCount`
- Truth anchor: `D5/S3/Zeros/ObservationDepthStopLoss.negative_depth_breaks_decay_nonnegativity`
- Truth anchor: `D5/S3/Zeros/ObservationDepthStopLoss.nonpositive_distance_breaks_initial_activity`
- Truth anchor: `D5/S3/Zeros/ObservationDepthStopLoss.observation_depth_stop_loss`
- Truth anchor: `D5/S3/Zeros/ObservationDepthStopLoss.remainingDepth`
