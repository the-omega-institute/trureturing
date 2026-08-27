# Pointwise and Probability Knowledge Separation

## Abstract

Pointwise fiber knowledge implies a.e. knowledge, but not conversely.

**Definition 1.1 (Pointwise sufficiency).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/PointwiseAlmostEverywhereSeparation.PointwiseSufficient`

*Formalization.* `D5/S3/Observer/ProbabilisticClosure/PointwiseAlmostEverywhereSeparation.PointwiseSufficient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A target is pointwise sufficient when it is constant on every fiber of the readout, with no exceptional state.

**Definition 1.2 (Almost-everywhere sufficiency).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/PointwiseAlmostEverywhereSeparation.AlmostEverywhereSufficient`

*Formalization.* `D5/S3/Observer/ProbabilisticClosure/PointwiseAlmostEverywhereSeparation.AlmostEverywhereSufficient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A target is almost-everywhere sufficient when some factor through the readout agrees with it outside a null set.

**Theorem 1.3 (Pointwise sufficiency implies almost-everywhere sufficiency).**

$$Nonempty(Y), mu: Measure(X), q: X \to Q, T: X \to Y,\\{}PointwiseSufficient(q, T) \Rightarrow AlmostEverywhereSufficient(mu, q, T).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/PointwiseAlmostEverywhereSeparation.pointwise_sufficient_implies_almost_everywhere_sufficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The repository's answerability criterion constructs the exact factor under an anchor. The pinned general criterion weakens that premise to target nonemptiness, after which exact equality implies almost-everywhere equality under every measure.

**Theorem 1.4 (Target nonemptiness cannot be deleted in full generality).**

$$\exists q: Empty \to PUnit, T: Empty \to Empty, PointwiseSufficient(q, T) \land \neg AlmostEverywhereSufficient(0, q, T).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/PointwiseAlmostEverywhereSeparation.nonempty_target_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an empty state and target type but a one-point readout type, fiber constancy is vacuous while no factor from PUnit to Empty can exist.

**Theorem 1.5 (A supplied factor is sufficient under the zero measure).**

$$\forall q, T, Tbar, AlmostEverywhereSufficient(0, q, T).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/PointwiseAlmostEverywhereSeparation.zero_measure_almost_everywhere_sufficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All equalities hold almost everywhere for the zero measure. The factor is supplied explicitly so no hidden inhabitance premise is needed.

**Theorem 1.6 (Injective readouts are pointwise sufficient).**

$$Injective(q) \Rightarrow PointwiseSufficient(q, T).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/PointwiseAlmostEverywhereSeparation.injective_readout_pointwise_sufficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equality of injective readout values forces equality of states, so every target is constant on each singleton fiber. Identity readouts are included.

**Theorem 1.7 (Constant targets satisfy both notions).**

$$PointwiseSufficient(q, const(c)) \land AlmostEverywhereSufficient(mu, q, const(c)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/PointwiseAlmostEverywhereSeparation.constant_target_sufficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A constant target has no fiber defect and factors through every readout by the same constant, including constant and zero maps.

**Definition 1.8 (The counterexample measure).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/PointwiseAlmostEverywhereSeparation.nullPointMeasure`

*Formalization.* `D5/S3/Observer/ProbabilisticClosure/PointwiseAlmostEverywhereSeparation.nullPointMeasure` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The counterexample uses Lebesgue measure on R.

**Definition 1.9 (The counterexample readout).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/PointwiseAlmostEverywhereSeparation.nullPointReadout`

*Formalization.* `D5/S3/Observer/ProbabilisticClosure/PointwiseAlmostEverywhereSeparation.nullPointReadout` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The readout is constant from R to PUnit, so the whole state space is one fiber.

**Definition 1.10 (The counterexample target).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/PointwiseAlmostEverywhereSeparation.nullPointTarget`

*Formalization.* `D5/S3/Observer/ProbabilisticClosure/PointwiseAlmostEverywhereSeparation.nullPointTarget` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The Boolean target is true only at zero and false everywhere else.

**Definition 1.11 (The counterexample factor).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/PointwiseAlmostEverywhereSeparation.nullPointFactor`

*Formalization.* `D5/S3/Observer/ProbabilisticClosure/PointwiseAlmostEverywhereSeparation.nullPointFactor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The factor on PUnit is constantly false and differs from the target only at the origin.

**Theorem 1.12 (The counterexample measure is nonzero).**

$$nullPointMeasure \neq 0.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/PointwiseAlmostEverywhereSeparation.null_point_measure_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Lebesgue measure assigns infinite mass to the real line, excluding the vacuous zero-measure construction.

**Theorem 1.13 (The exceptional singleton is null).**

$$nullPointMeasure(\{0\}) = 0.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/PointwiseAlmostEverywhereSeparation.null_point_singleton_measure_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Mathlib's Lebesgue singleton theorem explicitly verifies that the origin has measure zero.

**Theorem 1.14 (One fiber contains two different target values).**

$$\exists x, y: \mathbb{R}, nullPointReadout(x) = nullPointReadout(y) \land nullPointTarget(x) \neq nullPointTarget(y).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/PointwiseAlmostEverywhereSeparation.null_point_same_fiber_different_target` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The points zero and one have the same PUnit readout, while the target is respectively true and false.

**Theorem 1.15 (The null-point target factors almost everywhere).**

$$AlmostEverywhereSufficient(nullPointMeasure, nullPointReadout, nullPointTarget).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/PointwiseAlmostEverywhereSeparation.null_point_almost_everywhere_sufficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Outside zero, the target equals the constantly false factor. The singleton calculation makes that exceptional set null.

**Theorem 1.16 (Almost-everywhere sufficiency is not pointwise sufficiency).**

$$AlmostEverywhereSufficient(nullPointMeasure, nullPointReadout, nullPointTarget) \land \neg PointwiseSufficient(nullPointReadout, nullPointTarget).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/PointwiseAlmostEverywhereSeparation.fpod_principle_118_1` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The explicit target factors through the constant readout almost everywhere but is not constant on that readout's sole fiber.

Strong lumpability instead characterizes pointwise descent of pushed-forward PMF rows. The conull-image theorem instead pulls measures back along injections; neither gives this strict comparison.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/PointwiseAlmostEverywhereSeparation.AlmostEverywhereSufficient`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/PointwiseAlmostEverywhereSeparation.PointwiseSufficient`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/PointwiseAlmostEverywhereSeparation.constant_target_sufficient`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/PointwiseAlmostEverywhereSeparation.fpod_principle_118_1`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/PointwiseAlmostEverywhereSeparation.injective_readout_pointwise_sufficient`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/PointwiseAlmostEverywhereSeparation.nonempty_target_is_necessary`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/PointwiseAlmostEverywhereSeparation.nullPointFactor`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/PointwiseAlmostEverywhereSeparation.nullPointMeasure`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/PointwiseAlmostEverywhereSeparation.nullPointReadout`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/PointwiseAlmostEverywhereSeparation.nullPointTarget`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/PointwiseAlmostEverywhereSeparation.null_point_almost_everywhere_sufficient`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/PointwiseAlmostEverywhereSeparation.null_point_measure_ne_zero`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/PointwiseAlmostEverywhereSeparation.null_point_same_fiber_different_target`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/PointwiseAlmostEverywhereSeparation.null_point_singleton_measure_zero`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/PointwiseAlmostEverywhereSeparation.pointwise_sufficient_implies_almost_everywhere_sufficient`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/PointwiseAlmostEverywhereSeparation.zero_measure_almost_everywhere_sufficient`
