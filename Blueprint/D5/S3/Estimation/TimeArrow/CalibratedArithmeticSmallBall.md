# Calibrated arithmetic small-ball bounds

## Abstract

Integer lattice bands, moving centers, and hypergeometric arithmetic estimates share one calibrated small-ball framework. Classical Stirling, Poisson, Littlewood-Offord, and hypergeometric estimates are recorded in Library/Estimation; the balanced hypergeometric maximum-atom bound is literature-attested, while the arithmetic and native calibration contracts are repository-derived.

**Definition 1.1 (Finite event mass).**

Lean statement: `D5/S3/Estimation/TimeArrow/CalibratedArithmeticSmallBall.eventMass`

*Formalization.* `D5/S3/Estimation/TimeArrow/CalibratedArithmeticSmallBall.eventMass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mass of an integer event is the finite sum of its point masses.

**Definition 1.2 (Lattice band).**

Lean statement: `D5/S3/Estimation/TimeArrow/CalibratedArithmeticSmallBall.latticeBand`

*Formalization.* `D5/S3/Estimation/TimeArrow/CalibratedArithmeticSmallBall.latticeBand` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A lattice band keeps the integer arguments whose calibrated value lies within a fixed real radius of an integer target.

**Definition 1.3 (Arithmetic small-ball event).**

Lean statement: `D5/S3/Estimation/TimeArrow/CalibratedArithmeticSmallBall.arithmeticEvent`

*Formalization.* `D5/S3/Estimation/TimeArrow/CalibratedArithmeticSmallBall.arithmeticEvent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The central event is the union of the lattice bands indexed by the supplied integer targets.

**Theorem 1.4 (Central arithmetic mass bound).**

Lean statement: `D5/S3/Estimation/TimeArrow/CalibratedArithmeticSmallBall.arithmetic_central_mass_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/TimeArrow/CalibratedArithmeticSmallBall.arithmetic_central_mass_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A real-valued calibration on the integers and a pointwise mass cap bound the central event by the number of targets times the lattice width.

**Definition 1.5 (Integer targets in a real interval).**

Lean statement: `D5/S3/Estimation/TimeArrow/CalibratedArithmeticSmallBall.integerTargets`

*Formalization.* `D5/S3/Estimation/TimeArrow/CalibratedArithmeticSmallBall.integerTargets` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The integer targets are the closed integer interval between the ceiling of the lower endpoint and the floor of the upper endpoint.

**Theorem 1.6 (Moving-center small-ball estimate).**

Lean statement: `D5/S3/Estimation/TimeArrow/CalibratedArithmeticSmallBall.moving_center_small_ball`

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/TimeArrow/CalibratedArithmeticSmallBall.moving_center_small_ball` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A monotone approximation to a moving center, with lower and upper slope bounds and a tail outside the central interval, yields the displayed finite small-ball mass bound.

**Theorem 1.7 (Hypergeometric arithmetic bound).**

Lean statement: `D5/S3/Estimation/TimeArrow/CalibratedArithmeticSmallBall.hypergeometric_arithmetic_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/TimeArrow/CalibratedArithmeticSmallBall.hypergeometric_arithmetic_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The hypergeometric count kernel satisfies a moving-center arithmetic bound under balanced margins, scale, and slope hypotheses.

**Theorem 1.8 (Hypergeometric predicate bound).**

Lean statement: `D5/S3/Estimation/TimeArrow/CalibratedArithmeticSmallBall.hypergeometric_predicate_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/TimeArrow/CalibratedArithmeticSmallBall.hypergeometric_predicate_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An arbitrary predicate contained in the central lattice window is bounded by the same hypergeometric central estimate plus the kernel tail.

**Theorem 1.9 (Balanced hypergeometric atom bound).**

Lean statement: `D5/S3/Estimation/TimeArrow/CalibratedArithmeticSmallBall.hypergeometric_balanced_max_atom`

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/TimeArrow/CalibratedArithmeticSmallBall.hypergeometric_balanced_max_atom` (`✓ std3`). ∎

*Citation.* S. N. Lahiri, A. Chatterjee and T. Maiti (2007). *Normal approximation to the hypergeometric distribution in nonstandard cases and a sub-Gaussian Berry–Esseen theorem*. DOI: [10.1016/j.jspi.2007.03.033](https://doi.org/10.1016/j.jspi.2007.03.033). URL: <https://arxiv.org/abs/math/0602276v1>.

*Commentary.*

For a fixed balance parameter, one positive constant uniformly bounds every atom of every balanced hypergeometric table.

**Theorem 1.10 (Native anchored central feedback).**

Lean statement: `D5/S3/Estimation/TimeArrow/CalibratedArithmeticSmallBall.native_anchored_central_feedback`

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/TimeArrow/CalibratedArithmeticSmallBall.native_anchored_central_feedback` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The native anchored experiment supplies a common calibrated central feedback bound for the original and conditioned environments.

**Theorem 1.11 (Signal four reference ratios).**

Lean statement: `D5/S3/Estimation/TimeArrow/CalibratedArithmeticSmallBall.signal_four_reference_ratios`

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/TimeArrow/CalibratedArithmeticSmallBall.signal_four_reference_ratios` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all natural M,q,L, support S : Support M q, real r,kappa with kappa>0, r>0, r<=1-kappa and compensation M q r<=1-kappa, L>=1, i : Fin M with i in S.val, and natural k,l, assume both L*(1+r)/(2*(k+1)) and L*(1-r)/(2*(l+1)) lie in [15/16,1]. For every j : Fin 4, rowReference S r L i at the j-th cell of [(k,l),(k+1,l),(k,l+1),(k+1,l+1)] lies between 7/8 and 9/8 times rowReference S r L i (k,l). Counts in the successor factors are cast to reals.

**Theorem 1.12 (Floored signal four reference ratios).**

Lean statement: `D5/S3/Estimation/TimeArrow/CalibratedArithmeticSmallBall.floored_signal_four_reference_ratios`

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/TimeArrow/CalibratedArithmeticSmallBall.floored_signal_four_reference_ratios` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original floor and its complementary count give the displayed four-cell reference-mass comparisons.

**Theorem 1.13 (Background reference cell ratio).**

Lean statement: `D5/S3/Estimation/TimeArrow/CalibratedArithmeticSmallBall.background_reference_cell_ratio`

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/TimeArrow/CalibratedArithmeticSmallBall.background_reference_cell_ratio` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At the same count cell, the background reference mass has its exact ratio to the signal reference mass.

**Definition 1.14 (Original window).**

Lean statement: `D5/S3/Estimation/TimeArrow/CalibratedArithmeticSmallBall.originalWindow`

*Formalization.* `D5/S3/Estimation/TimeArrow/CalibratedArithmeticSmallBall.originalWindow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The selection window uses the original compensated score with its complete left-open and right-closed bounds.

**Definition 1.15 (Original group posterior mean).**

Lean statement: `D5/S3/Estimation/TimeArrow/CalibratedArithmeticSmallBall.originalGroupPosteriorMean`

*Formalization.* `D5/S3/Estimation/TimeArrow/CalibratedArithmeticSmallBall.originalGroupPosteriorMean` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The group mean sums the complete support posterior over all rows in the same original score group.

## References

- Truth anchor: `D5/S3/Estimation/TimeArrow/CalibratedArithmeticSmallBall.arithmeticEvent`
- Truth anchor: `D5/S3/Estimation/TimeArrow/CalibratedArithmeticSmallBall.arithmetic_central_mass_bound`
- Truth anchor: `D5/S3/Estimation/TimeArrow/CalibratedArithmeticSmallBall.background_reference_cell_ratio`
- Truth anchor: `D5/S3/Estimation/TimeArrow/CalibratedArithmeticSmallBall.eventMass`
- Truth anchor: `D5/S3/Estimation/TimeArrow/CalibratedArithmeticSmallBall.floored_signal_four_reference_ratios`
- Truth anchor: `D5/S3/Estimation/TimeArrow/CalibratedArithmeticSmallBall.hypergeometric_arithmetic_bound`
- Truth anchor: `D5/S3/Estimation/TimeArrow/CalibratedArithmeticSmallBall.hypergeometric_balanced_max_atom`
- Truth anchor: `D5/S3/Estimation/TimeArrow/CalibratedArithmeticSmallBall.hypergeometric_predicate_bound`
- Truth anchor: `D5/S3/Estimation/TimeArrow/CalibratedArithmeticSmallBall.integerTargets`
- Truth anchor: `D5/S3/Estimation/TimeArrow/CalibratedArithmeticSmallBall.latticeBand`
- Truth anchor: `D5/S3/Estimation/TimeArrow/CalibratedArithmeticSmallBall.moving_center_small_ball`
- Truth anchor: `D5/S3/Estimation/TimeArrow/CalibratedArithmeticSmallBall.native_anchored_central_feedback`
- Truth anchor: `D5/S3/Estimation/TimeArrow/CalibratedArithmeticSmallBall.originalGroupPosteriorMean`
- Truth anchor: `D5/S3/Estimation/TimeArrow/CalibratedArithmeticSmallBall.originalWindow`
- Truth anchor: `D5/S3/Estimation/TimeArrow/CalibratedArithmeticSmallBall.signal_four_reference_ratios`
- Dependency: [D5/S3/DivergenceSupport/LogSumInequality](../../DivergenceSupport/LogSumInequality.md)
- Dependency: [D5/S3/Estimation/TimeArrow/NativeRectangleEnvironment](NativeRectangleEnvironment.md)
- Dependency: [D5/S3/Estimation/TimeArrow/NativeSharedRootFeedback](NativeSharedRootFeedback.md)
- Dependency: [D5/S3/Estimation/TimeArrow/NativeSignalConditionalFiber](NativeSignalConditionalFiber.md)
- Dependency: [D5/S3/Estimation/TimeArrow/NativeWeightedRowBudgets](NativeWeightedRowBudgets.md)
