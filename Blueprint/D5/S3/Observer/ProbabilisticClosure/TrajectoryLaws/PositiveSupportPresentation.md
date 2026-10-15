# Positive stationary support and original cylinders

## Abstract

Positive stationary support and original cylinders

Positive theta is the subtype of original hidden states with strictly positive stationary mass. trim theta restricts lambda and both real matrices to that subtype; includePath inserts its hidden coordinates into the original hidden set and keeps every emitted integer coordinate exactly unchanged.

**Theorem 1.1 (Entrywise no11 after trimming).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/PositiveSupportPresentation.trim_no11`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/PositiveSupportPresentation.trim_no11` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original Presentation, the square of the trimmed one-symbol matrix is the zero matrix. This conclusion applies to every pair of retained states. It does not impose any such entrywise condition on discarded rows.

Stationarity and nonnegativity show that a positive-mass state cannot have a positive transition into a zero-mass state. Thus the retained set is closed under every positive symbol transition. Restriction preserves the stochastic row sums, normalization and stationarity. The weighted original no11 sum is a sum of nonnegative terms; each term starting from a retained state has a positive initial multiplier and hence a zero two-one product. Restricting its intermediate-state sum therefore gives the asserted zero matrix. All four parameter conditions and the original weighted no11 constraint are proved in the fields of trim theta.

**Theorem 1.2 (Law-preserving inclusion including ghost cylinders).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/PositiveSupportPresentation.include_cylinders`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/PositiveSupportPresentation.include_cylinders` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every probability J on the trimmed original PathSpace satisfying the trimmed HasOriginalCylinders equalities, the actual measurable inclusion pushforward J.map (includePath theta) satisfies every original HasOriginalCylinders equality. Starts range over all integers and lengths include zero. No unifilarity is assumed.

If all states of the prescribed original hidden path are retained, its inclusion preimage is exactly the corresponding trimmed cylinder and its numerical path weight is unchanged. If any prescribed state is discarded, that preimage is empty. A nonzero weighted original path would start with positive stationary mass and, by closedness at each transition, would remain positive at every hidden coordinate; this contradicts the discarded state. Hence the original numerical cylinder weight is zero as well. This treats internal and terminal ghost states, not only an initial zero mass.

OriginalLawTrimming uses this inclusion theorem to construct one original law together with its retained law. The output map commutes exactly with the inclusion, so their visible laws coincide as measures, beyond equality of individual finite cylinders.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/PositiveSupportPresentation.include_cylinders`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/PositiveSupportPresentation.trim_no11`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/MarkedPredictiveQuotient](MarkedPredictiveQuotient.md)
