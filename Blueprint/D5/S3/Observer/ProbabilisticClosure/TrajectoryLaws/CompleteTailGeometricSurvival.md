# Complete-event geometric survival

## Abstract

CompleteTailGeometricSurvival

**Theorem 1.1 (Two-read survival and noncompletion).**

$$\forall X:FiniteType, (\forall Y:FiniteType, (\forall R:RegularTableXY, (\operatorname{RegularCompleteSurvival}(X, Y, R))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/CompleteTailGeometricSurvival.regular_complete_survival` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any finite types X and Y and actual RegularTable R, survivalEvent(n) contains none and finite words longer than n. At every x and y, its complete-law mass at cut 2n is at most (4/15)^n. The prefix inverse identity holds also for none. Two real all-event recursions multiply the upper continuation coefficients 2/3 and 2/5; row normalization gives a uniform two-read bound. The geometric bound tends to zero, hence each Q(x) and W(y) assigns zero mass to none. No properness assumption is required in addition to the RegularTable generation fields. This applies to the clamped native comparison, while the original emitter may retain noncompletion mass.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/CompleteTailGeometricSurvival.regular_complete_survival`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/CompleteTailWeightedDistortion](CompleteTailWeightedDistortion.md)
