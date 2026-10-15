# Condition K on the original emitted-bit clock

## Abstract

Condition K on the original emitted-bit clock

The deterministic-state observation convention is represented by arrival matrices K times the diagonal selector. Its equality with the usual stationary state-observation cylinder formula is proved on the same integer clock.

**Definition 1.1 (The deterministic observation selector).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateConditionK.observation`

*Formalization.* `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateConditionK.observation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a state observation f and Boolean x, observation(f,x) is the diagonal indicator of f(i)=x, retaining every structural zero.

**Theorem 1.2 (The actual Condition K exclusion).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateConditionK.actual_condition_k_boundary`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateConditionK.actual_condition_k_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite stationary marked presentation θ, transition matrix K and deterministic observation f with θ.matrix(x)=K observation(f,x), assume its whole visible law equals the actual twelve-state P and every pair of hidden states has a positive K-power entry. For every integer origin and every finite word, the actual cylinder mass equals the usual departure-observation formula using observation(f,x)K. Every word product of the arrival matrices has no nonempty exact positive rectangular support. Summing selectors gives K, hence stationarity and stochasticity transfer from θ. The intertwining identity cancels K at the two ends under the stationary initial row and stochastic final column. Irreducible positive stationary masses then make a nonzero rectangle a supported word, contradicting the same-law obstruction. Thus the additional aperiodicity required by finite Condition K cannot restore such a presentation. No rank-one or scaled-closure assertion is made.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateConditionK.actual_condition_k_boundary`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateConditionK.observation`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/PositiveRectangleLaw](PositiveRectangleLaw.md)
