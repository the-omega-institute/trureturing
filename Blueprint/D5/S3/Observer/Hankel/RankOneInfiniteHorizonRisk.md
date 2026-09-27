# RankOneInfiniteHorizonRisk

## Abstract

Sharp uniform prediction error for strictly stable scalar responses.

**Definition 1.1 (Compatible observations).**

Lean statement: `D5/S3/Observer/Hankel/RankOneInfiniteHorizonRisk.Compatible`

*Formalization.* `D5/S3/Observer/Hankel/RankOneInfiniteHorizonRisk.Compatible` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a parameter a strictly between zero and one, the impulse response at time k is a to the power k. Data consist of T+1 real observations indexed from zero through T. Each observation differs from its response by at most eta; the errors are deterministic and pointwise bounded.

**Definition 1.2 (All-future risk).**

Lean statement: `D5/S3/Observer/Hankel/RankOneInfiniteHorizonRisk.risk`

*Formalization.* `D5/S3/Observer/Hankel/RankOneInfiniteHorizonRisk.risk` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An estimator is any map from the observation vector to a real prediction at every integer time n at least T. Its loss is the supremum of absolute prediction error over all such times, all parameters in the open unit interval, and every compatible observation vector. Extended nonnegative real values allow unbounded losses.

**Definition 1.3 (Optimal worst-case risk).**

Lean statement: `D5/S3/Observer/Hankel/RankOneInfiniteHorizonRisk.minimaxRisk`

*Formalization.* `D5/S3/Observer/Hankel/RankOneInfiniteHorizonRisk.minimaxRisk` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The minimax risk is the infimum of the all-future risks over all deterministic sequence estimators, without restrictions on computation or measurability.

**Definition 1.4 (Finite Hankel sections).**

Lean statement: `D5/S3/Observer/Hankel/RankOneInfiniteHorizonRisk.hankel`

*Formalization.* `D5/S3/Observer/Hankel/RankOneInfiniteHorizonRisk.hankel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The Hankel section indexed from zero through N has entry a to the power i+j. It is the outer product of the vector of powers with itself, whose zeroth coordinate is one.

**Theorem 1.5 (Exact risk one half).**

Lean statement: `D5/S3/Observer/Hankel/RankOneInfiniteHorizonRisk.rank_one_infinite_horizon_risk`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/RankOneInfiniteHorizonRisk.rank_one_infinite_horizon_risk` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite integer T at least one and every positive eta, the all-future minimax risk equals one half. Every response tends to zero, and every nonempty finite Hankel section is positive semidefinite with rank exactly one. No common spectral gap is imposed.

The constant prediction one half bounds the error by one half. For the reverse inequality, the all-one observation vector is compatible with stable parameters sufficiently close to one. Fix one such parameter b and choose an allowed late time at which its response is arbitrarily small. A second parameter a can be chosen closer to one so that it remains compatible with the same data and its response at that time is arbitrarily close to one. The same prediction then incurs error approaching one half for at least one of these systems.

## References

- Truth anchor: `D5/S3/Observer/Hankel/RankOneInfiniteHorizonRisk.Compatible`
- Truth anchor: `D5/S3/Observer/Hankel/RankOneInfiniteHorizonRisk.hankel`
- Truth anchor: `D5/S3/Observer/Hankel/RankOneInfiniteHorizonRisk.minimaxRisk`
- Truth anchor: `D5/S3/Observer/Hankel/RankOneInfiniteHorizonRisk.rank_one_infinite_horizon_risk`
- Truth anchor: `D5/S3/Observer/Hankel/RankOneInfiniteHorizonRisk.risk`
