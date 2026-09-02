# Agency Reserve Stability

## Abstract

A positive singular-value reserve is the sharp perturbation radius preserving an agency dimension.

**Theorem 1.1 (Reserve controls robust rank and its sharp boundary).**

$$\begin{gathered}B \in \operatorname{RankAtMost}\left(k\right) \land\\{}\operatorname{infDist}\left(H\left(x\right), \operatorname{RankAtMost}\left(k\right)\right) = \operatorname{Reserve}\left(H\left(x\right), k\right) \land\\{}\operatorname{dist}\left(H\left(x\right), B\right) = \operatorname{infDist}\left(H\left(x\right), \operatorname{RankAtMost}\left(k\right)\right) \land\\{}0 < \operatorname{Reserve}\left(H\left(x\right), k\right) \land \operatorname{ContinuousAt}\left(\Lambda y. \operatorname{Reserve}\left(H\left(y\right), k\right), x\right) \Rightarrow\\{}\operatorname{Nonempty}\left(\operatorname{RankAtMost}\left(k\right)\right) \land \operatorname{infDist}\left(H\left(x\right), \operatorname{RankAtMost}\left(k\right)\right) = \operatorname{Reserve}\left(H\left(x\right), k\right) \land\\{}(\forall \Delta, \left\lVert \Delta \right\rVert < \operatorname{Reserve}\left(H\left(x\right), k\right) \Rightarrow k + 1 \leq \operatorname{rank}\left(H\left(x\right) + \Delta\right) \land 0 < \operatorname{Reserve}\left(H\left(x\right) + \Delta, k\right)) \land\\{}(\exists \Delta, \left\lVert \Delta \right\rVert = \operatorname{Reserve}\left(H\left(x\right), k\right) \land \operatorname{rank}\left(H\left(x\right) + \Delta\right) \leq k \land \operatorname{Reserve}\left(H\left(x\right) + \Delta, k\right) = 0) \land\\{}(\forall epsilon < \operatorname{Reserve}\left(H\left(x\right), k\right), \exists U \in \operatorname{N}\left(x\right), U \subseteq \operatorname{Safe}\left(H, k, epsilon\right)) \land\\{}(\exists V \in \operatorname{N}\left(x\right), \forall y \in V, k + 1 \leq \operatorname{rank}\left(H\left(y\right)\right)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/AgencyReserveStability.agency_reserve_stability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The index k is zero-based and represents the source's one-based agency dimension r = k + 1. This avoids truncated natural subtraction in the rank-at-most-(r-1) comparison class.

Eckart-Young-Mirsky and continuity of the selected singular value are explicit premises because pinned Mathlib supplies neither theorem. The low-rank set is nevertheless constructively nonempty, containing the zero operator.

Any smaller perturbation cannot enter the low-rank set, by the defining lower bound for infimum distance. An attaining best approximation constructs a perturbation exactly at the reserve whose selected singular value is zero, proving boundary sharpness.

Continuity places a neighborhood of the base point inside every safe region with threshold below the reserve. Mathlib's singular-value support theorem then keeps at least k + 1 range dimensions throughout a local neighborhood.

## References

- Truth anchor: `D5/S3/Observer/AgencyReserveStability.agency_reserve_stability`
