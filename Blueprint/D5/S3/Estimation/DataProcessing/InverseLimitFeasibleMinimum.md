# A nearest feasible completed law

## Abstract

A nearest feasible completed law.

**Theorem 1.1 (A nearest feasible completed law).**

$$\begin{aligned}\exists mu, d, Q: \operatorname{extendsMarginals}\left(mu\right), \operatorname{finiteMinima}\left(d\right), \operatorname{Monotone}\left(d\right), \operatorname{boundedByOne}\left(d\right)\\\operatorname{feasible}\left(Q\right), \operatorname{TV}\left(P, Q\right) = \operatorname{sup}\left(d\right)\\\forall R, \operatorname{feasible}\left(R\right) \Rightarrow \operatorname{TV}\left(P, Q\right) \le \operatorname{TV}\left(P, R\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/DataProcessing/InverseLimitFeasibleMinimum.exists_feasible_minimum_eq_iSup` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take a tower of finite nonempty discrete Borel alphabets with surjective bonding maps and commuting permutations. Legal joint supports are preserved by the coordinatewise bonding maps. Fix a compatible family of finite marginal probabilities and suppose that every finite feasible set is nonempty.

The comparison probability on the completed tuple space is arbitrary. Each finite total-variation minimum is attained, and these minimum values lie between zero and one and increase with the level. There is one completed feasible law whose total-variation distance from the comparison probability equals the supremum of the finite minimum values and is no larger than the distance of any completed feasible law.

Finite feasible sets are closed subsets of compact probability spaces: support, marginal equalities and zero expected excess are closed conditions. One-cut support transports zero excess through the bonding maps, while event pullbacks contract total variation.

Intersect each feasible set with the ball of the same radius, the supremum of the finite minima. These nonempty compact sets form an inverse system. A common thread of laws extends to a Borel probability; the proved feasibility correspondence and full-event total-variation identity establish attainment.

The completed marginal probability is constructed from the given finite marginal tower and has exactly those projections. No surjectivity of feasible-law maps, compatibility of separately selected minimizers, uniqueness of the nearest law or measurable selection is asserted.

## References

- Truth anchor: `D5/S3/Estimation/DataProcessing/InverseLimitFeasibleMinimum.exists_feasible_minimum_eq_iSup`
- Dependency: [D5/S3/Estimation/DataProcessing/InverseLimitFeasibleLaws](InverseLimitFeasibleLaws.md)
