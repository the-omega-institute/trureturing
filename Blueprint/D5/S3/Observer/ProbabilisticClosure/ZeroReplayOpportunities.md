# Opportunities and the first failed opportunity

## Abstract

Pointwise finite opportunity replay for the original two-arm waiting policy.

**Theorem 1.1 (A finite native archive for every seed and root).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/ZeroReplayOpportunities.finite_replay_first_failure`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/ZeroReplayOpportunities.finite_replay_first_failure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix any measurable seed space, any original waiting Policy, any seed, either Boolean root, and any natural r. The all-zero replay uses that policy's actual choices on its acquired action list and a list of false answers. Lists store the newest query first. At zero-based time n the chosen arm's inner endpoint is alternatingBit of the root at that arm's previous query count. A zero inner endpoint is an opportunity.

opportunityCount counts these opportunities in chronological query order. An induction on the original replay proves that this count is the sum of the two local alternating-prefix counts: each arm contributes its query count divided by two, rounded down for a true root and up for a false root. A replay query updates exactly its selected arm. This connects temporal opportunity order to local arm parity, including routes that never visit the other arm.

opportunityQuery is the one-based query number of the first prefix with more than r opportunities. There is a zero-based time n with opportunityQuery equal to n plus one, at most two times r plus three. Before that query the opportunity count is exactly r and its inner endpoint is zero. This follows from the two-arm count and the fact that each query contributes either zero or one opportunity.

archive retains the original seed and the finite native State whose actions are the replay through that query, whose replies are n false answers followed chronologically by one true marker, and whose stopped flag is true. A concrete source starts at the specified root, alternates on both arms before the chosen opportunity, and has false bits from that local edge onward on the marked arm. It has no adjacent true bits. The original actualRun is active after n queries and equals the archive after n plus one. The archive has exactly n plus one acquired actions, so its finite length satisfies the same bound.

The construction uses the original stopped-execution replay bridge. It is a pointwise counterfactual reconstruction; it does not continue queries after an actual marker. No parameter, seed probability law, almost-everywhere qualifier, or fairness assumption occurs. Measurability of the archive map, a measurable inverse, likelihoods, prior mixtures, and almost-sure termination of a randomly sampled actual source are separate statements.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/ZeroReplayOpportunities.finite_replay_first_failure`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/AdaptiveMarkerStoppingTails](AdaptiveMarkerStoppingTails.md)
