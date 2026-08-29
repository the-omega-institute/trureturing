# Agency Completion Minimality

## Abstract

Componentwise recoverability induces recoverability of the paired agency completion.

**Theorem 1.1 (Component factorizations induce a paired factorization).**

$$\forall current: H \to M, profile: H \to P,\\{}summary: H \to S, currentFactor: S \to M,\\{}profileFactor: S \to P,\\{}(\forall h: H, \operatorname{current}\left(h\right) = \operatorname{currentFactor}\left(\operatorname{summary}\left(h\right)\right) \land \forall h: H, \operatorname{profile}\left(h\right) = \operatorname{profileFactor}\left(\operatorname{summary}\left(h\right)\right)) \Rightarrow \exists pairFactor: S \to \operatorname{Prod}\left(M, P\right), h \mapsto (\operatorname{current}\left(h\right), \operatorname{profile}\left(h\right)) = pairFactor \circ summary.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/AgencySelf/AgencyCompletionMinimality.paired_completion_factors_through_summary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume both the current-memory readout and the strategy profile factor pointwise through the same summary.

Pair the two supplied factor maps. This yields a factor from summaries to memory-profile pairs through which the paired completion equals the composite with the summary.

The conclusion asserts existence of that paired factor; it does not claim uniqueness or a converse factorization.

**Theorem 1.2 (The paired completion recovers both components).**

$$\forall current: H \to M, profile: H \to P, (h \mapsto \operatorname{fst}\left(\operatorname{pair}\left(\operatorname{current}\left(h\right), \operatorname{profile}\left(h\right)\right)\right) = current \land h \mapsto \operatorname{snd}\left(\operatorname{pair}\left(\operatorname{current}\left(h\right), \operatorname{profile}\left(h\right)\right)\right) = profile).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/AgencySelf/AgencyCompletionMinimality.paired_completion_recovers_components` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary current and profile readouts, pair their values at each history.

The first and second product projections recover the current and profile functions respectively, with no extra assumptions.

## References

- Truth anchor: `D5/S3/Observer/AgencySelf/AgencyCompletionMinimality.paired_completion_factors_through_summary`
- Truth anchor: `D5/S3/Observer/AgencySelf/AgencyCompletionMinimality.paired_completion_recovers_components`
