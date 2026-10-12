# Native uniform innovations and the critical Bernoulli-factory moment

## Abstract

Native uniform innovations and the critical Bernoulli-factory moment.

Uniform [0,1] innovations are converted to Bernoulli answers in acquisition order. The resulting native execution preserves the source kernel, private-seed posterior and finite-leaf table law. Bernoulli-factory existence is classical (Keane--O'Brien and Nacu--Peres); the critical fractional-cost lower bound, exact native bookkeeping and its complete-output contract are repository-derived.

**Theorem 1.1 (A labelled native source trace has the product Bernoulli law).**

Lean statement: `D5/S3/Estimation/SequentialDecisionRisk/NativeBernoulliFactoryCriticalMoment.native_source_trace_law`

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/SequentialDecisionRisk/NativeBernoulliFactoryCriticalMoment.native_source_trace_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Williams (1991). *Probability with Martingales*. DOI: [10.1017/CBO9780511813658](https://doi.org/10.1017/CBO9780511813658). URL: <https://doi.org/10.1017/CBO9780511813658>.

*Commentary.*

For every measurable policy, source request, finite labelled trace, and measurable seed event, the native uniform implementation has the seed-section mass times the product of the requested Bernoulli cell probabilities.

**Theorem 1.2 (The next native answer has the requested conditional kernel).**

Lean statement: `D5/S3/Estimation/SequentialDecisionRisk/NativeBernoulliFactoryCriticalMoment.native_source_conditional_kernel`

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/SequentialDecisionRisk/NativeBernoulliFactoryCriticalMoment.native_source_conditional_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Williams (1991). *Probability with Martingales*. DOI: [10.1017/CBO9780511813658](https://doi.org/10.1017/CBO9780511813658). URL: <https://doi.org/10.1017/CBO9780511813658>.

*Commentary.*

Conditioned on any reached trace, source action and measurable private-seed event, the next uniform-to-Bernoulli answer factors with exactly the Bernoulli law for that source rate.

**Theorem 1.3 (A private action table gives the exact finite-leaf law).**

Lean statement: `D5/S3/Estimation/SequentialDecisionRisk/NativeBernoulliFactoryCriticalMoment.native_policy_table_leaf_law`

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/SequentialDecisionRisk/NativeBernoulliFactoryCriticalMoment.native_policy_table_leaf_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Williams (1991). *Probability with Martingales*. DOI: [10.1017/CBO9780511813658](https://doi.org/10.1017/CBO9780511813658). URL: <https://doi.org/10.1017/CBO9780511813658>.

*Commentary.*

For any action-probability table, the probability of a finite labelled trace followed by an action is the product of the table rows along the trace and the independent source likelihood.

**Theorem 1.4 (Identity rows preserve the first source answer).**

Lean statement: `D5/S3/Estimation/SequentialDecisionRisk/NativeBernoulliFactoryCriticalMoment.native_policy_table_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/SequentialDecisionRisk/NativeBernoulliFactoryCriticalMoment.native_policy_table_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Williams (1991). *Probability with Martingales*. DOI: [10.1017/CBO9780511813658](https://doi.org/10.1017/CBO9780511813658). URL: <https://doi.org/10.1017/CBO9780511813658>.

*Commentary.*

If a table's supported root and return rows obey the identity-row conditions, almost every private seed starts with the requested source and every finite return retains that source's first native answer.

**Definition 1.5 (Legal two-source factory parameters).**

Lean statement: `D5/S3/Estimation/SequentialDecisionRisk/NativeBernoulliFactoryCriticalMoment.FactoryParameters`

*Formalization.* `D5/S3/Estimation/SequentialDecisionRisk/NativeBernoulliFactoryCriticalMoment.FactoryParameters` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Williams (1991). *Probability with Martingales*. DOI: [10.1017/CBO9780511813658](https://doi.org/10.1017/CBO9780511813658). URL: <https://doi.org/10.1017/CBO9780511813658>.

*Commentary.*

FactoryParameters records B, C, kappa, gain g and positive noninteger beta together with their legal bounds.

**Definition 1.6 (Legal worlds for fixed parameters).**

Lean statement: `D5/S3/Estimation/SequentialDecisionRisk/NativeBernoulliFactoryCriticalMoment.World`

*Formalization.* `D5/S3/Estimation/SequentialDecisionRisk/NativeBernoulliFactoryCriticalMoment.World` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Williams (1991). *Probability with Martingales*. DOI: [10.1017/CBO9780511813658](https://doi.org/10.1017/CBO9780511813658). URL: <https://doi.org/10.1017/CBO9780511813658>.

*Commentary.*

A World chooses a two-branch index, a rate multiplier in its closed legal interval, and a positive h in the prescribed window.

**Theorem 1.7 (Native uniform execution pays the critical logarithmic cost).**

Lean statement: `D5/S3/Estimation/SequentialDecisionRisk/NativeBernoulliFactoryCriticalMoment.native_factory_logarithmic_total_call_cost`

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/SequentialDecisionRisk/NativeBernoulliFactoryCriticalMoment.native_factory_logarithmic_total_call_cost` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Williams (1991). *Probability with Martingales*. DOI: [10.1017/CBO9780511813658](https://doi.org/10.1017/CBO9780511813658). URL: <https://doi.org/10.1017/CBO9780511813658>.

*Commentary.*

For every legal parameter record and m above beta/2, complete-output total-variation accuracy at every legal world forces a positive logarithmic lower bound on the maximum expected fractional cost of the actual native source calls.

**Theorem 1.8 (Arbitrary real policy tables retain the native lower bound).**

Lean statement: `D5/S3/Estimation/SequentialDecisionRisk/NativeBernoulliFactoryCriticalMoment.real_policy_factory_logarithmic_total_call_cost`

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/SequentialDecisionRisk/NativeBernoulliFactoryCriticalMoment.real_policy_factory_logarithmic_total_call_cost` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Williams (1991). *Probability with Martingales*. DOI: [10.1017/CBO9780511813658](https://doi.org/10.1017/CBO9780511813658). URL: <https://doi.org/10.1017/CBO9780511813658>.

*Commentary.*

Every arbitrary real-probability table satisfies the exact native leaf, conditional-kernel, posterior, history-count and identity contracts; if it returns almost surely and is complete-output accurate, its actual total-call fractional cost is at least the same logarithmic lower bound.

## References

- Truth anchor: `D5/S3/Estimation/SequentialDecisionRisk/NativeBernoulliFactoryCriticalMoment.FactoryParameters`
- Truth anchor: `D5/S3/Estimation/SequentialDecisionRisk/NativeBernoulliFactoryCriticalMoment.World`
- Truth anchor: `D5/S3/Estimation/SequentialDecisionRisk/NativeBernoulliFactoryCriticalMoment.native_factory_logarithmic_total_call_cost`
- Truth anchor: `D5/S3/Estimation/SequentialDecisionRisk/NativeBernoulliFactoryCriticalMoment.native_policy_table_identity`
- Truth anchor: `D5/S3/Estimation/SequentialDecisionRisk/NativeBernoulliFactoryCriticalMoment.native_policy_table_leaf_law`
- Truth anchor: `D5/S3/Estimation/SequentialDecisionRisk/NativeBernoulliFactoryCriticalMoment.native_source_conditional_kernel`
- Truth anchor: `D5/S3/Estimation/SequentialDecisionRisk/NativeBernoulliFactoryCriticalMoment.native_source_trace_law`
- Truth anchor: `D5/S3/Estimation/SequentialDecisionRisk/NativeBernoulliFactoryCriticalMoment.real_policy_factory_logarithmic_total_call_cost`
- Dependency: [D5/S3/Estimation/SequentialDecisionRisk/SeededBernoulliFactoryExecution](SeededBernoulliFactoryExecution.md)
