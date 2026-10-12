# Seeded Bernoulli factory execution and total-call lower bounds

## Abstract

Seeded Bernoulli factory execution and total-call lower bounds.

A policy sees a private seed, a requested source label, and the complete acquired history. Each source action appends one actually acquired Bernoulli answer; a return action emits the complete two-bit cell. The record charges every source answer, including both labels at a finite return, and assigns infinite cost to nonreturn. The classical Bernoulli-factory existence results of Keane--O'Brien and Nacu--Peres concern terminating simulation; the stopping/likelihood transfer used here is classical. The logarithmic total-call lower bound is a repository-derived consequence for this complete-output contract.

**Definition 1.1 (The acquired source history).**

Lean statement: `D5/S3/Estimation/SequentialDecisionRisk/SeededBernoulliFactoryExecution.acquiredHistory`

*Formalization.* `D5/S3/Estimation/SequentialDecisionRisk/SeededBernoulliFactoryExecution.acquiredHistory` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Williams (1991). *Probability with Martingales*. DOI: [10.1017/CBO9780511813658](https://doi.org/10.1017/CBO9780511813658). URL: <https://doi.org/10.1017/CBO9780511813658>.

*Commentary.*

Given a policy, request, answer tape and finite time n, acquiredHistory recursively appends exactly the source answer produced by each source action and leaves a return action unchanged.

**Lemma 1.2 (Action cells have measurable singleton events).**

Lean statement: `D5/S3/Estimation/SequentialDecisionRisk/SeededBernoulliFactoryExecution.action_singleton_measurable`

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/SequentialDecisionRisk/SeededBernoulliFactoryExecution.action_singleton_measurable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Williams (1991). *Probability with Martingales*. DOI: [10.1017/CBO9780511813658](https://doi.org/10.1017/CBO9780511813658). URL: <https://doi.org/10.1017/CBO9780511813658>.

*Commentary.*

Every source or return action has a measurable singleton in the discrete sum action space.

**Lemma 1.3 (The first return time is a stopping time).**

Lean statement: `D5/S3/Estimation/SequentialDecisionRisk/SeededBernoulliFactoryExecution.calls_stopping`

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/SequentialDecisionRisk/SeededBernoulliFactoryExecution.calls_stopping` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Williams (1991). *Probability with Martingales*. DOI: [10.1017/CBO9780511813658](https://doi.org/10.1017/CBO9780511813658). URL: <https://doi.org/10.1017/CBO9780511813658>.

*Commentary.*

For a measurable policy, the first time its action belongs to the return-cell range is a stopping time for the seeded filtration.

**Lemma 1.4 (The stopped output is measurable).**

Lean statement: `D5/S3/Estimation/SequentialDecisionRisk/SeededBernoulliFactoryExecution.output_stopped_measurable`

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/SequentialDecisionRisk/SeededBernoulliFactoryExecution.output_stopped_measurable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Williams (1991). *Probability with Martingales*. DOI: [10.1017/CBO9780511813658](https://doi.org/10.1017/CBO9780511813658). URL: <https://doi.org/10.1017/CBO9780511813658>.

*Commentary.*

The cell returned at the first return time is measurable in the sigma algebra supplied by the stopping time.

**Theorem 1.5 (Every pre-return prefix contains one answer per step).**

Lean statement: `D5/S3/Estimation/SequentialDecisionRisk/SeededBernoulliFactoryExecution.acquired_history_length_before_return`

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/SequentialDecisionRisk/SeededBernoulliFactoryExecution.acquired_history_length_before_return` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Williams (1991). *Probability with Martingales*. DOI: [10.1017/CBO9780511813658](https://doi.org/10.1017/CBO9780511813658). URL: <https://doi.org/10.1017/CBO9780511813658>.

*Commentary.*

If n is no later than the first return, the acquired history at n has length n.

**Theorem 1.6 (A finite return charges all acquired answers).**

Lean statement: `D5/S3/Estimation/SequentialDecisionRisk/SeededBernoulliFactoryExecution.acquired_history_length_at_return`

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/SequentialDecisionRisk/SeededBernoulliFactoryExecution.acquired_history_length_at_return` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Williams (1991). *Probability with Martingales*. DOI: [10.1017/CBO9780511813658](https://doi.org/10.1017/CBO9780511813658). URL: <https://doi.org/10.1017/CBO9780511813658>.

*Commentary.*

When the first return occurs at n, the acquired history has length n, so the two source labels in the returned cell are included in the charged record.

**Lemma 1.7 (The abstract cost equals the charged record cost).**

Lean statement: `D5/S3/Estimation/SequentialDecisionRisk/SeededBernoulliFactoryExecution.cost_eq_record_cost`

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/SequentialDecisionRisk/SeededBernoulliFactoryExecution.cost_eq_record_cost` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Williams (1991). *Probability with Martingales*. DOI: [10.1017/CBO9780511813658](https://doi.org/10.1017/CBO9780511813658). URL: <https://doi.org/10.1017/CBO9780511813658>.

*Commentary.*

The WithTop call cost agrees pointwise with the fractional power of the acquired record length, with infinite value exactly at nonreturn.

**Lemma 1.8 (The four-cell perturbation is normalized).**

Lean statement: `D5/S3/Estimation/SequentialDecisionRisk/SeededBernoulliFactoryExecution.target_mass`

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/SequentialDecisionRisk/SeededBernoulliFactoryExecution.target_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Williams (1991). *Probability with Martingales*. DOI: [10.1017/CBO9780511813658](https://doi.org/10.1017/CBO9780511813658). URL: <https://doi.org/10.1017/CBO9780511813658>.

*Commentary.*

The four real cell masses consisting of the Bernoulli base row and signed diagonal perturbation sum to one for all real u, h and beta.

**Theorem 1.9 (Every accurate seeded policy pays logarithmic total-call cost).**

Lean statement: `D5/S3/Estimation/SequentialDecisionRisk/SeededBernoulliFactoryExecution.seeded_policy_logarithmic_total_call_cost`

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/SequentialDecisionRisk/SeededBernoulliFactoryExecution.seeded_policy_logarithmic_total_call_cost` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Williams (1991). *Probability with Martingales*. DOI: [10.1017/CBO9780511813658](https://doi.org/10.1017/CBO9780511813658). URL: <https://doi.org/10.1017/CBO9780511813658>.

*Commentary.*

For B equal to 2 or 4, C at least one, positive noninteger beta and any integer moment order m above beta/2, there are positive k and delta-zero such that every measurable parameter-independent seeded policy whose complete four-cell output is delta-close throughout the legal h-window has worst-world expected record cost at least k log(delta inverse). Infinite cost is retained for nonreturn.

**Theorem 1.10 (Independent action tables realize the same lower bound).**

Lean statement: `D5/S3/Estimation/SequentialDecisionRisk/SeededBernoulliFactoryExecution.real_policy_table_logarithmic_total_call_cost`

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/SequentialDecisionRisk/SeededBernoulliFactoryExecution.real_policy_table_logarithmic_total_call_cost` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Williams (1991). *Probability with Martingales*. DOI: [10.1017/CBO9780511813658](https://doi.org/10.1017/CBO9780511813658). URL: <https://doi.org/10.1017/CBO9780511813658>.

*Commentary.*

Every countable table of arbitrary real-probability action rows is realized by independent private coordinates. The row marginals are exact and the same complete-output logarithmic record-cost lower bound holds.

## References

- Truth anchor: `D5/S3/Estimation/SequentialDecisionRisk/SeededBernoulliFactoryExecution.acquiredHistory`
- Truth anchor: `D5/S3/Estimation/SequentialDecisionRisk/SeededBernoulliFactoryExecution.acquired_history_length_at_return`
- Truth anchor: `D5/S3/Estimation/SequentialDecisionRisk/SeededBernoulliFactoryExecution.acquired_history_length_before_return`
- Truth anchor: `D5/S3/Estimation/SequentialDecisionRisk/SeededBernoulliFactoryExecution.action_singleton_measurable`
- Truth anchor: `D5/S3/Estimation/SequentialDecisionRisk/SeededBernoulliFactoryExecution.calls_stopping`
- Truth anchor: `D5/S3/Estimation/SequentialDecisionRisk/SeededBernoulliFactoryExecution.cost_eq_record_cost`
- Truth anchor: `D5/S3/Estimation/SequentialDecisionRisk/SeededBernoulliFactoryExecution.output_stopped_measurable`
- Truth anchor: `D5/S3/Estimation/SequentialDecisionRisk/SeededBernoulliFactoryExecution.real_policy_table_logarithmic_total_call_cost`
- Truth anchor: `D5/S3/Estimation/SequentialDecisionRisk/SeededBernoulliFactoryExecution.seeded_policy_logarithmic_total_call_cost`
- Truth anchor: `D5/S3/Estimation/SequentialDecisionRisk/SeededBernoulliFactoryExecution.target_mass`
- Dependency: [D5/S3/Estimation/SequentialDecisionRisk/BernoulliCommonEndpointCharge](BernoulliCommonEndpointCharge.md)
- Dependency: [D5/S3/TotalVariation/Metric](../../TotalVariation/Metric.md)
