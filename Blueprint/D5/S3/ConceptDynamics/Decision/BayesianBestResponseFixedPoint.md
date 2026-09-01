# Bayesian Best Responses as Fixed Points

## Abstract

Finite Bayesian best responses form a nonempty correspondence whose equilibria are membership fixed points.

**Definition 1.1 (Finite conditional expected utility).**

Lean statement: `D5/S3/ConceptDynamics/Decision/BayesianBestResponseFixedPoint.conditionalExpectedUtility`

*Formalization.* `D5/S3/ConceptDynamics/Decision/BayesianBestResponseFixedPoint.conditionalExpectedUtility` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

On a finite state space, conditional expected utility is the prior-weighted utility sum over one signal fiber divided by that fiber's prior mass. The best-response definition invokes it only when this mass is strictly positive.

**Definition 1.2 (The Bayesian best-response correspondence).**

Lean statement: `D5/S3/ConceptDynamics/Decision/BayesianBestResponseFixedPoint.bestResponses`

*Formalization.* `D5/S3/ConceptDynamics/Decision/BayesianBestResponseFixedPoint.bestResponses` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A policy belongs to the response set when, at every positive-mass signal, its selected action realizes an IsGreatest value in the range of conditional expected utility. No condition is imposed at a zero-mass signal, and several maximizing actions may coexist.

**Theorem 1.3 (Positive normalization preserves the full argmax set).**

$$0 < Pr\left(b\right) \Rightarrow\\{}IsGreatest\left(range\left(CEU_{b}\right), CEU\left(b, pi\left(b\right)\right)\right) \iff IsGreatest\left(range\left(Numerator_{b}\right), Numerator\left(b, pi\left(b\right)\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Decision/BayesianBestResponseFixedPoint.conditional_argmax_iff_unnormalized_argmax` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a positive-probability signal, every conditional utility comparison is equivalent to the corresponding comparison between weighted-sum numerators. The proof divides both candidates by the same positive fiber mass, so it preserves all ties rather than choosing a unique maximizer.

**Theorem 1.4 (Finite best-response sets are nonempty).**

$$Finite\left(A\right) \land Nonempty\left(A\right) \Rightarrow \exists pi, pi \in BR\left(pi_{-i}\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Decision/BayesianBestResponseFixedPoint.bestResponses_nonempty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A finite nonempty action type has a maximizing conditional utility at each signal. Choosing one maximizer for each signal constructs a policy in the response set; zero-probability signals require no additional obligation.

**Definition 1.5 (Two-player Bayesian Nash equilibrium).**

Lean statement: `D5/S3/ConceptDynamics/Decision/BayesianBestResponseFixedPoint.IsBayesianNashEquilibrium`

*Formalization.* `D5/S3/ConceptDynamics/Decision/BayesianBestResponseFixedPoint.IsBayesianNashEquilibrium` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For two players with common finite state, signal, and action types, a profile is an equilibrium exactly when it belongs to the joint best-response set evaluated at itself.

**Theorem 1.6 (Bayesian Nash equilibrium is a best-response fixed point).**

$$BNE\left(pi\right) \iff \forall i \in Fin\left(2\right), pi_{i} \in BR\left(i, pi_{-i}\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Decision/BayesianBestResponseFixedPoint.bayesian_nash_equilibrium_iff_fixed_point` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Unfolding the joint correspondence says that each player's policy belongs to its response set against the other player's policy. This is the source fixed-point equation in a two-player model.

The formalization deliberately uses common signal and action types for the two players. It does not claim the heterogeneous general-n version, nor does it claim existence of a fixed point.

**Theorem 1.7 (The one-agent specialization is policy in BR of itself).**

$$SingleBNE\left(pi\right) \iff pi \in BR\left(pi\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Decision/BayesianBestResponseFixedPoint.single_agent_bayesian_equilibrium_iff_fixed_point` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When the response input and output policy are the same coordinate, the equilibrium statement has the literal membership-fixed-point form policy in BR(policy).

**Theorem 1.8 (The all-false coordination profile is a BNE).**

$$BNE\left(pi_{0}\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Decision/BayesianBestResponseFixedPoint.coordination_false_profile_is_bayesian_nash` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the unit-state, unit-signal, two-action coordination game, both players receive utility one when their actions agree and zero otherwise. The all-false profile gives each player a maximizing action and is therefore a concrete Bayesian Nash equilibrium.

**Theorem 1.9 (Player zero strictly improves at the mismatched profile).**

$$CEU\left(0, true, pi_{1}\right) > CEU\left(0, false, pi_{1}\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Decision/BayesianBestResponseFixedPoint.coordination_mismatch_player_zero_strict_deviation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At the profile where player zero chooses false and player one chooses true, player zero raises conditional expected utility from zero to one by switching to true.

**Theorem 1.10 (The mismatched profile is not a BNE).**

$$\neg BNE\left(pi_{mismatch}\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Decision/BayesianBestResponseFixedPoint.coordination_mismatch_not_bayesian_nash` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The explicit strict deviation contradicts the IsGreatest upper-bound clause for player zero. Thus the response definition does not classify every strategy profile as an equilibrium.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Decision/BayesianBestResponseFixedPoint.IsBayesianNashEquilibrium`
- Truth anchor: `D5/S3/ConceptDynamics/Decision/BayesianBestResponseFixedPoint.bayesian_nash_equilibrium_iff_fixed_point`
- Truth anchor: `D5/S3/ConceptDynamics/Decision/BayesianBestResponseFixedPoint.bestResponses`
- Truth anchor: `D5/S3/ConceptDynamics/Decision/BayesianBestResponseFixedPoint.bestResponses_nonempty`
- Truth anchor: `D5/S3/ConceptDynamics/Decision/BayesianBestResponseFixedPoint.conditionalExpectedUtility`
- Truth anchor: `D5/S3/ConceptDynamics/Decision/BayesianBestResponseFixedPoint.conditional_argmax_iff_unnormalized_argmax`
- Truth anchor: `D5/S3/ConceptDynamics/Decision/BayesianBestResponseFixedPoint.coordination_false_profile_is_bayesian_nash`
- Truth anchor: `D5/S3/ConceptDynamics/Decision/BayesianBestResponseFixedPoint.coordination_mismatch_not_bayesian_nash`
- Truth anchor: `D5/S3/ConceptDynamics/Decision/BayesianBestResponseFixedPoint.coordination_mismatch_player_zero_strict_deviation`
- Truth anchor: `D5/S3/ConceptDynamics/Decision/BayesianBestResponseFixedPoint.single_agent_bayesian_equilibrium_iff_fixed_point`
