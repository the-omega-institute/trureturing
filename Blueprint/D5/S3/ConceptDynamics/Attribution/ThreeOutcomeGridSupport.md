# Seed budgets for covariant three-outcome calibration

## Abstract

A sharp seed budget for exact three-outcome calibration with label symmetries.

**Definition 1.1 (Calibrating law on a three-outcome grid).**

$$\operatorname{CalibratingLaw}\left(S, w, f\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Attribution/ThreeOutcomeGridSupport.CalibratingLaw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Profiles are triples of nonnegative integer coordinates with sum six times q. The finite seed set S carries an action of the permutation group on three labels. The real weights w are strictly positive, sum to one, and are invariant under this action. The deterministic readout f assigns each profile and seed to one label. Each label's mass equals its profile coordinate divided by six times q. Simultaneously permuting the profile and seed takes the readout to the permuted label.

**Theorem 1.2 (Sharp three-outcome support budget).**

$$\forall q n, 0 < q \Rightarrow (\operatorname{SeedBudget}\left(6 \cdot q, 6 \cdot n\right) \iff 3 \cdot q + 1 \le 4^n)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/ThreeOutcomeGridSupport.triple_grid_support_budget_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive q and a natural budget n, a calibrating law exists on at most six times n seeds exactly when four to the power n is at least three times q plus one.

A permutation that fixes a seed must fix the readout at the uniform profile. A nonidentity permutation of three labels has at most one fixed label. At the profile with zero weight on that label and equal weights on the other two, the seed would have to return the zero-mass label. Positivity then gives a contradiction. Each seed orbit therefore has six elements. A transposition at a profile with two equal coordinates gives equal label counts within each orbit, limiting either count to the four values from zero through three.

The construction grows integer orbit weights with the bounded-digit constraint from complete partitions. Adding six seeds of a new weight preserves all ordered triple allocations, because the three integer capacities after division by the new weight have sum at least six. The same weights represent all tied-coordinate masses with four occupancy digits. The uniform profile uses the same count for all three labels in each orbit. Stabilizer-compatible readouts at representative profiles extend by permuting both inputs. Normalize the positive weights by the denominator.

The seed law is an input. The statement concerns a finite probability grid that includes zero coordinates and uses a denominator divisible by six.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Attribution/ThreeOutcomeGridSupport.CalibratingLaw`
- Truth anchor: `D5/S3/ConceptDynamics/Attribution/ThreeOutcomeGridSupport.triple_grid_support_budget_iff`
- Dependency: [D5/S3/ConceptDynamics/Attribution/CovariantGridSupport](CovariantGridSupport.md)
