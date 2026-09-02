# First-Break Rational Counterexample

## Abstract

A first nonzero observation admits both rational and irrational first coordinates.

**Definition 1.1 (First break).**

Lean statement: `D5/S3/CompletionDynamics/FirstBreakRationalCounterexample.HasFirstBreak`

*Formalization.* `D5/S3/CompletionDynamics/FirstBreakRationalCounterexample.HasFirstBreak` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A trajectory has a first break when coordinate zero vanishes and coordinate one does not.

**Theorem 1.2 (A first break does not force irrationality).**

$$\exists r, i: \mathbb{N} \to \mathbb{R},\\HasFirstBreak(r) \land \neg Irrational(r(1)) \land\\HasFirstBreak(i) \land Irrational(i(1)).$$

*Proof.* Machine-checked in Lean as `D5/S3/CompletionDynamics/FirstBreakRationalCounterexample.first_break_does_not_force_irrationality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There are two explicit real trajectories with a first break: one has rational first coordinate one, while the other has irrational first coordinate square root of two.

The paired witnesses show that the first-break condition alone does not select either arithmetic type.

## References

- Truth anchor: `D5/S3/CompletionDynamics/FirstBreakRationalCounterexample.HasFirstBreak`
- Truth anchor: `D5/S3/CompletionDynamics/FirstBreakRationalCounterexample.first_break_does_not_force_irrationality`
