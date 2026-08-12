# Guarded Walls Stay Outside Forbidden Configurations

## Abstract

A consistent guarded wall cannot become positive while its gatekeepers stay positive.

**Theorem 1.1 (Guarded walls never become positive).**

$$wallNeverPositive$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/GuardedWall.wall_never_positive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A wall is a set of statements that must stay outside a forbidden positive configuration. If every gatekeeper is positive, any positive wall statement would make that configuration forbidden. Consistency rules out the forbidden configuration, so every wall statement is necessarily non-positive at every time.

The Lean proof is a direct contradiction argument: specialize the forbidden-configuration hypothesis to the wall statement and feed it the gatekeeper positivity witnesses, then apply consistency.

**Theorem 1.2 (A Boolean guarded wall has a concrete witness).**

$$booleanGuardedWallWitness$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/GuardedWall.boolean_guarded_wall_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Boolean instance makes all hypotheses simultaneously explicit: true is the sole positive statement, false is the wall, and the forbidden predicate requires both values at once. The witness therefore certifies the hypotheses and the wall's non-positivity without any numerical or external evidence.

## References

- Truth anchor: `D5/S0/Computability/GuardedWall.boolean_guarded_wall_witness`
- Truth anchor: `D5/S0/Computability/GuardedWall.wall_never_positive`
