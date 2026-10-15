# Checked support conflicts retain the original event semantics

## Abstract

Finite natural joins preserve the same compatible total event.

Rows assign arbitrary finite lists of coordinates and values. Duplicate coordinates are permitted: compatibility requires every listed entry to agree with the same total event. No coordinate is fixed or discarded. The computed natural join checks equality on every overlapping coordinate and concatenates exactly the agreeing pairs.

**Theorem 1.1 (Every shared total event survives a natural join).**

Lean statement: `D5/S0/Certificates/FiniteNaturalJoin.join_covers`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/FiniteNaturalJoin.join_covers` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two compatible witness rows agree on each common coordinate because both use the same actual event. That pair survives the filter, its concatenation occurs in the joined relation, and all its entries retain compatibility. Repeated application therefore lets an actual computed empty join exclude simultaneous support membership. The original EJM support-conflict consumer supplies the full finite inputs and checks the empty join with the Lean kernel.

## References

- Truth anchor: `D5/S0/Certificates/FiniteNaturalJoin.join_covers`
