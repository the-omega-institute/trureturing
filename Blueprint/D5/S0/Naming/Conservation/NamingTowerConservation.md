# Naming Tower Conservation

## Abstract

Countable naming towers leave a full-measure anonymous complement.

**Proposition 1.1 (Countable towers leave a full-measure anonymous complement).**

$$Countable(namedUnion(systems)) \land \mu(namedUnion(systems)) = 0 \land \mu(X \setminus namedUnion(systems)) = \mu(X).$$

*Proof.* Machine-checked in Lean as `D5/S0/Naming/Conservation/NamingTowerConservation.countable_tower_anonymous_full_measure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The index type is arbitrary but countable, so it covers finite towers and countably infinite limiting towers without imposing an unclaimed nesting condition. Each layer is a NamingSystem, whose finite height sublevels make its named image countable.

The countable union of those named images is countable. Atomlessness makes that union null, and the complement-null measure identity then gives the anonymous complement exactly the measure of the whole carrier.

Pinned Mathlib supplies Set.Countable.measure_zero and measure_of_measure_compl_eq_zero. The repository theorem D5.S0.Naming.dark_side_conservation supplies the nullity clause; this corollary retains the countability mechanism and the full-measure complement conclusion explicitly.

## References

- Truth anchor: `D5/S0/Naming/Conservation/NamingTowerConservation.countable_tower_anonymous_full_measure`
- Dependency: [D5/S0/Naming/NamingSystem](../NamingSystem.md)
