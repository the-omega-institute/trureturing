# Equivariant Exposure on a Transitive Action

## Abstract

A single value determines an equivariant map on a transitive group action.

**Theorem 1.1 (One value determines an equivariant map).**

$$\operatorname{Transitive}(G, X) \land \operatorname{Equivariant}(f) \land \operatorname{Equivariant}(g) \land f(x_{0}) = g(x_{0}) \Rightarrow f = g.$$

*Proof.* Machine-checked in Lean as `D5/S0/Diagonal/Equivariance/EquivariantExposure.equivariant_maps_eq_of_eq_at` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any target point, pretransitivity supplies a group element that moves the chosen base point to that target. Equivariance transports the base-point equality along this group element, so the two maps agree at every point.

The proof reuses Mathlib's isPretransitive_iff_base theorem. No finiteness, faithfulness, or action on the codomain beyond a MulAction is required.

This is partial closure of the source atom's symmetric-exposure clause: equivariance turns one representative check into a global check. It does not formalize the Delta tax table, probe counterexample, or the gate-to-twist classification stated elsewhere in that atom.

## References

- Truth anchor: `D5/S0/Diagonal/Equivariance/EquivariantExposure.equivariant_maps_eq_of_eq_at`
