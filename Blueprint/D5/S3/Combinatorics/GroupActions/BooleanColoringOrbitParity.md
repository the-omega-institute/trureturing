# Parity of Boolean Coloring Orbits

## Abstract

A finite group acting on a finite set of sites has at least as many even Boolean coloring orbits as odd Boolean coloring orbits.

**Theorem 1.1 (Odd and even coloring orbits).**

Lean statement: `D5/S3/Combinatorics/GroupActions/BooleanColoringOrbitParity.card_odd_orbits_le_even`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/GroupActions/BooleanColoringOrbitParity.card_odd_orbits_le_even` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let G be a finite group acting on a finite set of sites. A Boolean coloring assigns zero or one to each site. The group acts on colorings by inverse relabeling. Parity is the XOR of all the site values and is invariant under this action. The number of orbits of colorings of parity one is at most the number of orbits of colorings of parity zero.

Fix an element of G. If it fixes an odd coloring, pointwise XOR with that coloring is an involution on its fixed colorings and reverses parity. The odd and even fixed-point counts are then equal. If there is no odd fixed coloring, the odd fixed-point count is zero. Summing these inequalities and applying Burnside's lemma to both parity classes gives the orbit inequality after cancellation of the positive group order.

This inequality is an independent prerequisite for the parity imbalance argument when tree contexts are restored by two choices per marked slot. See https://github.com/the-omega-institute/trureturing/issues/34249#issuecomment-7174384750 and https://github.com/the-omega-institute/trureturing/issues/34249#issuecomment-7174518467.

## References

- Truth anchor: `D5/S3/Combinatorics/GroupActions/BooleanColoringOrbitParity.card_odd_orbits_le_even`
