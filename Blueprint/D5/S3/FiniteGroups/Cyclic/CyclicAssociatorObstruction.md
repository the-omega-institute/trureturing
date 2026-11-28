# Cyclic Associator Obstruction

## Abstract

The cyclic product of an ambient associator excludes elements of nonzero carry type from subgroups that trivialize it.

**Theorem 1.1 (The cyclic product is invariant under coboundaries).**

Lean statement: `D5/S3/FiniteGroups/Cyclic/CyclicAssociatorObstruction.cyclicProduct_mul_coboundary`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/Cyclic/CyclicAssociatorObstruction.cyclicProduct_mul_coboundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite-order element g, multiply the values of a three-cochain α at (g,g^i,g) for i from zero through orderOf(g) minus one. With trivial action on an abelian multiplicative coefficient group, each of the two coboundary ratios telescopes by rotating i by one. The product is therefore invariant under multiplication by the coboundary of an arbitrary two-cochain.

**Theorem 1.2 (The cyclic product gives the type phase).**

Lean statement: `D5/S3/FiniteGroups/Cyclic/CyclicAssociatorObstruction.cyclicProduct_eq_type_phase`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/Cyclic/CyclicAssociatorObstruction.cyclicProduct_eq_type_phase` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let g and ζ both have exact order n greater than one. Assume the pullback of α along a ↦ g^a.val equals the carry phase of type t times a two-cochain coboundary. The carry phase is ζ raised to the least nonnegative representative of w(t,a,b,c). Telescoping removes the coboundary, and summing the carry exponents modulo n gives t. Thus the cyclic product is ζ raised to t.val. For ζ = exp(2πi/n), the carry phase is equation (2.13) of Evans–Gannon, arXiv:1804.11145v1.

**Theorem 1.3 (Nonzero type excludes subgroup membership).**

Lean statement: `D5/S3/FiniteGroups/Cyclic/CyclicAssociatorObstruction.not_mem_of_nonzero_type`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/Cyclic/CyclicAssociatorObstruction.not_mem_of_nonzero_type` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the ambient α restricts to a two-cochain coboundary on a subgroup H, every g in H has cyclic product one. Under the pullback comparison, exact order n of ζ makes this impossible for nonzero t in ZMod n. Both two-cochains are arbitrary.

Evans–Gannon, arXiv:1804.11145v1, equation (2.14), gives the generator-flux conformal weight ρ congruent to t/n² modulo 1/n after removing the central-charge term from the T phase. For the c = 48 P48q order-three case, a weight in 16/9 + (1/3)ℤ gives type 1 in this convention. Applying the obstruction to a group or VOA requires an external comparison of the actual ambient associator on the cyclic generator with the carry phase up to coboundary. Corollary 2 supplies the coboundary restriction condition for the extension subgroups in the Evans–Gannon setting.

## References

- Truth anchor: `D5/S3/FiniteGroups/Cyclic/CyclicAssociatorObstruction.cyclicProduct_eq_type_phase`
- Truth anchor: `D5/S3/FiniteGroups/Cyclic/CyclicAssociatorObstruction.cyclicProduct_mul_coboundary`
- Truth anchor: `D5/S3/FiniteGroups/Cyclic/CyclicAssociatorObstruction.not_mem_of_nonzero_type`
- Dependency: [D5/S3/FiniteGroups/Cyclic/CyclicCarryThreeCocycle](CyclicCarryThreeCocycle.md)
