# Ground Charge Descent in the Fixed Lattice Quotient

## Abstract

Fixed ground modes and neutral zero modes reduce charges and first oscillators.

The first-oscillator calculation uses the actual neutral quadratic zero modes and translation, following the rank-one calculations of Yamskulna (arXiv:math/0202056, section 4).

**Theorem 1.1 (A ground class equals a creation class on the other orbit).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2GroundCharge.fixed_ground_two_orbit_relation`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2GroundCharge.fixed_ground_two_orbit_relation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write s for the Gram pairing of a and b and assume s>0. The actual mode at -s-1 of the two fixed ground states has two terms with the same nonzero cocycle factor. The orbit of a+b contributes its ground state, while the orbit of a-b contributes its paired creation coefficient of index 2s. The mode lies in intrinsic C2, so the ground class is the negative of that creation class.

**Theorem 1.2 (A signed basis step lowers the charge energy).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2GroundCharge.fixed_ground_charge_step_outside_short`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2GroundCharge.fixed_ground_charge_step_outside_short` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If a charge γ is outside the closed box defined by |B(e_i,γ)| ≤ G(i,i), choose a signed basis charge a in a violated direction so B(a,γ) is positive. Set s = |B(e_i,γ)| - G(i,i) and δ = γ - 2a. The ground class at γ becomes the negative of the paired creation class at δ, of index 2s with creation direction -a on δ. The squared norm drops by 4s and the charge energy by 2s. Positive definiteness gives nonnegative energy, so this is a strict decrease on natural-valued energies.

**Theorem 1.3 (Fixed zero modes preserve the intrinsic C2 span).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2GroundCharge.fixed_zero_mode_mem_c2`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2GroundCharge.fixed_zero_mode_mem_c2` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the commutator of a fixed zero mode with a (-2)-mode, the binomial sum keeps only its index-zero term. The zero mode applied to a C2 generator therefore gives two fixed (-2)-products, one from acting on each factor. Linearity extends preservation to the whole span.

**Theorem 1.4 (Neutral zero modes isolate the first charged oscillator).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2GroundCharge.fixed_first_oscillator_class`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2GroundCharge.fixed_first_oscillator_class` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The quadratic with basis directions i and j acts on the ground by two terms, each a Gram pairing times a first oscillator. Weight by the j-th coordinate of the charge and sum over j. One term gives the squared norm times the first oscillator in direction i. The other is proportional to translation of the ground and vanishes in fixed C2. For nonzero norm, division expresses the first oscillator class in terms of actual zero modes.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2GroundCharge.fixed_first_oscillator_class`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2GroundCharge.fixed_ground_charge_step_outside_short`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2GroundCharge.fixed_ground_two_orbit_relation`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2GroundCharge.fixed_zero_mode_mem_c2`
- Dependency: [D5/S3/VertexAlgebra/Lattice/ActualC2Cofinite](../ActualC2Cofinite.md)
- Dependency: [D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2NeutralMonomials](ActualFixedC2NeutralMonomials.md)
- Dependency: [D5/S3/VertexAlgebra/Lattice/NormFourFixedPeirce](../NormFourFixedPeirce.md)
