# Finite Charge Support in the Fixed Leech C2 Quotient

## Abstract

Descent in charge energy leaves finitely many fixed charge orbits spanning the quotient.

**Theorem 1.1 (Symmetrized words span the full fixed orbit).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2ChargedOrbit.fixed_charge_orbit_eq_span_words`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2ChargedOrbit.fixed_charge_orbit_eq_span_words` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Pair a word at charge c with its sign transform at -c. Such words span the fixed subspace supported on that orbit by expanding the oscillator polynomials in their monomial basis and applying the fixed projection. When c=0 the two charges coincide, and the projection retains the even words.

**Theorem 1.2 (The leading term of a quadratic mode on a charged word).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2ChargedOrbit.fixed_quadratic_charged_word_length`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2ChargedOrbit.fixed_quadratic_charged_word_length` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual neutral quadratic (-1)-mode acting on a fixed charged word has the two-letter concatenation as its leading term. In the other terms the inner nonnegative mode acts by annihilation or a charge scalar, and the outer mode creates at most one oscillator. Thus the corrections are shorter words supported on the same orbit.

**Theorem 1.3 (The ground and the single oscillators generate under quadratic modes).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2ChargedOrbit.fixed_charge_orbit_le_of_ground_and_singles`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2ChargedOrbit.fixed_charge_orbit_le_of_ground_and_singles` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A subspace containing the fixed ground and all single oscillators and stable under quadratic (-1)-modes contains the entire orbit. Induction uses the two base lengths zero and one, then creates a pair from a shorter word and subtracts the shorter corrections.

**Theorem 1.4 (The signed basis step reduces the entire fixed orbit).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2ChargedOrbit.leech_fixed_charge_orbit_step_outside_short`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2ChargedOrbit.leech_fixed_charge_orbit_step_outside_short` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any Leech charge c outside the closed Gram-coordinate box, the signed basis step gives an orbit of strictly smaller charge energy. The ground reduction into that orbit extends to all single oscillators and then to every word by quadratic stability. The entire upper orbit maps into the lower orbit image modulo intrinsic C2.

**Theorem 1.5 (The short charge orbits span the intrinsic quotient).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2ChargedOrbit.leech_fixed_c2_finite_charge_support`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2ChargedOrbit.leech_fixed_c2_finite_charge_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The short charges are exactly those satisfying |B(e_i,c)| ≤ G(i,i) for every basis direction i. The Gram-coordinate map is injective by positive definiteness, so this closed integer box gives a finite set. Strong induction on charge energy reduces each orbit image to the span of those short orbit images. Each fixed state is a finite sum of symmetrized charge components, so this span is the whole quotient.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2ChargedOrbit.fixed_charge_orbit_eq_span_words`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2ChargedOrbit.fixed_charge_orbit_le_of_ground_and_singles`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2ChargedOrbit.fixed_quadratic_charged_word_length`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2ChargedOrbit.leech_fixed_c2_finite_charge_support`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2ChargedOrbit.leech_fixed_charge_orbit_step_outside_short`
- Dependency: [D5/S3/VertexAlgebra/Lattice/ActualC2Cofinite](../ActualC2Cofinite.md)
- Dependency: [D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2ChargedOscillator](ActualFixedC2ChargedOscillator.md)
- Dependency: [D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2Projection](ActualFixedC2Projection.md)
