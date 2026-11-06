# Actual odd BRST derived-bracket identities

## Abstract

Actual odd BRST derived-bracket identities

All statements use the existing full lattice BRST Cohomology quotient, product, parity, and P0-reduced Delta. The bracket is the actual descended current after parity on its first input; no replacement carrier, grading, positivity, charge restriction, or generic BV record is introduced. The full matter-ghost, Q, zero-energy and second-order telescope remains in force.

The parity argument is the literal ghost occupation parity. P0 commutes with that parity on the supplied full tensor basis, while the actual antighost mode is odd. The resulting laws apply to arbitrary quotient classes, with homogeneous labels used only where the displayed Koszul signs require them.

**Theorem 1.1 (P0 commutes with actual state parity).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyOddBracket.P0_parity_commutes`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyOddBracket.P0_parity_commutes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof is diagonal on the actual fullBasis: P0 contributes the energy indicator and state parity contributes the occupation sign.

**Theorem 1.2 (Delta is odd on the actual quotient).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyOddBracket.Delta_parity`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyOddBracket.Delta_parity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every quotient class, parity (Delta a) = - Delta (parity a), proved from Delta_classOf, P0-parity commutation and the actual odd antighost mode.

**Definition 1.3 (The actual derived bracket).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyOddBracket.oddBracket`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyOddBracket.oddBracket` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

oddBracket a b is cohomologyCurrent (parity a) b. It is the existing descended current with the first quotient input parity-shifted.

**Theorem 1.4 (Parity of the descended current).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyOddBracket.cohomologyCurrent_parity`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyOddBracket.cohomologyCurrent_parity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual state-field parity law and b(-1) oddness give parity (K a b) = - K (parity a) (parity b) on the full quotient.

**Theorem 1.5 (Generator formula for the odd bracket).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyOddBracket.oddBracket_generator`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyOddBracket.oddBracket_generator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a homogeneous first class of label p, the bracket is (-1)^p Delta(ab) - (-1)^p Delta(a)b - a Delta(b), using the already proved actual product defect.

**Theorem 1.6 (Delta shifts the parity label).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyOddBracket.Delta_homogeneous`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyOddBracket.Delta_homogeneous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If a has parity label p, Delta a has label p+1, using the compiled oddness identity and the involutive sign scalar.

**Theorem 1.7 (The odd bracket has shifted homogeneous label).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyOddBracket.oddBracket_homogeneous`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyOddBracket.oddBracket_homogeneous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For homogeneous inputs with labels p and q, the actual bracket has parity label p+q+1, obtained from current parity and the two input labels.

**Theorem 1.8 (Shifted antisymmetry).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyOddBracket.oddBracket_antisymm`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyOddBracket.oddBracket_antisymm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Homogeneous labels p and q give [a,b] = -(-1)^((p+1)(q+1)) [b,a]. The even-even sector is symmetric and the cross sectors are antisymmetric under the actual quotient product signs.

**Theorem 1.9 (Odd bracket Leibniz law).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyOddBracket.oddBracket_leibniz`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyOddBracket.oddBracket_leibniz` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For homogeneous a,b and arbitrary c, [a,bc] = [a,b]c + (-1)^((p+1)q)b[a,c]. The third class is unrestricted.

These compiled identities are a formal result for the supplied lattice matter-ghost BRST quotient. The Delta compatibility identity and the shifted Jacobi identity remain open targets; the preserved implementation WIP records the intended Module.End expansion but is not kernel-checked. This delivery does not assert a nonzero bracket, a normalized unital BV structure, full string theory, spacetime reconstruction, or AdS/CFT completion. Supplier attribution remains with the existing lattice, ghost, residue, Sugawara and Mathlib sources; no literature novelty claim is made.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyOddBracket.Delta_homogeneous`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyOddBracket.Delta_parity`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyOddBracket.P0_parity_commutes`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyOddBracket.cohomologyCurrent_parity`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyOddBracket.oddBracket`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyOddBracket.oddBracket_antisymm`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyOddBracket.oddBracket_generator`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyOddBracket.oddBracket_homogeneous`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyOddBracket.oddBracket_leibniz`
- Dependency: [D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyBVSecondOrder](LatticeBRSTCohomologyBVSecondOrder.md)
