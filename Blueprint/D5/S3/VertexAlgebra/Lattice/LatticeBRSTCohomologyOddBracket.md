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

If a has parity label p, Delta a has label p+1, using the preceding oddness identity and the involutive sign scalar.

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

**Theorem 1.10 (Delta compatibility of the actual current).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyOddBracket.cohomologyCurrent_delta`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyOddBracket.cohomologyCurrent_delta` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary quotient classes, Delta(K(a,b)) = -K(Delta(a),b) - K(parity(a),Delta(b)). The proof expands the actual all-class product defect and uses Delta squared zero. Both cross products are retained until Delta(parity(a)) = -parity(Delta(a)) cancels them.

**Theorem 1.11 (Delta compatibility of the actual bracket).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyOddBracket.Delta_bracket`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyOddBracket.Delta_bracket` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary a,b, Delta([a,b]) = [Delta(a),b] - [parity(a),Delta(b)]. This follows from current compatibility and the literal definition [a,b] = K(parity(a),b); neither input is required to be homogeneous.

**Theorem 1.12 (Shifted Jacobi on the full quotient).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyOddBracket.oddBracket_jacobi`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyOddBracket.oddBracket_jacobi` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For homogeneous a,b with labels p,q and arbitrary c, [a,[b,c]] = [[a,b],c] + (-1)^((p+1)(q+1))[b,[a,c]]. The proof uses left multiplication and bracket endomorphisms of the original quotient, the supplied current Leibniz law, and Delta compatibility. Its private commutator calculation yields the operator identity T(a)T(b) - (-1)^((p+1)(q+1))T(b)T(a) = T([a,b]), which is evaluated on unrestricted c.

The parity labels express only the supplied parity grading. The long-term programme remains the formalization of VOA, conformal field theory, anomalies and fusion, towards string theory and AdS/CFT; these identities do not establish that programme, a nonzero bracket, or spacetime reconstruction. Supplier attribution remains with the existing lattice, ghost, residue, Sugawara and Mathlib sources; no literature novelty claim is made.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyOddBracket.Delta_bracket`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyOddBracket.Delta_homogeneous`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyOddBracket.Delta_parity`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyOddBracket.P0_parity_commutes`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyOddBracket.cohomologyCurrent_delta`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyOddBracket.cohomologyCurrent_parity`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyOddBracket.oddBracket`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyOddBracket.oddBracket_antisymm`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyOddBracket.oddBracket_generator`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyOddBracket.oddBracket_homogeneous`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyOddBracket.oddBracket_jacobi`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyOddBracket.oddBracket_leibniz`
- Dependency: [D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyBVSecondOrder](LatticeBRSTCohomologyBVSecondOrder.md)
