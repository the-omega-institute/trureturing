# LatticeLightConeCoordinates

## Abstract

Original lattice light-cone algebra

The complex bilinear coordinate change preserves the original integral labels, oscillator variables and carrier. It supplies algebraic tools for later quartet calculations; it does not prove a BRST contraction or any no-ghost or string endpoint. Classical lattice-current context is Bakalov--Kac, arXiv math/0402315v1, section 4.1; the source-level coordinate construction and transport proofs are supplied here.

**Definition 1.1 (NullFrame.frameEquiv).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeLightConeCoordinates.frameEquiv`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeLightConeCoordinates.frameEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A frame consists only of two actual vectors with g(ePlus,ePlus)=g(eMinus,eMinus)=0 and g(ePlus,eMinus)=1. The explicitly proved linear equivalence sends v in the original E D to (g(eMinus,v),g(ePlus,v),projK(v)), with inverse a ePlus + b eMinus + k. K is the actual simultaneous kernel of the two Gram pairings.

**Definition 1.2 (polynomialEquiv).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeLightConeCoordinates.polynomialEquiv`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeLightConeCoordinates.polynomialEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every genuine finite basis b of the original complex space E D, frequencywise linear variable substitution and its explicit inverse give an algebra equivalence from the original Oscillator D. Both inverse laws are proved on variables; no transport certificate is a premise.

**Theorem 1.3 (NullFrame.vector_substitution).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeLightConeCoordinates.vector_substitution`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeLightConeCoordinates.vector_substitution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D, null frame F, t, actual basis B of F.K, original vector v and frequency index r, the image of lin(r,v) is g(eMinus,v) X(plus,r)+g(ePlus,v) X(minus,r)+the B-coordinates of projK(v) in the transverse variables.

For every actual frame and transverse basis, the inverse sends the plus and minus variables to lin(r,ePlus) and lin(r,eMinus), and the jth transverse variable to lin(r,B(j)) in the original polynomial algebra.

**Theorem 1.4 (NullFrame.creation_plus).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeLightConeCoordinates.creation_plus`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeLightConeCoordinates.creation_plus` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original integral charge p, r and polynomial P, a(ePlus,-r-1) becomes multiplication by X(plus,r).

**Theorem 1.5 (NullFrame.creation_minus).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeLightConeCoordinates.creation_minus`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeLightConeCoordinates.creation_minus` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original integral charge p, r and polynomial P, a(eMinus,-r-1) becomes multiplication by X(minus,r).

**Theorem 1.6 (NullFrame.annihilation_minus).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeLightConeCoordinates.annihilation_minus`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeLightConeCoordinates.annihilation_minus` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original integral charge p, r and polynomial P, a(eMinus,r+1) becomes (r+1) times partial differentiation in X(plus,r). The Gram pairing swaps the longitudinal derivative directions.

**Theorem 1.7 (NullFrame.annihilation_plus).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeLightConeCoordinates.annihilation_plus`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeLightConeCoordinates.annihilation_plus` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original integral charge p, r and polynomial P, a(ePlus,r+1) becomes (r+1) times partial differentiation in X(minus,r).

For every original integral charge p and P, the ePlus zero mode acts by pPlus(p)=g(ePlus,chargeVector(p)), with no nonzero-charge assumption needed for this identity.

For every original integral charge p and P, the eMinus zero mode acts by pMinus(p)=g(eMinus,chargeVector(p)).

**Theorem 1.8 (NullFrame.creation_K).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeLightConeCoordinates.creation_K`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeLightConeCoordinates.creation_K` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every k in the actual K, original charge p, r and P, the negative current is multiplication by the sum of B-coordinates of k times the original-frequency transverse variables.

**Theorem 1.9 (NullFrame.annihilation_K).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeLightConeCoordinates.annihilation_K`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeLightConeCoordinates.annihilation_K` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every k in the actual K, original charge p, r and P, the positive current is (r+1) times the sum of g(k,B(j)) times transverse partial derivatives. The transverse basis need not be orthogonal or integral.

**Theorem 1.10 (NullFrame.original_carrier_all_charges).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeLightConeCoordinates.original_carrier_all_charges`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeLightConeCoordinates.original_carrier_all_charges` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original complex direction u, integer m and original finite-charge state v, allChargeEquiv intertwines the actual original current a(u,m) with the explicitly constructed chargewise coordinateMode. The support index remains exactly Charge D.

**Theorem 1.11 (NullFrame.frequency_grading).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeLightConeCoordinates.frequency_grading`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeLightConeCoordinates.frequency_grading` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original D, F, actual basis B of F.K, P and natural n, the transformed polynomial is homogeneous of frequency n if and only if P is homogeneous for the original oscillatorWeight D. Each original variable (i,r) retains weight r+1 in both substitutions.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeLightConeCoordinates.annihilation_K`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeLightConeCoordinates.annihilation_minus`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeLightConeCoordinates.annihilation_plus`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeLightConeCoordinates.creation_K`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeLightConeCoordinates.creation_minus`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeLightConeCoordinates.creation_plus`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeLightConeCoordinates.frameEquiv`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeLightConeCoordinates.frequency_grading`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeLightConeCoordinates.original_carrier_all_charges`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeLightConeCoordinates.polynomialEquiv`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeLightConeCoordinates.vector_substitution`
- Dependency: [D5/S3/VertexAlgebra/LatticeSugawaraCurrents](../LatticeSugawaraCurrents.md)
