# C2 Cofiniteness of the Actual Positive-Definite Lattice VOA

## Abstract

A positive-definite even lattice has finite-dimensional quotient by the literal actual C2 span.

Let D be any original LatticeData, including rank zero, with integral symmetric Gram matrix and even diagonal. Charges are Charge(D)=Fin(rank(D)) -> Z, oscillators are complex polynomials in Index(D)=Fin(rank(D)) x N, and Carrier(D) is the finite-support charge sum of those polynomials. ActualC2.C2(D) is the literal complex span of mu(D,a,-2,b) for all original carrier states a and b. Assume only that the real cast of G is positive definite.

For a charge delta, sectorIdeal(D,delta) consists of oscillator polynomials p whose literal single(delta,p) lies in ActualC2.C2(D). The proof makes it an ideal using actual minus-one multiplication and all higher neutral modes. Creation coefficients satisfy the ground-field relation, and the consumed exponential derivation gives the Newton reduction of every chargePolynomial(D,alpha)^d modulo this ideal. Each X(i,0) is therefore nilpotent in a sector quotient, while every X(i,k) with k>0 vanishes.

**Definition 1.1 (The oscillator ideal in one charge sector).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/ActualC2Cofinite.sectorIdeal`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/ActualC2Cofinite.sectorIdeal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Fedor K. Popov (2026). *Lean_VOA, Classification/COne/LatticeC2.lean*. URL: <https://github.com/Fedor-Popov/Lean_VOA/blob/013a799ca834a8a6b3afa8129e3e522025b3f45c/VOA/Classification/COne/LatticeC2.lean>.

*Commentary.*

sectorIdeal(D,delta) is the ideal of oscillator polynomials p for which the original basis state single(delta,p) belongs to the literal actual C2 span. Its closure is proved from the actual neutral minus-one and higher-mode suppliers, not from a replacement quotient or an assumed generic interface.

**Definition 1.2 (The actual quotient map of one charge sector).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/ActualC2Cofinite.sectorMap`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/ActualC2Cofinite.sectorMap` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Fedor K. Popov (2026). *Lean_VOA, Classification/COne/LatticeC2.lean*. URL: <https://github.com/Fedor-Popov/Lean_VOA/blob/013a799ca834a8a6b3afa8129e3e522025b3f45c/VOA/Classification/COne/LatticeC2.lean>.

*Commentary.*

sectorMap(D,delta) sends an oscillator polynomial p to the quotient class of the original state single(delta,p) in Carrier(D) / ActualC2.C2(D). Its range is finite-generated once the sector ideal quotient is finite-dimensional.

**Definition 1.3 (The closed finite charge box).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/ActualC2Cofinite.shortCharges`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/ActualC2Cofinite.shortCharges` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Fedor K. Popov (2026). *Lean_VOA, Classification/COne/LatticeC2.lean*. URL: <https://github.com/Fedor-Popov/Lean_VOA/blob/013a799ca834a8a6b3afa8129e3e522025b3f45c/VOA/Classification/COne/LatticeC2.lean>.

*Commentary.*

shortCharges(D) is the set of charges delta satisfying |B(e_i,delta)| <= G_ii for every basis index i. Positive definiteness makes the Gram-coordinate map injective, so this closed integer box is finite. A charge outside it has sectorIdeal(D,delta)=top; the boundary is retained.

The port follows Fedor K. Popov's Lean_VOA source at commit 013a799ca834a8a6b3afa8129e3e522025b3f45c. Dong, Li, and Mason, arXiv:math/0102127v1, DOI 10.1090/conm/297/05093, pp. 24–26, (5.22)–(5.26), Lemma 5.18, and Proposition 5.19 give the classical C2 finite-generation mechanism. The local proof retains the Popov Apache-2.0 attribution and uses the repository's actual state-field and carrier declarations.

**Theorem 1.4 (Finite-dimensionality of the literal actual C2 quotient).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/ActualC2Cofinite.positive_definite_c2_cofinite`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/ActualC2Cofinite.positive_definite_c2_cofinite` (`✓ std3`). ∎

*Citation.* Fedor K. Popov (2026). *Lean_VOA, Classification/COne/LatticeC2.lean*. URL: <https://github.com/Fedor-Popov/Lean_VOA/blob/013a799ca834a8a6b3afa8129e3e522025b3f45c/VOA/Classification/COne/LatticeC2.lean>.

*Commentary.*

For every LatticeData D and hD:PosDef(D.G.map(Int.cast : Z -> R), the quotient Carrier(D) / ActualC2.C2(D) is finite-dimensional over C. The proof sums the finite ranges of sectorMap over the finite closed short-charge box. It includes rank zero, all charge fibers, all oscillator degrees, and zero exponents; it assumes no determinant-unit or unimodularity condition.

This is algebraic C2 cofiniteness for the literal constructed carrier and state field. It does not prove a full conformal field theory, anomaly cancellation, fusion completeness, string-theory consistency, or an AdS/CFT correspondence.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/ActualC2Cofinite.positive_definite_c2_cofinite`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/ActualC2Cofinite.sectorIdeal`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/ActualC2Cofinite.sectorMap`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/ActualC2Cofinite.shortCharges`
- Dependency: [D5/S3/VertexAlgebra/Lattice/ActualC2](ActualC2.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeActualConformalState](../LatticeActualConformalState.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeFiniteNegativeGeneration](../LatticeFiniteNegativeGeneration.md)
