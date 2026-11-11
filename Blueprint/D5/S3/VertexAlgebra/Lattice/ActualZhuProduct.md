# Original-carrier Zhu star and higher circles

## Abstract

Original-carrier Zhu star and higher circles

**Definition 1.1 (Bilinear star on the complete original carrier).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/ActualZhuProduct.star`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/ActualZhuProduct.star` (`✓ std3`).

*Citation.* Fedor K. Popov (2026). *Lean_VOA, full Zhu quotient and right-ideal residues*. URL: <https://github.com/Fedor-Popov/Lean_VOA/blob/013a799ca834a8a6b3afa8129e3e522025b3f45c/VOA/Modularity/ZhuAlgebraFinite.lean>.

*Commentary.*

The original internal direct sum of all integer energy grades defines a linear map from Carrier(D) to its complex linear endomorphisms. On an integer grade p the finite formula uses p.toNat; under positive definiteness the negative grades contain only zero. No restricted vacuum-descendant carrier or additional decomposition choice is introduced.

**Theorem 1.2 (Homogeneous finite star formula).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/ActualZhuProduct.star_homogeneous`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/ActualZhuProduct.star_homogeneous` (`✓ std3`). ∎

*Citation.* Fedor K. Popov (2026). *Lean_VOA, full Zhu quotient and right-ideal residues*. URL: <https://github.com/Fedor-Popov/Lean_VOA/blob/013a799ca834a8a6b3afa8129e3e522025b3f45c/VOA/Modularity/ZhuAlgebraFinite.lean>.

*Commentary.*

For any natural p, any original state a in energy grade p and any original state b, star(a,b) is the complete sum from j=0 through p of choose(p,j) times a_(j-1)b. This finite formula is used to expand the star product in the right-argument O stability proof.

**Definition 1.3 (Full higher-circle family).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/ActualZhuProduct.higherCircle`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/ActualZhuProduct.higherCircle` (`✓ std3`).

*Citation.* Fedor K. Popov (2026). *Lean_VOA, full Zhu quotient and right-ideal residues*. URL: <https://github.com/Fedor-Popov/Lean_VOA/blob/013a799ca834a8a6b3afa8129e3e522025b3f45c/VOA/Modularity/ZhuAlgebraFinite.lean>.

*Commentary.*

The n-th higher circle of a state with natural weight M is the sum from i=0 through M+n of choose(M+n,i) times a_(i-2-n)b, on the same original carrier.

**Theorem 1.4 (Higher circles belong to the same full O).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/ActualZhuProduct.higherCircle_mem_zhuO`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/ActualZhuProduct.higherCircle_mem_zhuO` (`✓ std3`). ∎

*Citation.* Fedor K. Popov (2026). *Lean_VOA, full Zhu quotient and right-ideal residues*. URL: <https://github.com/Fedor-Popov/Lean_VOA/blob/013a799ca834a8a6b3afa8129e3e522025b3f45c/VOA/Modularity/ZhuAlgebraFinite.lean>.

*Commentary.*

For positive-definite real Gram matrix, every natural n, homogeneous original a of natural energy M, and arbitrary original b, higherCircle(M,a,b,n) belongs to ActualZhuFinite.zhuO(D). The n=0 case is literally the existing full circle. The state derivative and actual translation grading prove the recursion (n+2) P(M,a,b,n+1) = P(M+1,T a,b,n) + (M+n+1) P(M,a,b,n); induction recovers the next residue by the nonzero scalar n+2.

Source-faithful native port of Fedor K. Popov, Lean_VOA, commit 013a799ca834a8a6b3afa8129e3e522025b3f45c, VOA/Modules/ZhuModule.lean, ZhuRingResidue.lean and ZhuRightIdeal.lean; Apache-2.0, with classical Zhu/Frenkel-Zhu attribution. The local carrier, fields, grading, derivative, commutator and O-space are the existing actual lattice construction. The local port is not independent mathematical novelty.

The consuming chain establishes star(u,o) in the same full O for arbitrary original u and o in O under positive definiteness. Opposite-argument stability star(o,u) in O and associator membership (u star v) star w - u star (v star w) in O are beyond this result. A bilinear product on the quotient requires both argument stabilities; an associative quotient Ring or Algebra requires further structure. Analytic CFT, fusion, anomaly, string theory and AdS/CFT remain outside this result.

Four-slot escape registration for star_homogeneous and higherCircle_mem_zhuO is unfinished: no faithful enrolled original-statement reconstruction, scoped readout, law bridge, whole-family variation, sensitivity, actual observational dependence and source-selection/realization evidence is supplied. https://github.com/the-omega-institute/trureturing/issues/28732 tracks this product-chain audit. Neither compilation nor the linked issue establishes declared_validated registration.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/ActualZhuProduct.higherCircle`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/ActualZhuProduct.higherCircle_mem_zhuO`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/ActualZhuProduct.star`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/ActualZhuProduct.star_homogeneous`
- Dependency: [D5/S3/VertexAlgebra/Lattice/ActualZhuBinomial](ActualZhuBinomial.md)
- Dependency: [D5/S3/VertexAlgebra/Lattice/ActualZhuFinite](ActualZhuFinite.md)
