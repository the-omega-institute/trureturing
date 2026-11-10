# Finite Binomial Change of Basis

## Abstract

The finite signed binomial change of basis in Zhu's associativity argument.

**Definition 1.1 (Coefficients in the shifted basis).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/ActualZhuMuIdentity.muCoeff`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/ActualZhuMuIdentity.muCoeff` (`✓ std3`).

*Citation.* Fedor K. Popov (2026). *Lean_VOA, full Zhu quotient, right-ideal residues and associator*. URL: <https://github.com/Fedor-Popov/Lean_VOA/blob/013a799ca834a8a6b3afa8129e3e522025b3f45c/VOA/Modularity/ZhuAlgebraFinite.lean>.

*Commentary.*

For natural L, b, n, muCoeff(L,b,n) is the sum over n <= kk <= b of (-1)^(kk-n) C(L,b-kk) C(kk,n). Here C(r,j) is the existing integerBinomial(r,j.toNat) when the integer j is nonnegative, and zero otherwise. Every subtraction in a binomial lower index is integer subtraction. An empty interval contributes zero.

**Theorem 1.2 (Exact finite basis transformation).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/ActualZhuMuIdentity.mu_identity`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/ActualZhuMuIdentity.mu_identity` (`✓ std3`). ∎

*Citation.* Fedor K. Popov (2026). *Lean_VOA, full Zhu quotient, right-ideal residues and associator*. URL: <https://github.com/Fedor-Popov/Lean_VOA/blob/013a799ca834a8a6b3afa8129e3e522025b3f45c/VOA/Modularity/ZhuAlgebraFinite.lean>.

*Commentary.*

For every natural K, L, b and every integer s, the sum for 0 <= k <= b of C(K,s+k) C(L,b-k) equals the sum for 0 <= n <= b of muCoeff(L,b,n) C(K+n,s+n). Negative s, zero parameters, and lower indices outside the natural upper index are included.

The proof uses mathlib's finite-difference expansion. Pascal's recurrence extends across all integer lower indices by treating j < -1, j = -1, and j >= 0 separately. Each forward difference of m -> C(K+m,s+m) increases the lower offset by one. Induction therefore collapses its alternating binomial transform to C(K,s+kk). Expanding muCoeff, exchanging the two finite sums, and removing the zero terms n > kk gives the stated identity.

This is a source-faithful adaptation of Fedor K. Popov's Apache-2.0 VOA/Modules/ZhuMuIdentity.lean, ZhuMu.muCoeff and ZhuMu.mu_identity, at https://github.com/Fedor-Popov/Lean_VOA/blob/013a799ca834a8a6b3afa8129e3e522025b3f45c/VOA/Modules/ZhuMuIdentity.lean. The upstream file SHA256 is d5331d266fde48898921d23a276b1ced5af9d39e46f52132fea357543797385d. The local implementation uses native Ring.choose and mathlib forward differences. Upstream uses Lean v4.30.0 and mathlib c5ea00351c28e24afc9f0f84379aa41082b1188f; this native port uses Lean v4.35.0 and mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679. This is literature-attested, with no claim of independent mathematical novelty. The classical mathematical sources are Zhu's associativity theorem and the work of Frenkel and Zhu.

ActualZhuAssociator.Ufam_inner consumes mu_identity to identify the finite higher-circle tower; its swapped-parameter use also supplies Vfam_inner. Both paths reach assoc_eq and associator_mem_zhuO. The coefficients and scalar identity are supplied with that consumer, with no separate scalar delivery.

Four-slot escape registration for mu_identity is unfinished under https://github.com/the-omega-institute/trureturing/issues/28745. Missing evidence is a faithful typed reconstruction and equivalence for the full K,L,b : Nat and s : Int telescope, a lawful enrolled-template readout and actual-positive law, whole-family intervention and sensitivity, and actual observational dependence, including zero and negative-index boundary fibres. No declared_validated registration is asserted.

The result is a finite scalar identity. It supplies coefficients for an associator argument and establishes no quotient multiplication, O-space stability, VOA associativity, analytic CFT, string theory, or AdS/CFT statement by itself.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/ActualZhuMuIdentity.muCoeff`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/ActualZhuMuIdentity.mu_identity`
- Dependency: [D5/S3/VertexAlgebra/StateFieldResidueReconstruction](../StateFieldResidueReconstruction.md)
