# Normalized additive lattice fusion and scalar equivalence

## Abstract

LatticeDualCosetFusion

**Theorem 1.1 (canonical_lawful).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetFusion.canonical_lawful`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetFusion.canonical_lawful` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary positive-definite even integral original D, every raw integral dual labels a,b and every explicit two-sided complex Gram inverse H, specialize the canonical external rank to D.rank and cross block to identity. Matrix.one_mulVec reduces the source, input and additive target actions to exactly a,b,a+b. LinearMap.ext supplies literal Lawful.source and Lawful.target; the full mixed_jacobi supplies all h,u,v,p,r,tau and all three finite supports, using exactly integerBinomial and residue epsilon. These identities are the membership proof of canonicalOperator in the existing Lawful submodule.

**Definition 1.2 (canonicalOperator).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetFusion.canonicalOperator`

*Formalization.* `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetFusion.canonicalOperator` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This constructs a member of the existing LatticeDualCosetIntertwiner.operatorSpace D a b H, with canonical_lawful as its membership proof. No positivity of the ambient block or restriction on rank is added.

**Theorem 1.3 (shift_eq_groundPower).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetFusion.shift_eq_groundPower`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetFusion.shift_eq_groundPower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary rational mu,nu satisfying sum_j G_ij mu_j=a_i and sum_j G_ij nu_j=b_i, the identity-cross-block canonical shift equals groundPower D mu nu 0 0, hence pairing D mu nu. The original shift_pair and pairRaw symmetry reduce to dualVector(a) dot b; the original rational inverse and rat_unit give inverse uniqueness dualVector(a)=mu; the second Gram equation gives the energy pairing. It aligns the coefficient used by canonical_groundEvaluation. Arbitrary Gram solutions remain explicit; no canonical-dual-only premise is substituted.

**Theorem 1.4 (canonical_groundEvaluation).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetFusion.canonical_groundEvaluation`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetFusion.canonical_groundEvaluation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With positivity, both inverse equations and both rational Gram equations, groundEvaluation of canonicalOperator is exactly one, at raw q=pairing D mu nu and mode -q-1. The source and input are ground D 0, literally the original vacuum; constantCoeff is coeff zero at old charge zero. This normalization proves the left inverse of scalarEquiv.

**Definition 1.5 (scalarInclusion).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetFusion.scalarInclusion`

*Formalization.* `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetFusion.scalarInclusion` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The complex linear map from scalars to the exact lawful submodule sends z to z times canonicalOperator. Its private injectivity proof uses the actual canonical intertwiner_ne_zero. That injectivity is used in the right-inverse proof of scalarEquiv.

**Definition 1.6 (scalarEquiv).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetFusion.scalarEquiv`

*Formalization.* `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetFusion.scalarEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The complex linear equivalence has domain operatorSpace D a b H and codomain C. Its forward linear map is definitionally the already proved groundEvaluation D a b H mu nu. Its inverse is definitionally scalarInclusion, z maps to z times the normalized canonical lawful field. The left inverse uses the existing groundEvaluation_injective and the proved normalization; injectivity of scalar inclusion proves the right inverse. Hypotheses are precisely positive definiteness of the original integral even D, both inverse equations for H and both rational Gram equations for arbitrary mu,nu. Empty Fin 0 matrix products, sums, charges and oscillator arguments remain valid; there is no Nonempty (Fin D.rank), positive rank, categorical or physical premise. The result integrates classical existence and rigidity; it makes no novelty claim.

Classical conventions: Bakalov--Kac, math/0402315v1, section 4.1. Native residue and conformal sources retain Scott Carnahan and Kalle Kytölä attributions. No mathematical novelty, physical realization, categorical fusion completion or string completion is claimed. The original rank may be zero; all external-rank statements also include zero.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetFusion.canonicalOperator`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetFusion.canonical_groundEvaluation`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetFusion.canonical_lawful`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetFusion.scalarEquiv`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetFusion.scalarInclusion`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetFusion.shift_eq_groundPower`
- Dependency: [D5/S3/VertexAlgebra/Sectors/LatticeCosetCanonicalLaws](LatticeCosetCanonicalLaws.md)
