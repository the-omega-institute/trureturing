# The full actual Zhu algebra acts on the entire dual-coset bottom

## Abstract

The full actual Zhu algebra acts on the entire dual-coset bottom

Let D be the original lattice data of arbitrary natural rank, with symmetric integral Gram matrix G and even diagonal, and assume its real Gram matrix is positive definite. Let beta be an integral charge and mu a rational vector satisfying sum_j G(i,j) mu(j) = beta(i) for every i. Every result here uses these original parameters and the original module action(D,beta). Bottom is the entire rational energy fiber at the attained global minimum of one half of (gamma+mu)^T G (gamma+mu), including all minimizing charges. Rank zero and the rank-one half-shift bottom with two independent eigenvectors are retained; there is no determinant-unit, positive-rank, norm-four or one-dimensional-bottom restriction.

**Theorem 1.1 (Every original full circle generator acts by zero).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetZhuRepresentation.zeroMode_circle`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetZhuRepresentation.zeroMode_circle` (`✓ std3`). ∎

*Citation.* Fedor K. Popov (2026). *Lean_VOA, full Zhu quotient algebra and original-carrier residue laws*. URL: <https://github.com/Fedor-Popov/Lean_VOA/blob/013a799ca834a8a6b3afa8129e3e522025b3f45c/VOA/Modularity/ZhuAlgebraFinite.lean>.

*Commentary.*

For every natural p, homogeneous original a of weight p and unrestricted original b, the zero mode of NormFourZhuFinite.circle(D,p,a,b) vanishes. Despite the supplier's name, this circle is the full binomial sum of choose(p,j) times the actual mode mu(a,j-2,b), with no norm-four restriction on a or b. In the consumed private circle_homogeneous proof, actual mode grading identifies its zero-mode indices as p+q-j. Core.circle_residue_top is applied to module_fullLaw derived from the original module Borcherds and to high_mode_kills_bottom for both inputs. The latter discharges the actual bottom truncations from energy minimality. Decomposing the unrestricted second state into its existing finite nonnegative gradeProjection sum extends the homogeneous residue identity to every b. This is the residue argument used for annihilation of the literal span, not an assumed circle-action law.

**Theorem 1.2 (The literal full O is contained in the zero-mode kernel).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetZhuRepresentation.zhuO_le_kernel`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetZhuRepresentation.zhuO_le_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Submodule.span_le extends zeroMode_circle to ActualZhuFinite.zhuO(D), the existing span of all full circle generators with unrestricted second state. The conclusion is O <= ker(zeroMode). It proves neither kernel equality nor faithfulness, and does not define O by a representation kernel. The representation descends this linear map by the proved kernel containment.

**Theorem 1.3 (Multiplication of zero modes for all original states).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetZhuRepresentation.zeroMode_star`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetZhuRepresentation.zeroMode_star` (`✓ std3`). ∎

*Citation.* Fedor K. Popov (2026). *Lean_VOA, full Zhu quotient algebra and original-carrier residue laws*. URL: <https://github.com/Fedor-Popov/Lean_VOA/blob/013a799ca834a8a6b3afa8129e3e522025b3f45c/VOA/Modularity/ZhuAlgebraFinite.lean>.

*Commentary.*

For unrestricted original a,b, zeroMode(star(a,b)) equals zeroMode(a) times zeroMode(b), with multiplication in Module.End given by composition. The consumed private star_homogeneous_zeroMode uses the existing star_homogeneous expansion and actual grading to obtain indices p+q-1-j. Core.star_residue_top consumes the derived original-module fullLaw and both minimal-energy high-mode vanishings, yielding the composition identity. The existing finite energy decompositions of both original states, complex linearity and the finite product-of-sums identity extend this result to every state. Product compatibility is proved; it is not supplied by an assumed algebra action. The generic residue suppliers and the converted interfaces are reused, rather than independently published as new helpers.

**Theorem 1.4 (The original vacuum acts as the identity).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetZhuRepresentation.zeroMode_vacuum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetZhuRepresentation.zeroMode_vacuum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The vacuum is in grade zero. zeroMode_homogeneous and the original module_vacuum identity field identify its coefficient minus one with the identity on the full bottom. The representation uses this identity as its unit law.

**Definition 1.5 (A unital complex algebra homomorphism from the original Zhu quotient).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetZhuRepresentation.representation`

*Formalization.* `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetZhuRepresentation.representation` (`✓ std3`).

*Citation.* Fedor K. Popov (2026). *Lean_VOA, full Zhu quotient algebra and original-carrier residue laws*. URL: <https://github.com/Fedor-Popov/Lean_VOA/blob/013a799ca834a8a6b3afa8129e3e522025b3f45c/VOA/Modularity/ZhuAlgebraFinite.lean>.

*Commentary.*

Using the existing ActualZhuAlgebra.quotientRing and quotientAlgebra, representation is an AlgHom from Q(D) = Carrier(D) modulo ActualZhuFinite.zhuO(D) to End_C(Bottom). The original quotient linear lift is justified by zhuO_le_kernel. AlgHom.ofLinearMap uses the proved vacuum unit and zeroMode_star; quotient surjectivity and quotientProduct_mk reduce multiplication to original representatives. The two ideal stabilities and quotient associativity are already proved suppliers of ActualZhuAlgebra, not new premises. This is the actual descended action on the same carrier quotient and literal O.

**Theorem 1.6 (Full-family evaluation on original homogeneous representatives).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetZhuRepresentation.representation_mk`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetZhuRepresentation.representation_mk` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every integer k, every original a in grade k and every v in the full bottom, the underlying carrier vector of representation([a])(v) equals the coefficient k-1 of the original module field action(a) applied to v. This evaluation theorem retains the entire original parameter telescope; zeroMode_homogeneous supplies this evaluation identity for the constructed action.

The residue construction follows Zhu/Frenkel--Zhu mathematics and the source-faithful Lean adaptation of Fedor K. Popov, Lean_VOA commit 013a799ca834a8a6b3afa8129e3e522025b3f45c, VOA/Modules/ZhuModule.lean and VOA/Modules/ZeroModeMult.lean, Apache-2.0. The native Core residue calculus, Mathlib quotient descent, actual fields, module Borcherds and energy suppliers retain their existing ownership. ActualZhuJointFaithful evaluates this representation on the complete native minimum basis, proves joint injectivity directly from its scalar matrix coefficients and obtains the sharp dimension equality. Nontriviality and finite dimension of the bottom are supplied by the original bottom_eigenvector, moduleL_eigen_iff and all_eigenspaces_finiteDimensional theorems. No irreducibility or rationality hypothesis is used.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetZhuRepresentation.representation`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetZhuRepresentation.representation_mk`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetZhuRepresentation.zeroMode_circle`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetZhuRepresentation.zeroMode_star`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetZhuRepresentation.zeroMode_vacuum`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetZhuRepresentation.zhuO_le_kernel`
- Dependency: [D5/S3/VertexAlgebra/Lattice/ActualZhuAlgebra](../Lattice/ActualZhuAlgebra.md)
- Dependency: [D5/S3/VertexAlgebra/Sectors/LatticeDualCosetZhuZeroMode](LatticeDualCosetZhuZeroMode.md)
