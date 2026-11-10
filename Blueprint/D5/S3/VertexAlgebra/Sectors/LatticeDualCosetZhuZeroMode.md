# Original dual-coset bottom and all-state zero modes

## Abstract

Original dual-coset bottom and all-state zero modes

Let D be the original LatticeData: arbitrary natural rank, symmetric integral Gram matrix G and even diagonal. For the bottom and zero-mode action, assume the real Gram matrix is positive definite, take an integral charge beta and a rational vector mu with sum_j G(i,j) mu(j) = beta(i) for every i. The module is the original action(D,beta) on the full Carrier(D). No determinant-unit, positive-rank, norm-four or one-dimensional-bottom hypothesis is imposed.

**Definition 1.1 (The entire lowest rational energy fiber).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetZhuZeroMode.Bottom`

*Formalization.* `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetZhuZeroMode.Bottom` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Bottom(D,mu,hD) is rationalGrade at h = chargeWeight(D,mu,minimizingCharge(D,mu,hD)). Here chargeWeight(gamma) is one half of (gamma+mu)^T G (gamma+mu). The minimizing charge specifies the energy value only; membership retains every original label of that energy. In particular, both minimizing charges of the rank-one Gram [2], mu=1/2 example remain in the same bottom, with the two independent actual eigenvectors supplied by LatticeDualCosetEnergyEndpoints.half_shift_actual_bottom_multiplicity. This abbreviation reuses the existing rationalGrade; it does not construct a smaller ground line.

**Theorem 1.2 (Original module Borcherds supplies the residue interface).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetZhuZeroMode.module_fullLaw`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetZhuZeroMode.module_fullLaw` (`✓ std3`). ∎

*Citation.* Fedor K. Popov (2026). *Lean_VOA, full Zhu quotient algebra and original-carrier residue laws*. URL: <https://github.com/Fedor-Popov/Lean_VOA/blob/013a799ca834a8a6b3afa8129e3e522025b3f45c/VOA/Modularity/ZhuAlgebraFinite.lean>.

*Commentary.*

For every D, integral beta and unrestricted original states a,b, module_borcherds gives the fullLaw for action(a), action(b) and r mapped to action(mu(a,r,b)), with shift zero. This interface conversion requires neither positive definiteness nor a rational dual vector. Its three finite-support witnesses are kept separate for moduleLeft, moduleFirst and moduleSecond; each is transported to its corresponding residue term. Ring.map_choose identifies the original integer binomial with complex Ring.choose, and the two separately finite right supports justify distributing finsum over subtraction. fullLaw is derived, never supplied as an extra hypothesis. Both homogeneous circle and star residue arguments in LatticeDualCosetZhuRepresentation use this interface to the original module Borcherds theorem.

**Theorem 1.3 (Bottom-energy minimality kills high modes).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetZhuZeroMode.high_mode_kills_bottom`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetZhuZeroMode.high_mode_kills_bottom` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the stated positivity and dual-pairing conditions, for any integer weight k, integer mode n at least k, homogeneous original state a of weight k and any vector v in the full bottom, a_n v is zero. The actual mode-grade theorem puts a hypothetical nonzero output at rational energy h+k-n-1, strictly below h. The original moduleL eigenspace equivalence and point_spectrum_subset force that same eigenvalue to have energy h+m for a natural m. Injectivity of the rational-to-complex cast and the two order bounds give a contradiction. The proof reuses the original spectral and grading suppliers, without assuming a highest-weight annihilation law. Its consumers are both homogeneous residue arguments in the paired representation module.

**Definition 1.4 (A complex-linear zero mode on every original state).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetZhuZeroMode.zeroMode`

*Formalization.* `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetZhuZeroMode.zeroMode` (`✓ std3`).

*Citation.* Fedor K. Popov (2026). *Lean_VOA, full Zhu quotient algebra and original-carrier residue laws*. URL: <https://github.com/Fedor-Popov/Lean_VOA/blob/013a799ca834a8a6b3afa8129e3e522025b3f45c/VOA/Modularity/ZhuAlgebraFinite.lean>.

*Commentary.*

For each integer homogeneous grade k, the private consumed homogeneousZero uses the actual action coefficient k-1. Actual mode grading proves that this coefficient preserves the entire bottom since its energy shift is zero. Linearity in both state and bottom vector then gives a linear map from that grade into End_C(Bottom). DirectSum.toModule, composed with the original carrierEnergyDecomposition, assembles these maps into Carrier(D) ->_C End_C(Bottom). The original direct sum supplies finite homogeneous support; no field or state carrier is replaced.

**Theorem 1.5 (Evaluation is the original coefficient in every integer degree).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetZhuZeroMode.zeroMode_homogeneous`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetZhuZeroMode.zeroMode_homogeneous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every integer k, every original a in grade k and every bottom vector v, the underlying carrier vector of zeroMode(a)(v) is action(a) at coefficient k-1 applied to v. Negative and zero fused degrees are included. The circle and star residue arguments, the vacuum unit and representation_mk use this direct-sum evaluation law.

The source-faithful residue adaptation follows Fedor K. Popov's Lean_VOA, immutable commit 013a799ca834a8a6b3afa8129e3e522025b3f45c, VOA/Modules/ZhuModule.lean and VOA/Modules/ZeroModeMult.lean, Apache-2.0. Copyright and license notices are retained in the paired Lean source and the library reference. This is literature-attested Zhu module mathematics combined with the native lattice fields, energy decomposition and module Borcherds suppliers, without a claim of independent literature novelty. LatticeDualCosetZhuRepresentation uses the full zero mode to descend the actual action to the literal Zhu quotient; ActualZhuJointFaithful then evaluates it on every tied minimum.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetZhuZeroMode.Bottom`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetZhuZeroMode.high_mode_kills_bottom`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetZhuZeroMode.module_fullLaw`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetZhuZeroMode.zeroMode`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetZhuZeroMode.zeroMode_homogeneous`
- Dependency: [D5/S3/VertexAlgebra/Sectors/LatticeDualCosetEnergyEndpoints](LatticeDualCosetEnergyEndpoints.md)
