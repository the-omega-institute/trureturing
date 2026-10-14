/- GID: D5/S3/VertexAlgebra/OriginalChargedGround
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/OriginalChargedGround
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native charged c1 ground states and the original BRST mass-shell cancellation. -/

import D5.S3.VertexAlgebra.OriginalCartanFaithfulness
import D5.S3.VertexAlgebra.LatticeActualOrderedProducts
import D5.S3.VertexAlgebra.LatticeTwistedGroundRealization

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

noncomputable section

namespace D5.S3.VertexAlgebra.OriginalChargedGround

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeSugawaraConformal
open LatticeSugawaraVirasoro LatticeBcGhostBrstCharge BcGhostFockSupport
open OriginalZeroChargeBrstAction OriginalBrstReassembly
open OriginalCartanOperator OriginalCartanCohomology
open scoped BigOperators TensorProduct VertexOperator

def ground (D : LatticeData) (charge : Charge D) : State D :=
  Finsupp.single charge (1 : Oscillator D) ⊗ₜ[ℂ] Finsupp.single {1} 1

private theorem c_high (mode : ℤ) (positive : 1 < mode) :
    c (K := ℂ) mode (Finsupp.single {1} 1) = 0 := by
  have different : 2 * (mode - 2).toNat ≠ 1 := by omega
  simp [c, show ¬ mode ≤ 1 by omega, annihilate,
    Finsupp.linearCombination_single, annihilateBasis, different]

theorem ground_Q (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftInverse : H * gramComplex D = 1) (rightInverse : gramComplex D * H = 1)
    (charge : Charge D) (normTwo : bilinear D charge charge = 2) :
    Q D H (ground D charge) = 0 := by
  classical
  have energy : chargeQuadratic D H charge = 1 := by
    rw [chargeQuadratic_eq D H leftInverse rightInverse, normTwo]
    norm_num
  rw [ground, Q_tmul_split]
  have matterSum :
      (∑ᶠ mode : ℤ,
        sugawaraMode D H mode (Finsupp.single charge (1 : Oscillator D)) ⊗ₜ[ℂ]
          c (K := ℂ) (-mode) (Finsupp.single {1} 1)) =
      Finsupp.single charge (1 : Oscillator D) ⊗ₜ[ℂ]
        c (K := ℂ) 0 (Finsupp.single {1} 1) := by
    rw [finsum_eq_single _ 0]
    · simp [sugawaraMode_ground_zero, energy]
    · intro mode nonzero
      by_cases positive : 0 < mode
      · rw [sugawaraMode_ground_positive D H charge mode positive]
        simp
      by_cases minusOne : mode = -1
      · subst mode
        norm_num [c, create, createBasis]
      · rw [c_high (-mode) (by omega)]
        simp
  rw [matterSum, ghostDoubleSum_nonpositive {1} (by decide)]
  norm_num [c, create, createBasis, sign, Finset.filter_insert,
    Finset.filter_singleton, ← TensorProduct.tmul_smul, TensorProduct.tmul_neg,
    smul_smul, Finsupp.smul_single,
    show ({3, 1} : Finset ℕ) = {1, 3} from by decide]

#print axioms ground_Q

theorem ground_B0 (D : LatticeData) (charge : Charge D) :
    B D 0 (ground D charge) = 0 := by
  simp only [ground, B, TensorProduct.map_tmul, LinearMap.id_apply]
  norm_num [b, annihilate, annihilateBasis]

theorem ground_field (D : LatticeData) (charge : Charge D) :
    LatticeBcGhostTensorStateField.stateField D (ground D charge) =
      VertexOperatorTensorProduct.field (actualField D charge) (BcGhostSuperGenerators.currentField .c) := by
  have ghost : c 1 (vacuum : Fock ℂ) = Finsupp.single {1} 1 := by
    norm_num [c, vacuum, create, createBasis, sign]
  rw [ground, ← ghost, LatticeBcGhostTensorStateField.stateField_tmul,
    LatticeAllStateField.stateField_ground, BcGhostSuperStateField.stateField_c_generator]

end D5.S3.VertexAlgebra.OriginalChargedGround
