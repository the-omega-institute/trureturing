/- GID: D5/S3/VertexAlgebra/LatticeHalfFockPhysicalRescaling
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockPhysicalRescaling
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact physical parity slices of the original half-current normal words. -/

import D5.S3.VertexAlgebra.LatticeHalfFockAllStateField
import D5.S3.VertexAlgebra.LatticeHalfFockChargedMonodromy
import D5.S3.VertexAlgebra.FieldNormalProductLocality

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

/- proof_shape: physicalSlice_normalInsertion: content; physicalSlice_normalWord: content;
   normalWord_physical_reconstruction: content
   admission_basis: escape-witness
   escape_witness: The exact signed native coefficient shifts are identified with
   canonical physical negative-mode normal convolution. The two complementary
   integer coefficient slices reconstruct the original word without altering
   its operators or normal split. All mode and parity helpers have live consumers.
   Literature status: classical twisted lattice construction; zero novelty. -/

namespace D5.S3.VertexAlgebra.LatticeHalfFockPhysicalRescaling

open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockFockNormalField LatticeHalfFockChargedMonodromy FieldNormalProduct
open scoped VertexOperator

noncomputable section

def physicalSlice (D : LatticeData) (hu : IsUnit D.G.det)
    (field : NativeField D hu) (shift : ℤ) : VertexOperator ℂ (ActualTensor D hu) :=
  VertexOperator.of_coeff (fun exponent => field.coeff (2 * exponent - shift)) (by
    intro vector
    refine ⟨(((HahnModule.of ℂ).symm (field vector)).order + shift) / 2 - 1, ?_⟩
    intro exponent member
    by_contra outside
    apply member
    change ((HahnModule.of ℂ).symm (field vector)).coeff (2 * exponent - shift) = 0
    apply HahnSeries.coeff_eq_zero_of_lt_order
    omega)

theorem physicalSlice_mode (D : LatticeData) (hu : IsUnit D.G.det)
    (field : NativeField D hu) (shift mode : ℤ) :
    (physicalSlice D hu field shift)[[mode]] = field.coeff (-2 * mode - shift - 2) := by
  simp only [physicalSlice, VertexOperator.ncoeff_of_coeff]
  rw [show 2 * (-mode - 1) - shift = -2 * mode - shift - 2 by omega]

def physicalJet (D : LatticeData) (hu : IsUnit D.G.det) (index : Index D) :
    VertexOperator ℂ (ActualTensor D hu) :=
  VertexOperator.of_coeff (fun exponent => jetCurrent D hu index (-exponent - 1)) (by
    intro vector
    obtain ⟨cutoff, bound⟩ :=
      LatticeHalfFock.tensor_current_truncation D (ActualGround D hu) vector
    refine ⟨-(cutoff : ℤ) - 1, ?_⟩
    intro exponent member
    by_contra outside
    apply member
    simp only [jetCurrent, LinearMap.smul_apply,
      bound index.1 (-exponent - 1) (by omega), smul_zero])

theorem physicalJet_mode (D : LatticeData) (hu : IsUnit D.G.det)
    (index : Index D) (mode : ℤ) :
    (physicalJet D hu index)[[mode]] = jetCurrent D hu index mode := by
  simp only [physicalJet, VertexOperator.ncoeff_of_coeff]
  congr 1
  omega

theorem physicalSlice_normalInsertion (D : LatticeData) (hu : IsUnit D.G.det)
    (index : Index D) (field : NativeField D hu) (shift : ℤ) :
    physicalSlice D hu (normalInsertion D hu index field) (shift + 2 * index.2 + 1) =
      (normalMinusOne (physicalJet D hu index) (physicalSlice D hu field shift)).val := by
  have modes (mode : ℤ) :
      (physicalSlice D hu (normalInsertion D hu index field)
        (shift + 2 * index.2 + 1))[[mode]] =
      (normalMinusOne (physicalJet D hu index) (physicalSlice D hu field shift)).val[[mode]] := by
    apply LinearMap.ext
    intro vector
    rw [physicalSlice_mode, (normalMinusOne _ _).property]
    simp only [normalInsertion, HVertexOperator.coeff_of_coeff, normalCoefficient,
      LinearMap.coe_mk, AddHom.coe_mk]
    congr 1
    · apply finsum_congr
      intro offset
      rw [physicalJet_mode, physicalSlice_mode]
      simp only [negativeTerm, jetCurrent, LinearMap.smul_apply]
      rw [show -2 * mode - (shift + 2 * (index.2 : ℤ) + 1) - 2 -
          2 * (offset : ℤ) + 2 * index.2 + 1 =
        -2 * (mode + offset) - shift - 2 by omega]
    · apply finsum_congr
      intro offset
      rw [physicalJet_mode, physicalSlice_mode]
      simp only [positiveTerm, jetCurrent, LinearMap.smul_apply, map_smul]
      rw [show -2 * mode - (shift + 2 * (index.2 : ℤ) + 1) - 2 +
          2 * (offset : ℤ) + 2 * index.2 + 3 =
        -2 * (mode - offset - 1) - shift - 2 by omega]
  apply HVertexOperator.coeff_inj
  funext exponent
  simpa only [VertexOperator.ncoeff_apply,
    show -(-exponent - 1) - 1 = exponent by omega] using modes (-exponent - 1)

def wordShift (D : LatticeData) : List (Index D) → ℤ
  | [] => 0
  | index :: tail => 2 * index.2 + 1 + wordShift D tail

def physicalCharge (D : LatticeData) (hu : IsUnit D.G.det) (charge : Charge D)
    (parity : ℤ) : VertexOperator ℂ (ActualTensor D hu) :=
  physicalSlice D hu (chargedField D hu charge +
    ((-1 : ℂ) ^ parity) • chargedField D hu (-charge)) parity

theorem physicalCharge_parity_mode (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (parity mode : ℤ) :
    (physicalCharge D hu charge parity)[[mode]] =
      chargedCoefficient D hu charge (-2 * mode - parity - 2) +
        ((-1 : ℂ) ^ parity) • chargedCoefficient D hu (-charge) (-2 * mode - parity - 2) := by
  simp only [physicalCharge, physicalSlice_mode, map_add, map_smul, Pi.add_apply,
    Pi.smul_apply, chargedField, HVertexOperator.coeff_of_coeff]

private theorem physicalCharge_as_slice (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (parity : ℤ) :
    physicalCharge D hu charge parity =
      (2 : ℂ) • physicalSlice D hu (chargedField D hu charge) parity := by
  have modes (mode : ℤ) :
      (physicalCharge D hu charge parity)[[mode]] =
        ((2 : ℂ) • physicalSlice D hu (chargedField D hu charge) parity)[[mode]] := by
    simp only [physicalCharge_parity_mode, map_smul, Pi.smul_apply,
      physicalSlice_mode, chargedField, HVertexOperator.coeff_of_coeff,
      charged_coefficient_coordinate_monodromy, smul_smul]
    have sign : ((-1 : ℂ) ^ parity) * ((-1 : ℂ) ^ (-2 * mode - parity - 2)) = 1 := by
      rw [← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
      have even : Even (parity + (-2 * mode - parity - 2)) := ⟨-mode - 1, by omega⟩
      exact even.neg_one_zpow
    rw [sign, one_smul]
    module
  apply HVertexOperator.coeff_inj
  funext exponent
  simpa only [VertexOperator.ncoeff_apply,
    show -(-exponent - 1) - 1 = exponent by omega] using modes (-exponent - 1)

def physicalWord (D : LatticeData) (hu : IsUnit D.G.det) (charge : Charge D)
    (parity : ℤ) : List (Index D) → VertexOperator ℂ (ActualTensor D hu)
  | [] => (2 : ℂ)⁻¹ • physicalCharge D hu charge parity
  | index :: tail => (normalMinusOne (physicalJet D hu index)
      (physicalWord D hu charge parity tail)).val

theorem physicalWord_nil (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (parity : ℤ) :
    physicalWord D hu charge parity [] = physicalSlice D hu (chargedField D hu charge) parity := by
  rw [physicalWord, physicalCharge_as_slice, smul_smul,
    inv_mul_cancel₀ (by norm_num : (2 : ℂ) ≠ 0), one_smul]

theorem physicalSlice_normalWord (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (parity : ℤ) (word : List (Index D)) :
    physicalSlice D hu (normalWord D hu charge word) (wordShift D word + parity) =
      physicalWord D hu charge parity word := by
  induction word with
  | nil => simp only [normalWord, wordShift, zero_add, physicalWord_nil]
  | cons index tail inductionProof =>
    simp only [normalWord, wordShift, physicalWord]
    rw [show 2 * (index.2 : ℤ) + 1 + wordShift D tail + parity =
      (wordShift D tail + parity) + 2 * index.2 + 1 by omega,
      physicalSlice_normalInsertion, inductionProof]

def physicalLift (D : LatticeData) (hu : IsUnit D.G.det)
    (field : VertexOperator ℂ (ActualTensor D hu)) (shift : ℤ) : NativeField D hu :=
  HVertexOperator.of_coeff (fun exponent =>
    if (exponent + shift) % 2 = 0 then field.coeff ((exponent + shift) / 2) else 0) (by
    intro vector
    apply Set.IsWF.isPWO
    apply BddBelow.isWF
    refine ⟨2 * ((HahnModule.of ℂ).symm (field vector)).order - shift - 1, ?_⟩
    intro exponent member
    by_contra outside
    apply member
    simp only [LinearMap.zero_apply]
    split_ifs
    · change ((HahnModule.of ℂ).symm (field vector)).coeff ((exponent + shift) / 2) = 0
      apply HahnSeries.coeff_eq_zero_of_lt_order
      omega
    · rfl)

private theorem physicalLift_slice (D : LatticeData) (hu : IsUnit D.G.det)
    (field : NativeField D hu) (shift exponent : ℤ) :
    (physicalLift D hu (physicalSlice D hu field shift) shift).coeff exponent =
      if (exponent + shift) % 2 = 0 then field.coeff exponent else 0 := by
  have sliceCoefficient (power : ℤ) :
      (physicalSlice D hu field shift).coeff power = field.coeff (2 * power - shift) := rfl
  simp only [physicalLift, HVertexOperator.coeff_of_coeff, sliceCoefficient]
  split_ifs with parity
  · rw [show 2 * ((exponent + shift) / 2) - shift = exponent by omega]
  · rfl

theorem native_parity_reconstruction (D : LatticeData) (hu : IsUnit D.G.det)
    (field : NativeField D hu) (shift : ℤ) :
    field = physicalLift D hu (physicalSlice D hu field shift) shift +
      physicalLift D hu (physicalSlice D hu field (shift + 1)) (shift + 1) := by
  apply HVertexOperator.coeff_inj
  funext exponent
  simp only [map_add, Pi.add_apply, physicalLift_slice]
  by_cases parity : (exponent + shift) % 2 = 0
  · have other : (exponent + (shift + 1)) % 2 ≠ 0 := by omega
    simp only [parity, other, if_true, if_false, add_zero]
  · have other : (exponent + (shift + 1)) % 2 = 0 := by omega
    simp only [parity, other, if_true, if_false, zero_add]

theorem normalWord_physical_reconstruction (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (word : List (Index D)) :
    normalWord D hu charge word =
      physicalLift D hu (physicalWord D hu charge 0 word) (wordShift D word) +
      physicalLift D hu (physicalWord D hu charge 1 word) (wordShift D word + 1) := by
  have reconstruction := native_parity_reconstruction D hu
    (normalWord D hu charge word) (wordShift D word)
  have evenSlice := physicalSlice_normalWord D hu charge 0 word
  simp only [add_zero] at evenSlice
  rw [evenSlice, physicalSlice_normalWord D hu charge 1 word] at reconstruction
  exact reconstruction

end
end D5.S3.VertexAlgebra.LatticeHalfFockPhysicalRescaling
