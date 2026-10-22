/- GID: D5/S3/VertexAlgebra/LatticeHalfFockPhysicalWordLocality
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockPhysicalWordLocality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Ordinary Dong locality consumed by exact physical slices of native normal words. -/

import D5.S3.VertexAlgebra.LatticeHalfFockPhysicalGeneratorLocality
import D5.S3.VertexAlgebra.LatticeHalfFockPhysicalLocality

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/- proof_shape: physicalSlice_charged_locality: bind-only; physicalWord_locality: bind-only
   admission_basis: escape-witness
   escape_witness: This module contributes no independent mathematics. Its charged
   coefficient specialization and ordinary Dong inductions are consumed on the
   live original all-state physical-locality proof path. The new rescaling and
   jet finite-difference content belong to their original owning modules.
   Literature status: classical Dong locality; zero novelty. -/

namespace D5.S3.VertexAlgebra.LatticeHalfFockPhysicalWordLocality

open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockFockNormalField LatticeHalfFockPhysicalRescaling
open LatticeHalfFockPhysicalGeneratorLocality LatticeHalfFockPhysicalLocality
open FieldNormalProductLocality FieldNormalProduct FiniteFieldLocality
open scoped VertexOperator

noncomputable section

set_option maxHeartbeats 2000000 in
theorem physicalSlice_charged_locality (D : LatticeData) (hu : IsUnit D.G.det)
    (first second : Charge D) (firstParity secondParity : ℤ) :
    delta^[(bilinear D first second).natAbs]
      (commutator (physicalSlice D hu (chargedField D hu first) firstParity)
        (physicalSlice D hu (chargedField D hu second) secondParity)) = 0 := by
  change (⇑(deltaEnd : Module.End ℂ (ℤ → ℤ → Module.End ℂ (ActualTensor D hu))))^[
      (bilinear D first second).natAbs]
    (FieldNormalProductLocality.commutator
      (physicalSlice D hu (chargedField D hu first) firstParity)
      (physicalSlice D hu (chargedField D hu second) secondParity)) = 0
  rw [← Module.End.pow_apply]
  funext left right
  apply LinearMap.ext
  intro vector
  rw [FieldDeltaBinomial.delta_binomial]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, FieldNormalProductLocality.commutator,
    physicalSlice_mode, chargedField, HVertexOperator.coeff_of_coeff,
    LinearMap.sub_apply, Module.End.mul_apply, Pi.zero_apply, LinearMap.zero_apply]
  have locality := charged_coefficient_physical_locality D hu first second
    (-2 * left - firstParity - 2) (-2 * right - secondParity - 2) vector
  convert locality using 1
  apply Finset.sum_congr rfl
  intro offset member
  have bound : offset ≤ (bilinear D first second).natAbs := by
    exact Nat.le_of_lt_succ (Finset.mem_range.mp member)
  rw [Int.natCast_sub bound]
  rw [show -2 * (left + ((bilinear D first second).natAbs : ℤ) - (offset : ℤ)) -
      firstParity - 2 = -2 * left - firstParity - 2 -
        2 * (((bilinear D first second).natAbs : ℤ) - (offset : ℤ)) by omega,
    show -2 * (right + (offset : ℤ)) - secondParity - 2 =
      -2 * right - secondParity - 2 - 2 * (offset : ℤ) by omega]

private theorem physicalJet_word_local (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (parity : ℤ) (word : List (Index D)) (index : Index D) :
    Local (physicalJet D hu index) (physicalWord D hu charge parity word) := by
  induction word generalizing index with
  | nil =>
    rw [physicalWord_nil]
    exact ⟨index.2 + 1, physicalJet_charge_locality D hu index charge parity⟩
  | cons head tail inductionProof =>
    exact localSymm _ _ (localNormal _ _ _
      ⟨head.2 + index.2 + 2, physicalJet_pair_locality D hu head index⟩
      (localSymm _ _ (inductionProof index)) (inductionProof head))

private theorem physicalCharge_word_local (D : LatticeData) (hu : IsUnit D.G.det)
    (first second : Charge D) (firstParity secondParity : ℤ) (word : List (Index D)) :
    Local (physicalSlice D hu (chargedField D hu first) firstParity)
      (physicalWord D hu second secondParity word) := by
  induction word with
  | nil =>
    rw [physicalWord_nil]
    exact ⟨(bilinear D first second).natAbs,
      physicalSlice_charged_locality D hu first second firstParity secondParity⟩
  | cons head tail inductionProof =>
    exact localSymm _ _ (localNormal _ _ _
      ⟨head.2 + 1, physicalJet_charge_locality D hu head first firstParity⟩
      (localSymm _ _ inductionProof) (physicalJet_word_local D hu second secondParity tail head))

theorem physicalWord_locality (D : LatticeData) (hu : IsUnit D.G.det)
    (first second : Charge D) (firstParity secondParity : ℤ)
    (firstWord secondWord : List (Index D)) :
    Local (physicalWord D hu first firstParity firstWord)
      (physicalWord D hu second secondParity secondWord) := by
  induction firstWord with
  | nil =>
    rw [physicalWord_nil]
    exact physicalCharge_word_local D hu first second firstParity secondParity secondWord
  | cons head tail inductionProof =>
    exact localNormal _ _ _ (physicalJet_word_local D hu second secondParity secondWord head)
      inductionProof (physicalJet_word_local D hu first firstParity tail head)

end
end D5.S3.VertexAlgebra.LatticeHalfFockPhysicalWordLocality
