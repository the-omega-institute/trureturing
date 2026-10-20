/- GID: D5/S3/VertexAlgebra/LatticeHalfFockPhysicalWordLocality
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockPhysicalWordLocality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform signed-slice Dong bounds for canonical charged words. -/

/- Classical Dong locality. Copyright (c) 2025 Scott Carnahan, Apache 2.0,
   vertexAlg 4453e34ec390e82a0c789c731ada8f9a6e86bdea via FieldNormalProduct.
   Actual half-Fock construction: Copyright (c) 2025 Kalle Kytölä; additional
   half-integer implementation copyright (c) 2026, Apache 2.0. Adapted from
   the preserved PhysicalWordLocality b34c02c9708d485fad75054e16c3bb78f140e47cf62dcd4ce3236110c6aa68e0.
   Dong--Nagatomo math/9808088v1 §3.2; Bakalov--Kac math/0402315v1 §4. -/
import D5.S3.VertexAlgebra.LatticeHalfFockPhysicalGeneratorLocality
import D5.S3.VertexAlgebra.LatticeHalfFockPhysicalLocality

/-! All orders are fixed before every signed shift of either source. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeHalfFockPhysicalWordLocality
open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockFockNormalField LatticeHalfFockPhysicalRescaling
open LatticeHalfFockPhysicalGeneratorLocality LatticeHalfFockPhysicalLocality
open FieldNormalProductLocality FieldNormalProduct FiniteFieldLocality
open scoped BigOperators VertexOperator
noncomputable section

private theorem chargedWordField_nil (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) : chargedWordField D hu charge [] = chargedField D hu charge := by
  apply HVertexOperator.coeff_inj
  funext exponent
  apply LinearMap.ext
  intro vector
  rw [chargedWordField, wordField_coefficient]
  change (∑ᶠ _ : Unit, (chargedField D hu charge).coeff exponent vector) = _
  exact finsum_unique _

private theorem physicalSlice_word_cons (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (index : Index D) (word : List (Index D)) (shift : ℤ) :
    physicalSlice D hu (chargedWordField D hu charge (index :: word)) shift =
      (normalMinusOne (physicalJet D hu index)
        (physicalSlice D hu (chargedWordField D hu charge word)
          (shift - (2 * (index.2 : ℤ) + 1)))).val := by
  rw [chargedWordField, wordField_cons_singleton]
  have h := physicalSlice_singletonLinear D hu index
    (wordField D hu (chargedField D hu charge) word)
    (shift - (2 * (index.2 : ℤ) + 1))
  rw [show shift - (2 * (index.2 : ℤ) + 1) + 2 * index.2 + 1 = shift by ring] at h
  exact h

set_option maxHeartbeats 2000000 in
private theorem physicalSlice_charged_locality (D : LatticeData) (hu : IsUnit D.G.det)
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


private def jetWordOrder {D : LatticeData} : List (Index D) → Index D → ℕ
  | [], i => i.2 + 1
  | j :: w, i => j.2 + i.2 + 2 + jetWordOrder w i + jetWordOrder w j

private theorem jet_word_locality (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (word : List (Index D)) (index : Index D) :
    ∀ shift : ℤ, delta^[jetWordOrder word index]
      (commutator (physicalJet D hu index)
        (physicalSlice D hu (chargedWordField D hu charge word) shift)) = 0 := by
  induction word generalizing index with
  | nil =>
    intro shift
    rw [chargedWordField_nil]
    exact physicalJet_charge_locality D hu index charge shift
  | cons head tail ih =>
    intro shift
    rw [physicalSlice_word_cons]
    apply symmetry
    exact normalMinusOne_locality _ _ _
      (head.2 + index.2 + 2) (jetWordOrder tail index) (jetWordOrder tail head)
      (physicalJet_pair_locality D hu head index)
      (symmetry _ _ _ (ih index (shift - (2 * (head.2 : ℤ) + 1))))
      (ih head (shift - (2 * (head.2 : ℤ) + 1)))

private def chargeWordOrder (D : LatticeData) (a b : Charge D) : List (Index D) → ℕ
  | [] => (bilinear D a b).natAbs
  | j :: u => j.2 + 1 + chargeWordOrder D a b u + jetWordOrder u j

private theorem charge_word_locality (D : LatticeData) (hu : IsUnit D.G.det)
    (a b : Charge D) (word : List (Index D)) :
    ∀ s t : ℤ, delta^[chargeWordOrder D a b word]
      (commutator (physicalSlice D hu (chargedField D hu a) s)
        (physicalSlice D hu (chargedWordField D hu b word) t)) = 0 := by
  induction word with
  | nil =>
    intro s t
    rw [chargedWordField_nil]
    exact physicalSlice_charged_locality D hu a b s t
  | cons head tail ih =>
    intro s t
    rw [physicalSlice_word_cons]
    apply symmetry
    exact normalMinusOne_locality _ _ _
      (head.2 + 1) (chargeWordOrder D a b tail) (jetWordOrder tail head)
      (physicalJet_charge_locality D hu head a s)
      (symmetry _ _ _ (ih s (t - (2 * (head.2 : ℤ) + 1))))
      (jet_word_locality D hu b tail head (t - (2 * (head.2 : ℤ) + 1)))

private def wordOrder (D : LatticeData) (a b : Charge D) :
    List (Index D) → List (Index D) → ℕ
  | [], u => chargeWordOrder D a b u
  | i :: w, u => jetWordOrder u i + wordOrder D a b w u + jetWordOrder w i

/-- One Dong bound works simultaneously for every signed slice of both words. -/
theorem physicalWord_locality (D : LatticeData) (hu : IsUnit D.G.det)
    (first second : Charge D) (firstWord secondWord : List (Index D)) :
    ∃ order : ℕ, ∀ s t : ℤ, delta^[order]
      (commutator (physicalSlice D hu (chargedWordField D hu first firstWord) s)
        (physicalSlice D hu (chargedWordField D hu second secondWord) t)) = 0 := by
  refine ⟨wordOrder D first second firstWord secondWord, ?_⟩
  induction firstWord with
  | nil =>
    intro s t
    rw [chargedWordField_nil]
    exact charge_word_locality D hu first second secondWord s t
  | cons head tail ih =>
    intro s t
    rw [physicalSlice_word_cons]
    exact normalMinusOne_locality _ _ _
      (jetWordOrder secondWord head) (wordOrder D first second tail secondWord)
      (jetWordOrder tail head)
      (jet_word_locality D hu second secondWord head t)
      (ih (s - (2 * (head.2 : ℤ) + 1)) t)
      (jet_word_locality D hu first tail head (s - (2 * (head.2 : ℤ) + 1)))

end
end D5.S3.VertexAlgebra.LatticeHalfFockPhysicalWordLocality
