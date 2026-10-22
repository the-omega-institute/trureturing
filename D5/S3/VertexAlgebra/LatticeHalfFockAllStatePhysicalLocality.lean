/- GID: D5/S3/VertexAlgebra/LatticeHalfFockAllStatePhysicalLocality
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockAllStatePhysicalLocality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact finite-charge corrected native fields have physical two-sheet locality. -/

import D5.S3.VertexAlgebra.LatticeHalfFockPhysicalWordLocality

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

/- proof_shape: normalWord_cover_locality: content; Ytw_physical_locality: content
   admission_basis: escape-witness
   escape_witness: Exact parity-lift transport converts ordinary Dong locality
   into the original double-cover finite commutator. Genuine finite maxima
   propagate through actual charge, Corr-shift and monomial supports. Every
   signed original coefficient and arbitrary target vector remains in scope.
   No all-state locality, Jacobi, rank or positivity premise is introduced.
   Literature status: classical twisted lattice locality; zero novelty. -/

namespace D5.S3.VertexAlgebra.LatticeHalfFockAllStatePhysicalLocality

open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockFockNormalField LatticeHalfFockAllStateField
open LatticeHalfFockPhysicalRescaling LatticeHalfFockPhysicalWordLocality
open FieldNormalProductLocality FiniteFieldLocality
open scoped VertexOperator

noncomputable section

private theorem delta_power {State : Type*} [AddCommGroup State] [Module ℂ State]
    (distribution : ℤ → ℤ → Module.End ℂ State) (order : ℕ) :
    (deltaEnd ^ order) distribution = delta^[order] distribution :=
  Module.End.pow_apply deltaEnd order distribution

def coverGrid (D : LatticeData) (hu : IsUnit D.G.det)
    (first second : NativeField D hu) (firstExponent secondExponent : ℤ) :
    ℤ → ℤ → Module.End ℂ (ActualTensor D hu) :=
  fun left right => first.coeff (firstExponent - 2 * left) *
      second.coeff (secondExponent - 2 * right) -
    second.coeff (secondExponent - 2 * right) * first.coeff (firstExponent - 2 * left)

def CoverLocal (D : LatticeData) (hu : IsUnit D.G.det)
    (first second : NativeField D hu) : Prop :=
  ∃ order : ℕ, ∀ firstExponent secondExponent : ℤ,
    delta^[order] (coverGrid D hu first second firstExponent secondExponent) = 0

def translated {State : Type*} (distribution : ℤ → ℤ → State) (left right : ℤ) :
    ℤ → ℤ → State := fun first second => distribution (left + first) (right + second)

private theorem delta_translated {State : Type*} [AddCommGroup State]
    (distribution : ℤ → ℤ → State) (left right : ℤ) (order : ℕ) :
    delta^[order] (translated distribution left right) =
      translated (delta^[order] distribution) left right := by
  induction order with
  | zero => rfl
  | succ order inductionProof =>
    rw [Function.iterate_succ_apply', inductionProof, Function.iterate_succ_apply']
    funext first second
    simp only [delta, translated, add_assoc]

private theorem lift_coefficient (D : LatticeData) (hu : IsUnit D.G.det)
    (field : VertexOperator ℂ (ActualTensor D hu)) (shift exponent offset : ℤ) :
    (physicalLift D hu field shift).coeff (exponent - 2 * offset) =
      if (exponent + shift) % 2 = 0 then field[[-((exponent + shift) / 2) - 1 + offset]]
      else 0 := by
  simp only [physicalLift, HVertexOperator.coeff_of_coeff, VertexOperator.ncoeff_apply]
  have parity : (exponent - 2 * offset + shift) % 2 = (exponent + shift) % 2 := by omega
  rw [parity]
  split_ifs
  · rw [show (exponent - 2 * offset + shift) / 2 =
      -(-((exponent + shift) / 2) - 1 + offset) - 1 by omega]
  · rfl

private theorem coverLift_local (D : LatticeData) (hu : IsUnit D.G.det)
    (first second : VertexOperator ℂ (ActualTensor D hu)) (firstShift secondShift : ℤ)
    (locality : Local first second) :
    CoverLocal D hu (physicalLift D hu first firstShift) (physicalLift D hu second secondShift) := by
  obtain ⟨order, killed⟩ := locality
  refine ⟨order, ?_⟩
  intro firstExponent secondExponent
  have grid : coverGrid D hu (physicalLift D hu first firstShift)
      (physicalLift D hu second secondShift) firstExponent secondExponent =
      if (firstExponent + firstShift) % 2 = 0 ∧ (secondExponent + secondShift) % 2 = 0 then
        translated (commutator first second) (-((firstExponent + firstShift) / 2) - 1)
          (-((secondExponent + secondShift) / 2) - 1) else 0 := by
    funext left right
    simp only [coverGrid, lift_coefficient, translated, FieldNormalProductLocality.commutator]
    split_ifs <;> simp_all [translated, FieldNormalProductLocality.commutator]
  rw [grid]
  split_ifs
  · rw [delta_translated, killed]
    rfl
  · rw [← delta_power, map_zero]

private theorem coverLocal_add (D : LatticeData) (hu : IsUnit D.G.det)
    (first second third : NativeField D hu)
    (firstLocal : CoverLocal D hu first third) (secondLocal : CoverLocal D hu second third) :
    CoverLocal D hu (first + second) third := by
  obtain ⟨firstOrder, firstKilled⟩ := firstLocal
  obtain ⟨secondOrder, secondKilled⟩ := secondLocal
  refine ⟨max firstOrder secondOrder, ?_⟩
  intro firstExponent secondExponent
  have grid : coverGrid D hu (first + second) third firstExponent secondExponent =
      coverGrid D hu first third firstExponent secondExponent +
        coverGrid D hu second third firstExponent secondExponent := by
    funext left right
    simp only [coverGrid, map_add, Pi.add_apply, add_mul, mul_add]
    abel
  rw [grid, ← delta_power]
  rw [map_add, delta_power, delta_power,
    monotone _ _ _ (le_max_left _ _) (firstKilled firstExponent secondExponent),
    monotone _ _ _ (le_max_right _ _) (secondKilled firstExponent secondExponent), add_zero]

private theorem delta_flip {State : Type*} [AddCommGroup State] [Module ℂ State]
    (value : ℤ → ℤ → Module.End ℂ State) (order : ℕ) :
    delta^[order] (flipDistribution value) =
      ((-1 : ℂ) ^ order) • flipDistribution (delta^[order] value) := by
  induction order with
  | zero => simp
  | succ count inductionProof =>
    rw [Function.iterate_succ_apply', inductionProof, Function.iterate_succ_apply']
    funext left right
    simp only [delta, flipDistribution, LinearMap.coe_mk, AddHom.coe_mk,
      Pi.smul_apply, pow_succ]
    module

private theorem coverLocal_symm (D : LatticeData) (hu : IsUnit D.G.det)
    (first second : NativeField D hu) (locality : CoverLocal D hu first second) :
    CoverLocal D hu second first := by
  obtain ⟨order, killed⟩ := locality
  refine ⟨order, ?_⟩
  intro firstExponent secondExponent
  have grid : coverGrid D hu second first firstExponent secondExponent =
      -flipDistribution (coverGrid D hu first second secondExponent firstExponent) := by
    funext left right
    simp only [coverGrid, flipDistribution, LinearMap.coe_mk, AddHom.coe_mk, Pi.neg_apply]
    abel
  rw [grid, ← delta_power]
  rw [map_neg, delta_power, delta_flip, killed, map_zero, smul_zero, neg_zero]

private theorem coverLocal_smul (D : LatticeData) (hu : IsUnit D.G.det)
    (scalar : ℂ) (first second : NativeField D hu) (locality : CoverLocal D hu first second) :
    CoverLocal D hu (scalar • first) second := by
  obtain ⟨order, killed⟩ := locality
  refine ⟨order, ?_⟩
  intro firstExponent secondExponent
  have grid : coverGrid D hu (scalar • first) second firstExponent secondExponent =
      scalar • coverGrid D hu first second firstExponent secondExponent := by
    funext left right
    simp only [coverGrid, map_smul, Pi.smul_apply,
      Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_sub]
  rw [grid, ← delta_power]
  rw [map_smul, delta_power, killed, smul_zero]

private theorem coverLocal_sum (D : LatticeData) (hu : IsUnit D.G.det)
    {IndexType : Type*} (indices : Finset IndexType) (fields : IndexType → NativeField D hu)
    (other : NativeField D hu) (locality : ∀ index ∈ indices, CoverLocal D hu (fields index) other) :
    CoverLocal D hu (∑ index ∈ indices, fields index) other := by
  classical
  induction indices using Finset.induction_on with
  | empty =>
    refine ⟨0, ?_⟩
    intros
    simp only [Finset.sum_empty, Function.iterate_zero_apply]
    funext left right
    simp [coverGrid]
  | @insert head tail absent inductionProof =>
    rw [Finset.sum_insert absent]
    exact coverLocal_add D hu _ _ _ (locality head (Finset.mem_insert_self _ _))
      (inductionProof (fun index member => locality index (Finset.mem_insert_of_mem member)))

private theorem coverLocal_shift (D : LatticeData) (hu : IsUnit D.G.det)
    (shift : ℕ) (first second : NativeField D hu) (locality : CoverLocal D hu first second) :
    CoverLocal D hu (shiftLinear D hu shift first) second := by
  obtain ⟨order, killed⟩ := locality
  refine ⟨order, ?_⟩
  intro firstExponent secondExponent
  have grid : coverGrid D hu (shiftLinear D hu shift first) second firstExponent secondExponent =
      coverGrid D hu first second (firstExponent + 2 * shift) secondExponent := by
    funext left right
    simp only [coverGrid, shiftLinear, shiftField, LinearMap.coe_mk, AddHom.coe_mk,
      HVertexOperator.coeff_of_coeff]
    rw [show firstExponent - 2 * left + 2 * shift = firstExponent + 2 * shift - 2 * left by omega]
  rw [grid, killed]

theorem normalWord_cover_locality (D : LatticeData) (hu : IsUnit D.G.det)
    (first second : Charge D) (firstWord secondWord : List (Index D)) :
    CoverLocal D hu (normalWord D hu first firstWord) (normalWord D hu second secondWord) := by
  rw [normalWord_physical_reconstruction, normalWord_physical_reconstruction]
  apply coverLocal_add
  · apply coverLocal_symm
    apply coverLocal_add
    · apply coverLocal_symm
      exact coverLift_local D hu _ _ _ _ (physicalWord_locality D hu first second 0 0 _ _)
    · apply coverLocal_symm
      exact coverLift_local D hu _ _ _ _ (physicalWord_locality D hu first second 0 1 _ _)
  · apply coverLocal_symm
    apply coverLocal_add
    · apply coverLocal_symm
      exact coverLift_local D hu _ _ _ _ (physicalWord_locality D hu first second 1 0 _ _)
    · apply coverLocal_symm
      exact coverLift_local D hu _ _ _ _ (physicalWord_locality D hu first second 1 1 _ _)

private theorem Ytw_word_locality (D : LatticeData) (hu : IsUnit D.G.det)
    (state : Carrier D) (charge : Charge D) (word : List (Index D)) :
    CoverLocal D hu (Ytw D hu state) (normalWord D hu charge word) := by
  rw [Ytw_enumerated_expansion D hu state
    (fun _ _ exponent => LatticeAllStateField.occurrences D exponent) (by intros; rfl)]
  apply coverLocal_sum
  intro sourceCharge _
  apply coverLocal_sum
  intro shift _
  apply coverLocal_sum
  intro exponent _
  apply coverLocal_smul
  apply coverLocal_shift
  exact normalWord_cover_locality D hu sourceCharge charge _ word

theorem Ytw_physical_locality (D : LatticeData) (hu : IsUnit D.G.det)
    (first second : Carrier D) :
    ∃ order : ℕ, ∀ firstExponent secondExponent : ℤ, ∀ vector : ActualTensor D hu,
      ∑ offset ∈ Finset.range (order + 1),
        (((-1 : ℂ) ^ offset) * (order.choose offset : ℂ)) •
          ((Ytw D hu first).coeff (firstExponent - 2 * ((order - offset : ℕ) : ℤ))
              ((Ytw D hu second).coeff (secondExponent - 2 * (offset : ℤ)) vector) -
            (Ytw D hu second).coeff (secondExponent - 2 * (offset : ℤ))
              ((Ytw D hu first).coeff (firstExponent - 2 * ((order - offset : ℕ) : ℤ)) vector)) = 0 := by
  have locality : CoverLocal D hu (Ytw D hu first) (Ytw D hu second) := by
    apply coverLocal_symm
    rw [Ytw_enumerated_expansion D hu second
      (fun _ _ exponent => LatticeAllStateField.occurrences D exponent) (by intros; rfl)]
    apply coverLocal_sum
    intro charge _
    apply coverLocal_sum
    intro shift _
    apply coverLocal_sum
    intro exponent _
    apply coverLocal_smul
    apply coverLocal_shift
    exact coverLocal_symm D hu _ _ (Ytw_word_locality D hu first charge _)
  obtain ⟨order, killed⟩ := locality
  refine ⟨order, ?_⟩
  intro firstExponent secondExponent vector
  have operatorKilled : (deltaEnd ^ order)
      (coverGrid D hu (Ytw D hu first) (Ytw D hu second) firstExponent secondExponent) = 0 := by
    rw [delta_power]
    exact killed firstExponent secondExponent
  have zero := congrArg (fun distribution : ℤ → ℤ → Module.End ℂ (ActualTensor D hu) =>
    distribution 0 0 vector) operatorKilled
  rw [FieldDeltaBinomial.delta_binomial] at zero
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, coverGrid, zero_add,
    LinearMap.sub_apply, Module.End.mul_apply, Pi.zero_apply, LinearMap.zero_apply] at zero
  convert zero using 1
  apply Finset.sum_congr rfl
  intro offset member
  have bound : offset ≤ order := Nat.le_of_lt_succ (Finset.mem_range.mp member)
  rw [Int.natCast_sub bound]

end
end D5.S3.VertexAlgebra.LatticeHalfFockAllStatePhysicalLocality
