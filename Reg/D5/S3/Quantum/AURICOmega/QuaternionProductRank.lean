import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.AURICOmega.QuaternionProductRank
import Reg.Support.DependentFamily

/-! Source-bound audit of the feature-rank failure for the product of two quaternion models. -/

namespace Reg.D5.S3.Quantum.AURICOmega.QuaternionProductRank

open _root_.D5.S3.Quantum.AURICOmega.TernaryComparisonGroup
open _root_.D5.S3.Quantum.AURICOmega.TernaryComparisonProduct
open _root_.D5.S3.Quantum.AURICOmega.QuaternionComparisonModel
open _root_.D5.S3.Quantum.AURICOmega.QuaternionProductRank
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

open scoped Quaternion

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false
noncomputable section

/-- A ternary comparison structure transported along an equivalence of carriers. -/
def pullback {α β : Type} (e : α ≃ β) (C : TernaryComparison β) : TernaryComparison α where
  tri x y z := e.symm (C.tri (e x) (e y) (e z))
  kappa x y := C.kappa (e x) (e y)
  tri_self_left x z := by simp only [C.tri_self_left, Equiv.symm_apply_apply]
  tri_self_right x z := by simp only [C.tri_self_right, Equiv.symm_apply_apply]
  tri_assoc x y z u v := by simp only [Equiv.apply_symm_apply, C.tri_assoc]
  kappa_symm x y := C.kappa_symm _ _
  kappa_eq_one_iff x y := (C.kappa_eq_one_iff _ _).trans e.injective.eq_iff
  kappa_nonneg x y := C.kappa_nonneg _ _
  kappa_tri_right x y u v := by simp only [Equiv.apply_symm_apply, C.kappa_tri_right]
  kappa_tri_left u v x y := by simp only [Equiv.apply_symm_apply, C.kappa_tri_left]
  kappa_gram_nonneg n x c := C.kappa_gram_nonneg n (fun i => e (x i)) c

/-- Transport preserves feature rank. -/
theorem pullback_hasFeatureRank {α β : Type} (e : α ≃ β) (C : TernaryComparison β) {r : ℕ}
    (h : C.HasFeatureRank r) : (pullback e C).HasFeatureRank r := by
  obtain ⟨f, hf⟩ := h
  exact ⟨fun x => f (e x), fun x y => hf (e x) (e y)⟩

/-- The unit quaternion `cos t + sin t * i`. -/
def circlePoint (t : ℝ) : unitary ℍ[ℝ] :=
  ⟨⟨Real.cos t, Real.sin t, 0, 0⟩, by
    have h : Quaternion.normSq (⟨Real.cos t, Real.sin t, 0, 0⟩ : ℍ[ℝ]) = 1 := by
      rw [Quaternion.normSq_def']
      simp only
      nlinarith [Real.cos_sq_add_sin_sq t]
    exact Unitary.mem_iff.mpr
      ⟨by rw [Quaternion.star_mul_self, h, Quaternion.coe_one],
       by rw [Quaternion.self_mul_star, h, Quaternion.coe_one]⟩⟩

/-- There are infinitely many unit quaternions. -/
theorem infinite_unitary : Infinite (unitary ℍ[ℝ]) := by
  refine Infinite.of_injective (fun n : ℕ => circlePoint (1 / ((n : ℝ) + 1))) fun m n h => ?_
  have hre := congrArg (fun z : unitary ℍ[ℝ] => (z : ℍ[ℝ]).re) h
  change Real.cos (1 / ((m : ℝ) + 1)) = Real.cos (1 / ((n : ℝ) + 1)) at hre
  have mem : ∀ k : ℕ, 1 / ((k : ℝ) + 1) ∈ Set.Icc 0 Real.pi := fun k => by
    have hk : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) k]
    refine ⟨by positivity, ?_⟩
    calc 1 / ((k : ℝ) + 1) ≤ 1 := by rw [div_le_one (by linarith)]; exact hk
      _ ≤ Real.pi := by linarith [Real.one_le_pi_div_two]
  have h1 := Real.injOn_cos (mem m) (mem n) hre
  rw [one_div, one_div, inv_inj, add_left_inj] at h1
  exact_mod_cast h1

/-- Pairs of unit quaternions are equinumerous with unit quaternions. -/
theorem pair_equiv : Nonempty (unitary ℍ[ℝ] × unitary ℍ[ℝ] ≃ unitary ℍ[ℝ]) := by
  have : Infinite (unitary ℍ[ℝ]) := infinite_unitary
  refine Cardinal.eq.1 ?_
  rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.mul_eq_self (Cardinal.aleph0_le_mk _)]

/-- The quaternion model transported to pairs; its reading has feature rank five. -/
def pairModel : TernaryComparison (unitary ℍ[ℝ] × unitary ℍ[ℝ]) :=
  pullback (Classical.choice pair_equiv) quaternionModel

/-- The quaternion model transported along inversion: its transfer is `z * y⁻¹ * x`. -/
def reversedModel : TernaryComparison (unitary ℍ[ℝ]) :=
  pullback (Equiv.inv (unitary ℍ[ℝ])) quaternionModel

namespace Factor

/-- Observe the product of the quaternion model with a chosen second factor. -/
abbrev signature : Signature where
  Params := Unit
  State _ := TernaryComparison (unitary ℍ[ℝ])
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := TernaryComparison (unitary ℍ[ℝ] × unitary ℍ[ℝ])
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ D => prod quaternionModel D) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => pairModel) (fun e => nomatch e)

/-- Retain all four conjuncts of `prod_quaternionModel_not_hasFeatureRank_five`. -/
abbrev arena : Arena where
  signature := signature
  Law r := (prod quaternionModel quaternionModel).Noncommutative ∧
    (prod quaternionModel quaternionModel).ChainConnected ∧
    (prod quaternionModel quaternionModel).TouchesZero ∧
    ¬ (r.readout () () quaternionModel).HasFeatureRank 5

theorem rejected_law : ¬ arena.Law rejected := fun h =>
  h.2.2.2 (pullback_hasFeatureRank _ _ quaternionModel_hasFeatureRank_five)

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), quaternionModel, reversedModel, fun h => ?_⟩
  obtain ⟨a, b, c, hne⟩ := quaternionModel_noncommutative
  have h' : prod quaternionModel quaternionModel = prod quaternionModel reversedModel := h
  have ht := congrArg (fun S : TernaryComparison (unitary ℍ[ℝ] × unitary ℍ[ℝ]) =>
    (S.tri (1, a) (1, b) (1, c)).2) h'
  change a * b⁻¹ * c = (a⁻¹ * b⁻¹⁻¹ * c⁻¹)⁻¹ at ht
  apply hne
  change a * b⁻¹ * c = c * b⁻¹ * a
  rw [ht]
  group

def source_registration :
    Registration arena (type_of% prod_quaternionModel_not_hasFeatureRank_five) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨prod_quaternionModel_not_hasFeatureRank_five, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

end Factor

def prod_quaternionModel_not_hasFeatureRank_five_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      prod_quaternionModel_not_hasFeatureRank_five (Realization Factor.signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.AURICOmega.QuaternionProductRank.prod_quaternionModel_not_hasFeatureRank_five_unit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.QuaternionProductRank.Factor.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨Factor.arena⟩
  objectArena := .source ⟨Factor.arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Factor.arena ⟨Factor.source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Factor.signature
    (fun _ _ D => prod quaternionModel D) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.AURICOmega.QuaternionProductRank
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "arg", "arg", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end

end Reg.D5.S3.Quantum.AURICOmega.QuaternionProductRank
