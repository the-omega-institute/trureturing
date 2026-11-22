import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Words.Patterns.Separable.OccupiedMellinDiscreteCenter
import Reg.Support.DependentFamily

/-! The stored readout is the actual paired sample at varying exponent. -/

namespace Reg.D5.S1.Words.Patterns.Separable.OccupiedMellinDiscreteCenter


open _root_.D5.S1.Words.Patterns.Separable.OccupiedMellinDiscreteCenter
open _root_.D5.S1.Words.Patterns.Separable.OccupiedMellinInterior (sample)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → ℝ → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ β => sample β) (fun a => nomatch a)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ _ => 17) (fun a => nomatch a)

def arena : Arena where
  signature := signature
  Law R := ∀ {β δ : ℝ}, 0 ≤ β → β ≤ 3 / 4 → 0 ≤ δ → δ ≤ 1 / 2 →
    ∀ (n K : ℕ), 0 < n → (K : ℝ) / n ≤ δ →
    ((∑ i ∈ Finset.range K, |R.readout () () β (2 / (n : ℝ)) (1 - (((i+1 : ℕ) : ℝ) / n))|) +
      |R.readout () () β (2 / (n : ℝ)) 1| +
      (∑ i ∈ Finset.range K, |R.readout () () β (2 / (n : ℝ)) (1 + (((i+1 : ℕ) : ℝ) / n))|)) / n ≤
      56 * δ ^ (1 / 4 : ℝ) + 16 * (n : ℝ) ^ (-(1 / 4 : ℝ))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz := h (β := 0) (δ := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    1 0 (by omega) (by norm_num)
  simp [rejected, realize] at hz
  norm_num at hz

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, 1 / 2, ?_⟩
  intro h
  have he := congrFun (congrFun h 0) 2
  change sample 0 0 2 = sample (1 / 2) 0 2 at he
  have hp : 0 < (2 : ℝ) ^ (-(3 / 2 : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have hq : (3 : ℝ) ^ (-(1 / 2 : ℝ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hnorm : |1 - (2 : ℝ)| = 1 := by norm_num
  simp only [sample, hnorm, neg_zero, Real.rpow_zero, zero_add, Real.one_rpow] at he
  norm_num only [show 1 + (2 : ℝ) = 3 by norm_num] at he
  have hneg : (2 : ℝ) ^ (-(3 / 2 : ℝ)) * ((3 : ℝ) ^ (-(1 / 2 : ℝ)) + 1 - 2 * 1) < 0 :=
    mul_neg_of_pos_of_neg hp (by linarith)
  linarith

def family : Registration arena (type_of% @near_center_cutoff) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨near_center_cutoff, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (@Subsingleton.elim Unit _ j i)).elim,
    rfl, rejected_law⟩, fun a => nomatch a⟩
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@near_center_cutoff) (Realization signature) (Type) Unit where
  unitName := `Reg.D5.S1.Words.Patterns.Separable.OccupiedMellinDiscreteCenter.unit
  realizationName := `Reg.D5.S1.Words.Patterns.Separable.OccupiedMellinDiscreteCenter.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ β => sample β) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.Patterns.Separable.OccupiedMellinDiscreteCenter
    definition := none
    coordinates := #[]
    readouts := #[{
      path :=  #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "fn", "arg", "fn", "arg", "arg", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end
end Reg.D5.S1.Words.Patterns.Separable.OccupiedMellinDiscreteCenter
