import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Asymptotics.GeometricRightUSCUniformization
import Reg.Support.SingleDependentReadout
import Mathlib.Topology.Baire.CompleteMetrizable

/-! Full-family source audit of geometric right upper semicontinuity uniformization. -/

namespace Reg.D5.S3.Analytic.Asymptotics.GeometricRightUSCUniformization
open Set
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Analytic.Asymptotics.GeometricRightUSCUniformization
open LeanInformationAudit
noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ → ℝ)
    (fun _ => ℝ → ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ F => F) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ x => -x) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (F : ℝ → ℝ) (T : ℝ), 1 ≤ T →
    (∀ x : ℝ, T ≤ x → UpperSemicontinuousWithinAt F (Ioi x) x) →
    ∀ a b : ℝ, 1 < a → a < b → ∀ S : Set ℝ, S ⊆ Ioo a b → ¬ IsMeagre S →
    (∀ q ∈ S, ∃ M : ℝ, 0 ≤ M ∧ ∃ N : ℕ, 1 ≤ N ∧
      ∀ k : ℕ, N ≤ k → -M ≤ F (q ^ k)) →
    ∃ M : ℝ, 0 ≤ M ∧ ∃ X : ℝ, T < X ∧
      ∀ x : ℝ, X ≤ x → -M ≤ R.readout () () F x

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hS : ¬ IsMeagre (Ioo (2 : ℝ) 3) :=
    not_isMeagre_of_isOpen isOpen_Ioo (nonempty_Ioo.mpr (by norm_num))
  obtain ⟨M, _, X, _, hX⟩ := h (fun _ => 0) 1 le_rfl
    (fun x _ z hz => Filter.Eventually.of_forall (fun _ => hz))
    2 3 (by norm_num) (by norm_num) (Ioo 2 3) Subset.rfl hS
    (fun _ _ => ⟨0, le_rfl, 1, le_rfl, fun _ _ => by simp⟩)
  have hx := hX (max X (M + 1)) (le_max_left _ _)
  have hmx := le_max_right X (M + 1)
  change -M ≤ -max X (M + 1) at hx
  linarith

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (fun _ => 0), (fun _ => 1), ?_⟩
  intro h
  have hh := congrFun h 0
  norm_num [actual, realize] at hh

def family : Registration arena
    (type_of% (@uniform_lower_bound_of_nonmeagre_geometric_bases_right_usc)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@uniform_lower_bound_of_nonmeagre_geometric_bases_right_usc,
    rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@uniform_lower_bound_of_nonmeagre_geometric_bases_right_usc)
    (Realization signature) Unit Unit where
  unitName := `D5.S3.Analytic.Asymptotics.GeometricRightUSCUniformization.uniform_lower_bound_of_nonmeagre_geometric_bases_right_usc.__information_unit
  realizationName := `Reg.D5.S3.Analytic.Asymptotics.GeometricRightUSCUniformization.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ F => F) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Asymptotics.GeometricRightUSCUniformization
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "arg", "body", "arg", "arg", "body",
        "arg", "body", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit
end
end Reg.D5.S3.Analytic.Asymptotics.GeometricRightUSCUniformization
