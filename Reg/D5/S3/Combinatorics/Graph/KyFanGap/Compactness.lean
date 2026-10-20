import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.KyFanGap.Compactness
import Reg.Support.SingleDependentReadout

/-! The positive lower-bound parameter is observed within the complete family. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators
open _root_.D5.S3.Combinatorics.Graph.KyFanGap
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
namespace Reg.D5.S3.Combinatorics.Graph.KyFanGap.Compactness

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature :=
  realize signature (fun _ _ x y => x > y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law T := ∀ (R : ℕ) (M : ℝ) {k : ℕ}, ¬ IsSquare k →
    ∃ η, T.readout () () η 0 ∧ ∀ (p : Fin R → ℝ) (S : Matrix (Fin R) (Fin R) ℝ),
      (∀ a, 0 ≤ p a) → (∑ a, p a) = 1 → S.IsSymm →
      (∀ a b, |S a b| ≤ M) → η ≤ modelDefect p S (1 / Real.sqrt k)
private theorem rejectedLaw : ¬ arena.Law rejected := by
  intro h
  obtain ⟨η, hη, _⟩ := h 1 1 Nat.prime_two.not_isSquare
  exact hη
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have h := congrFun he (0 : ℝ)
  norm_num [actual, realize] at h
def family : Registration arena (type_of% (@exists_model_defect_gap)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_model_defect_gap, rejected, rejectedLaw⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejectedLaw
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exists_model_defect_gap) (Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.KyFanGap.exists_model_defect_gap.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.KyFanGap.Compactness.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x > y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.KyFanGap.Compactness
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Graph.KyFanGap.Compactness
