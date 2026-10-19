import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.KyFanGap.UniformGap
import Reg.Support.SingleDependentReadout

/-! The positive lower-bound parameter is observed within the complete family. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators
open _root_.D5.S3.Combinatorics.Graph.KyFanGap
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
namespace Reg.D5.S3.Combinatorics.Graph.KyFanGap.UniformGap

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => Prop)
def actual : Realization signature :=
  realize signature (fun _ _ x => 0 < x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law T := ∀ {k : ℕ}, ¬ IsSquare k → ∀ (M : ℝ),
    ∃ η, T.readout () () η ∧ ∀ (n : ℕ), 0 < n →
      ∀ (q : Fin k → ℝ) (x : Fin n → Fin k → ℝ),
        (∀ r s, |bilinearKernel q (x r) (x s)| ≤ M) →
          η ≤ empiricalDefect q x (1 / Real.sqrt k)
private theorem rejectedLaw : ¬ arena.Law rejected := by
  intro h
  obtain ⟨η, hη, _⟩ := h Nat.prime_two.not_isSquare 0
  exact hη
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have hpos : (0 : ℝ) < 0 := he.mpr (by norm_num [actual, realize])
  exact lt_irrefl _ hpos
def family : Registration arena (type_of% (@bilinear_defect_gap)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@bilinear_defect_gap, rejected, rejectedLaw⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejectedLaw
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@bilinear_defect_gap) (Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.KyFanGap.bilinear_defect_gap.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.KyFanGap.UniformGap.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => 0 < x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.KyFanGap.UniformGap
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg", "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Graph.KyFanGap.UniformGap
