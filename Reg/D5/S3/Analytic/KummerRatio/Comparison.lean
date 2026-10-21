import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.KummerRatio.Comparison
import D5.S3.Analytic.KummerRatio.Series
import Reg.Support.SingleDependentReadout

open _root_.D5.S3.Analytic.KummerRatio.Comparison
open _root_.D5.S3.Analytic.KummerRatio.Defs
open _root_.D5.S3.Analytic.KummerRatio.Series
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Set

namespace Reg.D5.S3.Analytic.KummerRatio.Comparison
noncomputable section

namespace Generic

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature
    (Σ _ : ℝ → ℝ → ℝ, Σ _ : ℝ, Σ _ : ℝ, ℝ) (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ q x =>
    q.1 (q.2.2.1 + q.2.2.2) x * q.1 q.2.1 x /
      (q.1 (q.2.1 + q.2.2.2) x * q.1 q.2.2.1 x)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {c : ℝ} {y dy ddy : ℝ → ℝ → ℝ} {a b δ : ℝ}
    (_H : SolutionFamily c y dy ddy) (_hc : 0 < c)
    (_ha : 0 < a) (_hab : a < b) (_hδ : 0 < δ),
    StrictAntiOn (R.readout () ⟨y, a, b, δ⟩) (Ioi 0)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hm := h (a := 1) (b := 2) (δ := 1)
    (_root_.D5.S3.Analytic.KummerRatio.Comparison.kummer_family (by norm_num : (0 : ℝ) < 1))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hh := hm (show (1 : ℝ) ∈ Ioi 0 by norm_num)
    (show (2 : ℝ) ∈ Ioi 0 by norm_num) (by norm_num : (1 : ℝ) < 2)
  exact (lt_irrefl (0 : ℝ)) hh

def family : Registration arena (type_of% @solution_ratio_strictAntiOn) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@solution_ratio_strictAntiOn, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    change ObservationalDependence signature actual
    intro i
    refine ⟨⟨fun s x : ℝ => s + x, 1, 2, 1⟩, 0, 1, ?_⟩
    norm_num [actual, realize]

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@solution_ratio_strictAntiOn) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.KummerRatio.Comparison.Generic.unit
  realizationName := `Reg.D5.S3.Analytic.KummerRatio.Comparison.Generic.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ q x =>
    q.1 (q.2.2.1 + q.2.2.2) x * q.1 q.2.1 x /
      (q.1 (q.2.1 + q.2.2.2) x * q.1 q.2.2.1 x)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.KummerRatio.Comparison
    definition := none
    coordinates := #[1, 4, 5, 6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Generic

namespace Kummer

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature
    (Σ _ : ℝ, Σ _ : ℝ, Σ _ : ℝ, ℝ) (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ q x => ratio q.1 q.2.1 q.2.2.1 q.2.2.2 x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {a b c δ : ℝ} (_ha : 0 < a) (_hab : a < b) (_hc : 0 < c) (_hδ : 0 < δ),
    StrictAntiOn (R.readout () ⟨a, b, c, δ⟩) (Ioi 0)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hm := h (a := 1) (b := 2) (c := 1) (δ := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hh := hm (show (1 : ℝ) ∈ Ioi 0 by norm_num)
    (show (2 : ℝ) ∈ Ioi 0 by norm_num) (by norm_num : (1 : ℝ) < 2)
  exact (lt_irrefl (0 : ℝ)) hh

def family : Registration arena (type_of% @ratio_strictAntiOn) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@ratio_strictAntiOn, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    change ObservationalDependence signature actual
    intro i
    refine ⟨⟨1, 2, 1, 1⟩, 1, 2, ?_⟩
    exact ne_of_gt (ratio_strictAntiOn (by norm_num : (0 : ℝ) < 1)
      (by norm_num : (1 : ℝ) < 2) (by norm_num : (0 : ℝ) < 1)
      (by norm_num : (0 : ℝ) < 1) (by norm_num : (1 : ℝ) ∈ Ioi 0)
      (by norm_num : (2 : ℝ) ∈ Ioi 0) (by norm_num : (1 : ℝ) < 2))

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@ratio_strictAntiOn) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.KummerRatio.Comparison.Kummer.unit
  realizationName := `Reg.D5.S3.Analytic.KummerRatio.Comparison.Kummer.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ q x => ratio q.1 q.2.1 q.2.2.1 q.2.2.2 x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.KummerRatio.Comparison
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Kummer

end
end Reg.D5.S3.Analytic.KummerRatio.Comparison
