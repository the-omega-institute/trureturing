import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.KummerRatio.Transform
import Reg.Support.DependentFamily

/-! Complementary-parameter reflection as a varying Kummer evaluation family. -/

namespace Reg.D5.S3.Analytic.KummerRatio.Transform
open _root_.D5.S3.Analytic.KummerRatio.Defs
open _root_.D5.S3.Analytic.KummerRatio.Series
open _root_.D5.S3.Analytic.KummerRatio.Transform
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
noncomputable section

abbrev signature : Signature where
  Params := Σ _ : ℝ, ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p x => kummer p.1 p.2 x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {c : ℝ} (s : ℝ), 0 < c → ∀ x : ℝ,
    R.readout () ⟨s, c⟩ x = Real.exp x * kummer (c-s) c (-x)

private lemma rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := @h 1 1 (by norm_num) 0
  norm_num [rejected, realize, kummer_zero] at he

private lemma diagonal (x : ℝ) : kummer 1 1 x = Real.exp x := by
  rw [kummer, Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  apply tsum_congr
  intro n
  have hp : (ascPochhammer ℝ n).eval 1 ≠ 0 := (ascPochhammer_pos n 1 (by norm_num)).ne'
  rw [kummerCoeff, div_mul_eq_div_div, div_self hp]
  ring

private lemma dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1, 1⟩, 0, 1, ?_⟩
  intro he
  have h : Real.exp 0 = Real.exp 1 := by simpa [actual, realize, diagonal] using he
  have hz := Real.exp_injective h
  norm_num at hz

def family : Registration arena (type_of% @kummer_transform) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨kummer_transform, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def audit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@kummer_transform) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.KummerRatio.Transform.unit
  realizationName := `Reg.D5.S3.Analytic.KummerRatio.Transform.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p x => kummer p.1 p.2 x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.KummerRatio.Transform
    definition := none
    coordinates := #[1, 0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit
end
end Reg.D5.S3.Analytic.KummerRatio.Transform
