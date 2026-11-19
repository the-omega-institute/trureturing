import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.Analytic.LogLogGlobalCurvatureStability
import Reg.Support.DependentFamily

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Arith.Robin.Analytic.LogLogGlobalCurvatureStability

open _root_.D5.S3.Arith.Robin.Analytic.LogLogGlobalCurvature
open _root_.D5.S3.Arith.Robin.Analytic.LogLogGlobalCurvatureStability
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Σ a : ℝ, ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature
    (fun _ p y =>
      |(Real.log (Real.log p.1) + (p.2 - p.1) / (p.1 * Real.log p.1) -
          Real.log (Real.log p.2)) -
        (Real.log (Real.log p.1) + (y - p.1) / (p.1 * Real.log p.1) -
          Real.log (Real.log y))|)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature
    (fun _ p y =>
      |(Real.log (Real.log p.1) + (p.2 - p.1) / (p.1 * Real.log p.1) -
          Real.log (Real.log p.2)) -
        (Real.log (Real.log p.1) + (y - p.1) / (p.1 * Real.log p.1) -
          Real.log (Real.log y))| + 1)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {a x y : ℝ}, 1 < a → 1 < x → 1 < y →
    let K := fun z : ℝ => Real.log (Real.log a) +
      (z - a) / (a * Real.log a) - Real.log (Real.log z)
    let w := fun t : ℝ => (1 + Real.log t) / (t ^ 2 * (Real.log t) ^ 2)
    let c := min a (min x y)
    let M := |x - y|
    let d := |y - a|
    R.readout () ⟨a, x⟩ y ≤ w c * (d * M + M ^ 2 / 2)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h (a := 2) (x := 2) (y := 2) (by norm_num) (by norm_num)
    (by norm_num)
  dsimp only [rejected, realize] at hbad
  norm_num [sub_self, abs_zero] at hbad

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro _i
  refine ⟨⟨2, 2⟩, (2 : ℝ), (3 : ℝ), ?_⟩
  change
    |(Real.log (Real.log 2) + (2 - 2) / (2 * Real.log 2) -
        Real.log (Real.log 2)) -
      (Real.log (Real.log 2) + (2 - 2) / (2 * Real.log 2) -
        Real.log (Real.log 2))| ≠
    |(Real.log (Real.log 2) + (2 - 2) / (2 * Real.log 2) -
        Real.log (Real.log 2)) -
      (Real.log (Real.log 2) + (3 - 2) / (2 * Real.log 2) -
        Real.log (Real.log 3))|
  have h2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have h3 : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  have hbound := loglog_tangent_gap_quadratic
    (a := (2 : ℝ)) (b := (3 : ℝ)) (by norm_num) (by norm_num)
  dsimp only at hbound
  have hbound' : 0 <
      Real.log (Real.log (2 : ℝ)) + (3 - 2) / (2 * Real.log 2) -
        Real.log (Real.log 3) := by
    have hleft : 0 <
        (1 + Real.log (3 : ℝ)) /
            (9 * (Real.log (3 : ℝ)) ^ 2) / 2 := by
      positivity
    have hbound'' := hbound.1
    norm_num [max_eq_right, min_eq_left] at hbound''
    have hpos := lt_of_lt_of_le hleft hbound''
    convert hpos using 1 <;> ring
  have hrightpos : 0 <
      |(Real.log (Real.log 2) + (2 - 2) / (2 * Real.log 2) -
          Real.log (Real.log 2)) -
        (Real.log (Real.log 2) + (3 - 2) / (2 * Real.log 2) -
          Real.log (Real.log 3))| := by
    have hzero :
        Real.log (Real.log (2 : ℝ)) + (2 - 2) / (2 * Real.log 2) -
          Real.log (Real.log 2) = 0 := by ring
    rw [hzero]
    have hneg : 0 -
        (Real.log (Real.log 2) + (3 - 2) / (2 * Real.log 2) -
          Real.log (Real.log 3)) < 0 := by linarith
    rw [abs_of_neg hneg]
    linarith
  simpa only [sub_self, abs_zero] using (ne_of_gt hrightpos).symm

def family : Registration arena
    (type_of% (@loglog_tangent_gap_stability)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@loglog_tangent_gap_stability, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@loglog_tangent_gap_stability) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.LogLogGlobalCurvatureStability.loglog_tangent_gap_stability.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.LogLogGlobalCurvatureStability.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.Analytic.LogLogGlobalCurvatureStability
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

namespace Scaled

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {a x y : ℝ}, Real.exp 2 ≤ a → a / 2 ≤ x → a / 2 ≤ y →
    let K := fun z : ℝ => Real.log (Real.log a) +
      (z - a) / (a * Real.log a) - Real.log (Real.log z)
    let M := |x - y|
    let d := |y - a|
    R.readout () ⟨a, x⟩ y ≤
      (16 / (a ^ 2 * Real.log a)) * (d * M + M ^ 2 / 2)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h (a := Real.exp 2) (x := Real.exp 2) (y := Real.exp 2)
    le_rfl (by linarith [Real.exp_pos (2 : ℝ)])
    (by linarith [Real.exp_pos (2 : ℝ)])
  dsimp only [rejected, realize] at hbad
  norm_num [sub_self, abs_zero] at hbad

def family : Registration arena
    (type_of% (@loglog_tangent_gap_stability_scaled)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@loglog_tangent_gap_stability_scaled, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@loglog_tangent_gap_stability_scaled) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.LogLogGlobalCurvatureStability.loglog_tangent_gap_stability_scaled.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.LogLogGlobalCurvatureStability.Scaled.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.Analytic.LogLogGlobalCurvatureStability
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Scaled
end Reg.D5.S3.Arith.Robin.Analytic.LogLogGlobalCurvatureStability
