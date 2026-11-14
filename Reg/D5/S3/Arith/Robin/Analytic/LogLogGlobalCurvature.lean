import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.Analytic.LogLogGlobalCurvature
import Reg.Support.DependentFamily

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Arith.Robin.Analytic.LogLogGlobalCurvature

open _root_.D5.S3.Arith.Robin.Analytic.LogLogGlobalCurvature
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature
    (fun _ a b => Real.log (Real.log a) + (b - a) / (a * Real.log a) -
      Real.log (Real.log b))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature
    (fun _ a b => Real.log (Real.log a) + (b - a) / (a * Real.log a) -
      Real.log (Real.log b) + 1)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {a b : ℝ}, 1 < a → 1 < b →
    let K := Real.log (Real.log a) + (b - a) / (a * Real.log a) -
      Real.log (Real.log b)
    let w := fun t : ℝ => (1 + Real.log t) / (t ^ 2 * (Real.log t) ^ 2)
    w (max a b) * (b - a) ^ 2 / 2 ≤ R.readout () a b ∧
      R.readout () a b ≤ w (min a b) * (b - a) ^ 2 / 2

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h (a := 2) (b := 2) (by norm_num) (by norm_num)
  dsimp only [rejected, realize] at hbad
  have hbad' := hbad.2
  norm_num [max_self, min_self, sub_self, abs_zero] at hbad'

def family : Registration arena
    (type_of% (@loglog_tangent_gap_quadratic)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@loglog_tangent_gap_quadratic, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro _i
    refine ⟨2, 2, 3, ?_⟩
    change
      (Real.log (Real.log 2) + (2 - 2) / (2 * Real.log 2) -
        Real.log (Real.log 2)) ≠
      (Real.log (Real.log 2) + (3 - 2) / (2 * Real.log 2) -
        Real.log (Real.log 3))
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
    have hzero :
        Real.log (Real.log (2 : ℝ)) + (2 - 2) / (2 * Real.log 2) -
          Real.log (Real.log 2) = 0 := by ring
    rw [hzero]
    exact (ne_of_gt hbound').symm

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@loglog_tangent_gap_quadratic) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.LogLogGlobalCurvature.loglog_tangent_gap_quadratic.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.LogLogGlobalCurvature.family
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
    owner := `D5.S3.Arith.Robin.Analytic.LogLogGlobalCurvature
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "fn", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end Reg.D5.S3.Arith.Robin.Analytic.LogLogGlobalCurvature
