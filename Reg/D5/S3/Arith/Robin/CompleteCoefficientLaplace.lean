import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.CompleteCoefficientLaplace
import Reg.Support.DependentFamily

/- SOURCE ONLY / UNCOMPILED, including every definition and proof below.
This is a faithful dependent-family evidence ATTEMPT, not declared_validated.
The real input axis and the entire source telescope are retained. The missing
sourceSelection is intentional: compiler-derived occurrence binding and the
current E1--E8/binding evidence must be supplied by the caller after compilation.
No template failure or applicability of issue #5214 has been established. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Arith.Robin.CompleteCoefficientLaplace

open Set MeasureTheory
open _root_.D5.S3.Arith.Robin.CompleteCoefficientLaplace
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature where
  Params := ℂ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ s u => physicalIntegrand s u) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

/-- Vary the physical-integrability observation while retaining every other clause
of the complete theorem. This is the full original law, not a norm-only surrogate. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {A : ℝ} {s : ℂ}, 1 < A → 0 < s.re → s.re < 1 →
    IntegrableOn (R.readout () s) (Ioi A) ∧
    coefficient A s = s⁻¹ * (∫ x in Ioi (Real.log A), logIntegrand s x) ∧
    Integrable (kernel s)
      ((volume.restrict (Ioi (Real.log A))).prod (volume.restrict (Ioi (0 : ℝ)))) ∧
    IntegrableOn (resolventIntegrand (Real.log A) s) (Ioi (0 : ℝ)) ∧
    coefficient A s = (A : ℂ) ^ (s - 1) / s *
      (∫ t in Ioi (0 : ℝ), resolventIntegrand (Real.log A) s t) ∧
    ‖coefficient A s‖ ≤
      A ^ (s.re - 1) * logWeight (Real.log A) / (‖s‖ * ‖1 - s‖)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hi : IntegrableOn (fun _ : ℝ => (1 : ℂ)) (Ioi (2 : ℝ)) :=
    (h (A := 2) (s := 1 / 2) (by norm_num) (by norm_num) (by norm_num)).1
  simpa [integrableOn_const_iff, Real.volume_Ioi] using hi

def family : Registration arena (type_of% (@complete_coefficient_laplace)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@complete_coefficient_laplace, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j different
      exact (different (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    -- Both observations lie on the physical positive-log axis, at a valid strip s.
    refine ⟨(1 / 2 : ℂ), Real.exp 1, Real.exp 2, ?_⟩
    change physicalIntegrand (1 / 2) (Real.exp 1) ≠
      physicalIntegrand (1 / 2) (Real.exp 2)
    have hn1 : ‖physicalIntegrand (1 / 2) (Real.exp 1)‖ =
        Real.exp (-(3 / 2 : ℝ)) * 2 := by
      rw [physicalIntegrand, norm_mul,
        Complex.norm_cpow_eq_rpow_re_of_pos (Real.exp_pos 1),
        Complex.norm_real, Real.norm_eq_abs]
      norm_num [Real.log_exp, Real.rpow_def_of_pos (Real.exp_pos 1)]
    have hn2 : ‖physicalIntegrand (1 / 2) (Real.exp 2)‖ =
        Real.exp (-3) * (3 / 4 : ℝ) := by
      rw [physicalIntegrand, norm_mul,
        Complex.norm_cpow_eq_rpow_re_of_pos (Real.exp_pos 2),
        Complex.norm_real, Real.norm_eq_abs]
      norm_num [Real.log_exp, Real.rpow_def_of_pos (Real.exp_pos 2)]
    have he : Real.exp (-3) < Real.exp (-(3 / 2 : ℝ)) :=
      Real.exp_lt_exp.mpr (by norm_num)
    intro h
    have hn := congrArg norm h
    rw [hn1, hn2] at hn
    linarith [Real.exp_pos (-3)]

/-- Four-slot source attempt. The absent source selection and absent compiled
binding evidence prevent any assertion of validated registration. -/
def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@complete_coefficient_laplace)
    (type_of% (realize signature actual.readout actual.anchor)) (type_of% ℝ) Unit where
  unitName := `D5.S3.Arith.Robin.CompleteCoefficientLaplace.complete_coefficient_laplace.__information_unit
  realizationName := `Reg.D5.S3.Arith.Robin.CompleteCoefficientLaplace.family
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
  escapeFrom := some ℝ
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Arith.Robin.CompleteCoefficientLaplace
