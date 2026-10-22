import LeanInformationAuditInterface.Contract.Registration
import D5.S3.TotalVariation.Asymptotics.GaussianCoshKernel
import Reg.Support.SingleDependentReadout

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.TotalVariation.Asymptotics.GaussianCoshKernel
open StatLean.HypothesisTesting LeanInformationAudit MeasureTheory Set

noncomputable section
namespace Reg.D5.S3.TotalVariation.Asymptotics.GaussianCoshKernel

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => |x|) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law F := ∀ lo hi : ℝ, 0 < lo →
    ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧
      ∀ q ∈ Icc lo hi, ∀ d : ℝ, 0 < d → d ≤ δ →
        Integrable (fun u : ℝ =>
          stdNormalPDF u * max (Real.exp d - Real.cosh (q * u)) 0) ∧
        F.readout () () (gaussianCoshIntegral q d -
          (4 * Real.sqrt 2 * stdNormalPDF 0 / (3 * q)) * d ^ (3 / 2 : ℝ)) ≤
            C * d ^ (5 / 2 : ℝ)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨δ, C, hδ, hC, hb⟩ := h 1 1 (by norm_num)
  let d := min δ (1 / (2 * (C + 1)))
  have hp : 0 < 2 * (C + 1) := by positivity
  have hd : 0 < d := lt_min hδ (by positivity)
  have hdle : d ≤ 1 / (2 * (C + 1)) := min_le_right _ _
  have hd1 : d ≤ 1 := hdle.trans ((div_le_iff₀ hp).2 (by linarith))
  have hpow : d ^ (5 / 2 : ℝ) ≤ d :=
    Real.rpow_le_self_of_le_one hd.le hd1 (by norm_num)
  have hh := (hb 1 (by norm_num) d hd (min_le_left _ _)).2
  change (1 : ℝ) ≤ C * d ^ (5 / 2 : ℝ) at hh
  have hCd : C * d ≤ C / (2 * (C + 1)) := by
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hdle hC
  have hsmall : C / (2 * (C + 1)) < 1 := (div_lt_iff₀ hp).2 (by linarith)
  have hm := mul_le_mul_of_nonneg_left hpow hC
  linarith

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change |(0 : ℝ)| ≠ |(1 : ℝ)|
  norm_num

def family : Registration arena (type_of% (@gaussian_cosh_uniform_remainder)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨gaussian_cosh_uniform_remainder, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@gaussian_cosh_uniform_remainder) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.TotalVariation.Asymptotics.GaussianCoshKernel.unit
  realizationName := `Reg.D5.S3.TotalVariation.Asymptotics.GaussianCoshKernel.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => |x|) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.TotalVariation.Asymptotics.GaussianCoshKernel
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg", "body", "arg", "body", "arg", "arg",
        "body", "body", "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.TotalVariation.Asymptotics.GaussianCoshKernel

namespace Reg.D5.S3.TotalVariation.Asymptotics.GaussianCoshKernel.Integrability

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ u => stdNormalPDF u) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law F := ∀ q d : ℝ, Integrable
    (fun u : ℝ => F.readout () () u * max (Real.exp d - Real.cosh (q * u)) 0)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 0 1
  have hp : 0 < max (Real.exp 1 - 1) 0 := lt_max_iff.2 (Or.inl (by
    have he := Real.exp_lt_exp.mpr (show (0 : ℝ) < 1 by norm_num)
    rw [Real.exp_zero] at he
    linarith))
  have hn : ¬ Integrable (fun _ : ℝ => max (Real.exp 1 - 1) 0) := by
    simpa [integrable_const_iff, isFiniteMeasure_iff] using hp.ne'
  apply hn
  simpa [rejected, realize] using hh

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change stdNormalPDF 0 ≠ stdNormalPDF 1
  unfold stdNormalPDF
  apply ne_of_gt
  apply (div_lt_div_iff_of_pos_right (Real.sqrt_pos.2 (by positivity))).2
  apply Real.exp_lt_exp.mpr
  norm_num

def family : Registration arena (type_of% (@kernel_integrable)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨kernel_integrable, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@kernel_integrable) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.TotalVariation.Asymptotics.GaussianCoshKernel.Integrability.unit
  realizationName := `Reg.D5.S3.TotalVariation.Asymptotics.GaussianCoshKernel.Integrability.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ u => stdNormalPDF u) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.TotalVariation.Asymptotics.GaussianCoshKernel
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.TotalVariation.Asymptotics.GaussianCoshKernel.Integrability
