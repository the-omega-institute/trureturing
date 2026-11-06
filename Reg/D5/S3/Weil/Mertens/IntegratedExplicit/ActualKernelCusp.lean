import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelCusp
import Reg.Support.SingleDependentReadout

/-! Observe the literal remainder, retaining the source interval and the right-sided limit. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Set Filter
open scoped Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelLocalPositivity
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelCusp
open LeanInformationAudit

namespace Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelCusp

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ t => R t) (fun e => nomatch e)

private theorem mass_lt_seven : firstLiMass < 7 := by
  rw [firstLiMass_split]
  have h₂ : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hπ : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.two_le_pi])
  linarith [Real.eulerMascheroniConstant_lt_two_thirds]

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  obtain ⟨t, ht⟩ : ∃ t : ℝ, R 0 ≠ R t := by
    by_contra hh
    push_neg at hh
    have hz (t : ℝ) : R t = 0 := by simpa [R, K_zero] using (hh t).symm
    have hl := cusp_quadratic_limit
    simp only [hz, zero_div] at hl
    have he : (0 : ℝ) = (firstLiMass - 7) / 8 :=
      tendsto_nhds_unique tendsto_const_nhds hl
    linarith [mass_lt_seven]
  exact ⟨(), 0, t, ht⟩

namespace Uniform

def arena : Arena where
  signature := signature
  Law A := ∀ {t : ℝ}, 0 < t → t ≤ 1 / 2 → |A.readout () () t| ≤ 2 * t ^ 2

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (t := 1 / 2) (by norm_num) le_rfl
  change |(1 : ℝ)| ≤ 2 * (1 / 2 : ℝ) ^ 2 at hh
  norm_num at hh

def evidence : Registration arena (type_of% @cusp_remainder_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@cusp_remainder_bound, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@cusp_remainder_bound) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelCusp.cusp_remainder_bound.__information_unit
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelCusp.Uniform.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ t => R t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelCusp
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms registration
end Uniform

namespace Quadratic

def arena : Arena where
  signature := signature
  Law A := Tendsto (fun t : ℝ => A.readout () () t / t ^ 2)
    (𝓝[>] 0) (𝓝 ((firstLiMass - 7) / 8))

def rejected : Realization signature :=
  realize signature (fun _ _ t => ((firstLiMass - 7) / 8 + 1) * t ^ 2)
    (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb : Tendsto
      (fun t : ℝ => ((firstLiMass - 7) / 8 + 1) * t ^ 2 / t ^ 2)
      (𝓝[>] 0) (𝓝 ((firstLiMass - 7) / 8 + 1)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    change 0 < t at ht
    field_simp [ht.ne']
  have he := tendsto_nhds_unique hb h
  linarith

def evidence : Registration arena (type_of% @cusp_quadratic_limit) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨cusp_quadratic_limit, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@cusp_quadratic_limit) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelCusp.cusp_quadratic_limit.__information_unit
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelCusp.Quadratic.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ t => R t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelCusp
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "fn", "arg", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms registration
end Quadratic

end Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelCusp
