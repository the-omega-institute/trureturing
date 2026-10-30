import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.ZetaGamma.FormCore.RightExponentialTailGlobalL2
import Reg.Support.SingleDependentReadout

/-! Faithful source audits of the split-kernel estimate and global squared mass. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory Set
open _root_.D5.S3.Weil.ZetaGamma.FormCore.RightExponentialTail
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Weil.ZetaGamma.FormCore.RightExponentialTailGlobalL2

namespace SplitKernelSquare

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ z => z.re) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (-1 : ℝ)) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {k : ℝ} (_hk : 0 < k) (u : ℝ → ℂ)
      (_hu : MemLp u 2 (volume.restrict (Ioi 0))) (t : ℝ) (_ht : 0 ≤ t),
    ‖rightExponentialTail k u t‖ ^ 2 ≤
      k⁻¹ * R.readout () ()
        (rightExponentialTail k (fun x => ((‖u x‖ ^ 2 : ℝ) : ℂ)) t)

private theorem source_reconstruction :
    (type_of% (@right_exponential_tail_sq_le_tail_sq)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hall
  have h := hall (k := 1) (by norm_num) (fun _ : ℝ => (0 : ℂ)) MemLp.zero'
    0 (by norm_num)
  norm_num [rejected, realize, rightExponentialTail] at h

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change (0 : ℂ).re ≠ (1 : ℂ).re
  norm_num

def familyRegistration : Registration arena (type_of% (@right_exponential_tail_sq_le_tail_sq)) where
  actual := actual
  bridge := source_reconstruction
  variation := ⟨@right_exponential_tail_sq_le_tail_sq, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@right_exponential_tail_sq_le_tail_sq) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Weil.ZetaGamma.FormCore.RightExponentialTailGlobalL2.SplitKernelSquare.unit
  realizationName := `Reg.D5.S3.Weil.ZetaGamma.FormCore.RightExponentialTailGlobalL2.SplitKernelSquare.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => z.re) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaGamma.FormCore.RightExponentialTailGlobalL2
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms familyRegistration
#print axioms registration

end SplitKernelSquare

namespace GlobalMass

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ → ℂ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ u => ∫ t : ℝ in Ioi 0, ‖u t‖ ^ 2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (-1 : ℝ)) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {k : ℝ} (_hk : 0 < k) (u : ℝ → ℂ)
      (_hu : MemLp u 2 (volume.restrict (Ioi 0)))
      (_hm : AEStronglyMeasurable (rightExponentialTail k u)
        (volume.restrict (Ioi 0))),
    MemLp (rightExponentialTail k u) 2 (volume.restrict (Ioi 0)) ∧
      (∫ t : ℝ in Ioi 0, ‖rightExponentialTail k u t‖ ^ 2) ≤
        (k⁻¹) ^ 2 * R.readout () () u

private theorem source_reconstruction :
    (type_of% (@right_exponential_tail_memLp_two_and_mass_bound)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hall
  have hm : AEStronglyMeasurable
      (rightExponentialTail 1 (fun _ : ℝ => (0 : ℂ)))
      (volume.restrict (Ioi (0 : ℝ))) := by
    have heq : rightExponentialTail 1 (fun _ : ℝ => (0 : ℂ)) =
        fun _ : ℝ => (0 : ℂ) := by
      funext t
      simp [rightExponentialTail]
    rw [heq]
    exact aestronglyMeasurable_const
  have h := (hall (k := 1) (by norm_num) (fun _ : ℝ => (0 : ℂ)) MemLp.zero' hm).2
  norm_num [rejected, realize, rightExponentialTail] at h

private def indicatorInput : ℝ → ℂ :=
  (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℂ))

private theorem indicator_mass : (∫ x : ℝ in Ioi 0, ‖indicatorInput x‖ ^ 2) = 1 := by
  have heq : (fun x : ℝ => ‖indicatorInput x‖ ^ 2) =
      (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) := by
    funext x
    by_cases hx : x ∈ Ioc (0 : ℝ) 1 <;> simp [indicatorInput, hx]
  rw [heq, setIntegral_indicator measurableSet_Ioc,
    inter_eq_right.mpr Ioc_subset_Ioi_self, setIntegral_const]
  norm_num

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (fun _ : ℝ => (0 : ℂ)), indicatorInput, ?_⟩
  change (∫ t : ℝ in Ioi 0, ‖(0 : ℂ)‖ ^ 2) ≠
    ∫ t : ℝ in Ioi 0, ‖indicatorInput t‖ ^ 2
  rw [indicator_mass]
  norm_num

def familyRegistration : Registration arena (type_of% (@right_exponential_tail_memLp_two_and_mass_bound)) where
  actual := actual
  bridge := source_reconstruction
  variation := ⟨@right_exponential_tail_memLp_two_and_mass_bound, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@right_exponential_tail_memLp_two_and_mass_bound) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Weil.ZetaGamma.FormCore.RightExponentialTailGlobalL2.GlobalMass.unit
  realizationName := `Reg.D5.S3.Weil.ZetaGamma.FormCore.RightExponentialTailGlobalL2.GlobalMass.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ u => ∫ t : ℝ in Ioi 0, ‖u t‖ ^ 2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaGamma.FormCore.RightExponentialTailGlobalL2
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "arg", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms familyRegistration
#print axioms registration

end GlobalMass

end Reg.D5.S3.Weil.ZetaGamma.FormCore.RightExponentialTailGlobalL2
