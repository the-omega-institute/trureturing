import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Interpolation.CapWeightedEnergySharpness
import Reg.Support.SingleDependentReadout

noncomputable section
open MeasureTheory Set
open _root_.D5.S3.Analytic.Interpolation.CapWeightedEnergy
open _root_.D5.S3.Analytic.Interpolation.CapWeightedEnergySharpness
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Analytic.Interpolation.CapWeightedEnergySharpness

namespace Moments

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Prop) (fun _ => Prop → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ∧ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (alpha B a : ℝ) (_halpha0 : 0 < alpha) (_halpha1 : alpha < 1)
      (_hB : 0 ≤ B) (_ha : 0 < a),
    R.readout () ()
      (AEStronglyMeasurable (extremizer alpha B a) (volume.restrict (Ioi (0 : ℝ))))
      ((∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), ‖extremizer alpha B a t‖ ≤ B) ∧
        (IntegrableOn (fun t : ℝ => t * ‖extremizer alpha B a t‖ ^ 2) (Ioi 0) ∧
          (∫ t in Ioi (0 : ℝ), t * ‖extremizer alpha B a t‖ ^ 2) =
            B ^ 2 * a ^ 2 * ((alpha + 1) / (2 * alpha))) ∧
        (IntegrableOn (fun t : ℝ => t ^ (-alpha) * extremizer alpha B a t) (Ioi 0) ∧
          (∫ t in Ioi (0 : ℝ), t ^ (-alpha) * extremizer alpha B a t) =
            B * a ^ (1 - alpha) * (1 / (1 - alpha) + 1 / (2 * alpha))))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (1 / 2) 0 1 (by norm_num) (by norm_num) le_rfl (by norm_num)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), True, False, ?_⟩
  intro he
  have h := congrFun he True
  simp [actual, realize] at h

def family : Registration arena (type_of% @extremizer_admissible_and_moments) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@extremizer_admissible_and_moments, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@extremizer_admissible_and_moments) (Realization signature) Unit Unit where
  unitName := `D5.S3.Analytic.Interpolation.CapWeightedEnergySharpness.extremizer_admissible_and_moments.__information_unit
  realizationName := `Reg.D5.S3.Analytic.Interpolation.CapWeightedEnergySharpness.Moments.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ∧ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Interpolation.CapWeightedEnergySharpness
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Moments

namespace Optimality

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (alpha C : ℝ) (_halpha0 : 0 < alpha) (_halpha1 : alpha < 1)
    (_huniform : ∀ (w : ℝ → ℝ) (B delta : ℝ), 0 ≤ B → 0 ≤ delta →
      AEStronglyMeasurable w (volume.restrict (Ioi (0 : ℝ))) →
      (∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), ‖w t‖ ≤ B) →
      IntegrableOn (fun t : ℝ => t * ‖w t‖ ^ 2) (Ioi 0) →
      (∫ t in Ioi (0 : ℝ), t * ‖w t‖ ^ 2) ≤ delta →
      ‖∫ t in Ioi (0 : ℝ), t ^ (-alpha) * w t‖ ≤
        C * B ^ alpha * delta ^ ((1 - alpha) / 2)),
    R.readout () () (sharpConstant alpha) C

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  apply h (1 / 2) (sharpConstant (1 / 2)) (by norm_num) (by norm_num)
  intro w B delta hB hdelta hw hcap henergy hbudget
  simpa only [smul_eq_mul] using
    (norm_integral_le_sharp_cap_energy w (1 / 2) B delta (by norm_num) (by norm_num)
      hB hdelta hw hcap henergy hbudget).2

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have h := congrFun he 0
  norm_num [actual, realize] at h

def family : Registration arena (type_of% @sharp_constant_le_of_uniform_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@sharp_constant_le_of_uniform_bound, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@sharp_constant_le_of_uniform_bound) (Realization signature) Unit Unit where
  unitName := `D5.S3.Analytic.Interpolation.CapWeightedEnergySharpness.sharp_constant_le_of_uniform_bound.__information_unit
  realizationName := `Reg.D5.S3.Analytic.Interpolation.CapWeightedEnergySharpness.Optimality.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Interpolation.CapWeightedEnergySharpness
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Optimality

#print axioms Moments.family
#print axioms Optimality.family

end Reg.D5.S3.Analytic.Interpolation.CapWeightedEnergySharpness
