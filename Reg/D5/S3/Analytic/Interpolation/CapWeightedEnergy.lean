import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Interpolation.CapWeightedEnergy
import Reg.Support.SingleDependentReadout

/-! Faithful dependent registration of the actual integrability and norm bound. -/

noncomputable section
universe u
open MeasureTheory Set
open _root_.D5.S3.Analytic.Interpolation.CapWeightedEnergy
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Analytic.Interpolation.CapWeightedEnergy

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Prop) (fun _ => Prop → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ∧ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (w : ℝ → E) (alpha B delta : ℝ)
    (_halpha0 : 0 < alpha) (_halpha1 : alpha < 1) (_hB : 0 ≤ B) (_hdelta : 0 ≤ delta)
    (_hw : AEStronglyMeasurable w (volume.restrict (Ioi (0 : ℝ))))
    (_hcap : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), ‖w t‖ ≤ B)
    (_henergy : IntegrableOn (fun t : ℝ => t * ‖w t‖ ^ 2) (Ioi 0))
    (_hbudget : (∫ t in Ioi (0 : ℝ), t * ‖w t‖ ^ 2) ≤ delta),
    R.readout () ()
      (IntegrableOn (fun t : ℝ => t ^ (-alpha) • w t) (Ioi 0))
      (‖∫ t in Ioi (0 : ℝ), t ^ (-alpha) • w t‖ ≤
        sharpConstant alpha * B ^ alpha * delta ^ ((1 - alpha) / 2))

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact @h (ULift.{u} ℝ) inferInstance inferInstance inferInstance
    (fun _ => 0) (1 / 2) 0 0 (by norm_num) (by norm_num) le_rfl le_rfl
    aestronglyMeasurable_const
    (.of_forall (fun _ => by simp))
    (by simpa using (integrable_zero ℝ ℝ (volume.restrict (Ioi (0 : ℝ)))))
    (by simp)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), True, False, ?_⟩
  intro he
  have h := congrFun he True
  simp [actual, realize] at h

def family : Registration arena.{u}
    (type_of% @norm_integral_le_sharp_cap_energy.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@norm_integral_le_sharp_cap_energy, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@norm_integral_le_sharp_cap_energy.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Analytic.Interpolation.CapWeightedEnergy.norm_integral_le_sharp_cap_energy.__information_unit
  realizationName := `Reg.D5.S3.Analytic.Interpolation.CapWeightedEnergy.family
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
    owner := `D5.S3.Analytic.Interpolation.CapWeightedEnergy
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit


abbrev nearArena : Arena where
  signature := signature
  Law R := ∀ (alpha a : ℝ) (_halpha : alpha < 1) (_ha : 0 < a),
    R.readout () ()
      (IntegrableOn (fun t : ℝ => t ^ (-alpha)) (Ioc 0 a))
      ((∫ t in Ioc (0 : ℝ) a, t ^ (-alpha)) = a ^ (1 - alpha) / (1 - alpha))

private theorem near_rejected_law : ¬ nearArena.Law rejected := by
  intro h
  exact h 0 1 (by norm_num) (by norm_num)

def nearFamily : Registration nearArena (type_of% @power_integral_near) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@power_integral_near, rejected, near_rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    nearArena.Law actual rejected near_rejected_law
  dependence := dependence

def nearAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@power_integral_near) (Realization signature) Unit Unit where
  unitName := `D5.S3.Analytic.Interpolation.CapWeightedEnergy.power_integral_near.__information_unit
  realizationName := `Reg.D5.S3.Analytic.Interpolation.CapWeightedEnergy.nearFamily
  realizationSource := none
  generated := false
  arena := .source ⟨nearArena⟩
  objectArena := .source ⟨nearArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source nearArena ⟨nearFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ∧ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Interpolation.CapWeightedEnergy
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms nearFamily
#print axioms nearAudit

abbrev tailArena : Arena where
  signature := signature
  Law R := ∀ (alpha a : ℝ) (_halpha : 0 < alpha) (_ha : 0 < a),
    R.readout () ()
      (IntegrableOn (fun t : ℝ => t ^ (-2 * alpha - 1)) (Ioi a))
      ((∫ t in Ioi a, t ^ (-2 * alpha - 1)) = a ^ (-2 * alpha) / (2 * alpha))

private theorem tail_rejected_law : ¬ tailArena.Law rejected := by
  intro h
  exact h 1 1 (by norm_num) (by norm_num)

def tailFamily : Registration tailArena (type_of% @power_integral_tail) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@power_integral_tail, rejected, tail_rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    tailArena.Law actual rejected tail_rejected_law
  dependence := dependence

def tailAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@power_integral_tail) (Realization signature) Unit Unit where
  unitName := `D5.S3.Analytic.Interpolation.CapWeightedEnergy.power_integral_tail.__information_unit
  realizationName := `Reg.D5.S3.Analytic.Interpolation.CapWeightedEnergy.tailFamily
  realizationSource := none
  generated := false
  arena := .source ⟨tailArena⟩
  objectArena := .source ⟨tailArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source tailArena ⟨tailFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ∧ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Interpolation.CapWeightedEnergy
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms tailFamily
#print axioms tailAudit

abbrev linearArena : Arena where
  signature := signature
  Law R := ∀ (a : ℝ) (_ha : 0 < a),
    R.readout () ()
      (IntegrableOn (fun t : ℝ => t) (Ioc 0 a))
      ((∫ t in Ioc (0 : ℝ) a, t) = a ^ 2 / 2)

private theorem linear_rejected_law : ¬ linearArena.Law rejected := by
  intro h
  exact h 1 (by norm_num)

def linearFamily : Registration linearArena (type_of% @linear_integral_near) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@linear_integral_near, rejected, linear_rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    linearArena.Law actual rejected linear_rejected_law
  dependence := dependence

def linearAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@linear_integral_near) (Realization signature) Unit Unit where
  unitName := `D5.S3.Analytic.Interpolation.CapWeightedEnergy.linear_integral_near.__information_unit
  realizationName := `Reg.D5.S3.Analytic.Interpolation.CapWeightedEnergy.linearFamily
  realizationSource := none
  generated := false
  arena := .source ⟨linearArena⟩
  objectArena := .source ⟨linearArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source linearArena ⟨linearFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ∧ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Interpolation.CapWeightedEnergy
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms linearFamily
#print axioms linearAudit

end Reg.D5.S3.Analytic.Interpolation.CapWeightedEnergy
