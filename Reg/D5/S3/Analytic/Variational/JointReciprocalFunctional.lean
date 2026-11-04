import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Variational.JointReciprocalFunctional
import Reg.Support.SingleDependentReadout

open Set MeasureTheory
open scoped ContDiff
open _root_.D5.S3.Analytic.Variational.JointReciprocalFunctional
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Analytic.Variational.JointReciprocalFunctional

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature := realize signature (fun _ _ z => z) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def rootArena : Arena where
  signature := signature
  Law R := ∀ (b : ℝ), 0 < b → b ≤ 1 →
    ∃! v : ℝ, 0 < v ∧ v < upperRoot b ∧
      R.readout () () (coordinate b v) = Real.log 2

private theorem rejected_root : ¬ rootArena.Law rejected := by
  intro h
  obtain ⟨v, hv, _⟩ := h 1 (by norm_num) le_rfl
  have heq : (0 : ℝ) = Real.log 2 := hv.2.2
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  linarith

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize]

def rootFamily : Registration rootArena (type_of% exists_unique_scalar_root) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨exists_unique_scalar_root, rejected, rejected_root⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    rootArena.Law actual rejected rejected_root
  dependence := actual_dependence

def rootAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    exists_unique_scalar_root (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.Variational.JointReciprocalFunctional.rootUnit
  realizationName := `Reg.D5.S3.Analytic.Variational.JointReciprocalFunctional.rootFamily
  realizationSource := none
  generated := false
  arena := .source ⟨rootArena⟩
  objectArena := .source ⟨rootArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source rootArena ⟨rootFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

def profileArena : Arena where
  signature := signature
  Law R := ∀ (b : ℝ), 0 < b → b ≤ 1 →
    0 < scalarRoot b ∧ scalarRoot b < upperRoot b ∧
    coordinate b (scalarRoot b) = Real.log 2 ∧ 0 < sharpConstant b ∧
    ∃ s : Set ℝ, IsOpen s ∧ Icc (1 : ℝ) 2 ⊆ s ∧
      ContDiffOn ℝ ∞ (optimizer b) s ∧
      (∀ x ∈ s, 0 < optimizer b x) ∧ StrictMonoOn (optimizer b) s ∧
      Admissible (optimizer b) ∧ mass (optimizer b) = 1 ∧
      R.readout () () (cost b (optimizer b)) = sharpConstant b

private theorem rejected_profile : ¬ profileArena.Law rejected := by
  intro h
  obtain ⟨_, _, _, hC, s, _, _, _, _, _, _, _, heq⟩ := h 1 (by norm_num) le_rfl
  change (0 : ℝ) = sharpConstant 1 at heq
  linarith

def profileFamily : Registration profileArena (type_of% constructed_profile) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨constructed_profile, rejected, rejected_profile⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    profileArena.Law actual rejected rejected_profile
  dependence := actual_dependence

def profileAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    constructed_profile (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.Variational.JointReciprocalFunctional.profileUnit
  realizationName := `Reg.D5.S3.Analytic.Variational.JointReciprocalFunctional.profileFamily
  realizationSource := none
  generated := false
  arena := .source ⟨profileArena⟩
  objectArena := .source ⟨profileArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source profileArena ⟨profileFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

def variationalArena : Arena where
  signature := signature
  Law R := ∀ (b : ℝ), 0 < b → b ≤ 1 →
    let C := R.readout () () (sharpConstant b)
    0 < C ∧
    (∀ u : ℝ → ℝ, Admissible u → C ≤ mass u * cost b u) ∧
    IsLeast {y : ℝ | ∃ u : ℝ → ℝ, Admissible u ∧ mass u * cost b u = y}
      (C) ∧
    sInf {y : ℝ | ∃ u : ℝ → ℝ, Admissible u ∧ mass u * cost b u = y} =
      C ∧
    (∀ a : ℝ, 0 < a → Admissible (fun x => a * optimizer b x) ∧
      mass (fun x => a * optimizer b x) * cost b (fun x => a * optimizer b x) =
        C) ∧
    ∀ d : ℝ, 0 < d →
      IsLeast {y : ℝ | ∃ u : ℝ → ℝ, Admissible u ∧
        d / 8 * (4 * mass u + cost b u) = y} (d / 2 * Real.sqrt (C)) ∧
      sInf {y : ℝ | ∃ u : ℝ → ℝ, Admissible u ∧
        d / 8 * (4 * mass u + cost b u) = y} = d / 2 * Real.sqrt (C) ∧
      Admissible (fun x => Real.sqrt (C) / 2 * optimizer b x) ∧
      d / 8 * (4 * mass (fun x => Real.sqrt (C) / 2 * optimizer b x) +
        cost b (fun x => Real.sqrt (C) / 2 * optimizer b x)) =
          d / 2 * Real.sqrt (C)

private theorem rejected_variational : ¬ variationalArena.Law rejected := by
  intro h
  have hp := (h 1 (by norm_num) le_rfl).1
  change (0 : ℝ) < 0 at hp
  exact (lt_irrefl 0) hp

def variationalFamily : Registration variationalArena (type_of% sharp_joint_variational) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨sharp_joint_variational, rejected, rejected_variational⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    variationalArena.Law actual rejected rejected_variational
  dependence := actual_dependence

def variationalAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    sharp_joint_variational (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.Variational.JointReciprocalFunctional.variationalUnit
  realizationName := `Reg.D5.S3.Analytic.Variational.JointReciprocalFunctional.variationalFamily
  realizationSource := none
  generated := false
  arena := .source ⟨variationalArena⟩
  objectArena := .source ⟨variationalArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source variationalArena ⟨variationalFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]


abbrev energySignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℝ) (fun _ => ℝ)

def energyActual : Realization energySignature :=
  realize energySignature (fun _ b z => b * z) (fun e => nomatch e)

def energyRejected : Realization energySignature :=
  realize energySignature (fun _ b z => b * z + 1) (fun e => nomatch e)

private theorem energy_dependence : ObservationalDependence energySignature energyActual := by
  intro i
  refine ⟨1, 0, 1, ?_⟩
  norm_num [energyActual, realize]

def normalizedArena : Arena where
  signature := energySignature
  Law R := ∀ (b : ℝ), 0 < b → b ≤ 1 → ∀ {u : ℝ → ℝ}, Admissible u → mass u = 1 →
    IntervalIntegrable (energyDensity b u) volume 1 2 ∧
    0 ≤ energy b u ∧
    sharpConstant b + R.readout () b (energy b u) ≤ cost b u ∧
    (energy b u = 0 ↔
      u =ᵐ[volume.restrict (Icc (1 : ℝ) 2)] optimizer b) ∧
    (cost b u = sharpConstant b ↔ u =ᵐ[volume.restrict (Icc (1 : ℝ) 2)] optimizer b)

private theorem rejected_normalized : ¬ normalizedArena.Law energyRejected := by
  intro h
  obtain ⟨_, _, _, _, s, _, _, _, _, _, hw, hm, hc⟩ := constructed_profile 1 (by norm_num) le_rfl
  have hE := (normalized_stability 1 (by norm_num) le_rfl hw hm).2.2.2.1.2
    (Filter.EventuallyEq.rfl : optimizer 1 =ᵐ[volume.restrict (Icc (1 : ℝ) 2)] optimizer 1)
  have he := (h 1 (by norm_num) le_rfl hw hm).2.2.1
  change sharpConstant 1 + (1 * energy 1 (optimizer 1) + 1) ≤ cost 1 (optimizer 1) at he
  rw [hE, hc] at he
  linarith

def normalizedFamily : Registration normalizedArena (type_of% normalized_stability) where
  actual := energyActual
  bridge := Iff.rfl
  variation := ⟨normalized_stability, energyRejected, rejected_normalized⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    normalizedArena.Law energyActual energyRejected rejected_normalized
  dependence := energy_dependence

def normalizedAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    normalized_stability (Realization energySignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.Variational.JointReciprocalFunctional.normalizedUnit
  realizationName := `Reg.D5.S3.Analytic.Variational.JointReciprocalFunctional.normalizedFamily
  realizationSource := none
  generated := false
  arena := .source ⟨normalizedArena⟩
  objectArena := .source ⟨normalizedArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source normalizedArena ⟨normalizedFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize energySignature (fun _ b z => b * z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Variational.JointReciprocalFunctional
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
      "arg", "arg", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def stabilityArena : Arena where
  signature := energySignature
  Law R := ∀ (b : ℝ), 0 < b → b ≤ 1 → ∀ {u : ℝ → ℝ}, Admissible u →
    let v := fun x => (mass u)⁻¹ * u x
    0 < mass u ∧ IntervalIntegrable (energyDensity b v) volume 1 2 ∧
    0 ≤ energy b v ∧
    R.readout () b (energy b v) ≤ mass u * cost b u - sharpConstant b ∧
    (mass u * cost b u = sharpConstant b ↔
      u =ᵐ[volume.restrict (Icc (1 : ℝ) 2)] (fun x => mass u * optimizer b x)) ∧
    (mass u * cost b u = sharpConstant b ↔
      ∃ a : ℝ, 0 < a ∧ u =ᵐ[volume.restrict (Icc (1 : ℝ) 2)] (fun x => a * optimizer b x))

private theorem rejected_stability : ¬ stabilityArena.Law energyRejected := by
  intro h
  obtain ⟨_, _, _, _, s, _, _, _, _, _, hw, hm, hc⟩ := constructed_profile 1 (by norm_num) le_rfl
  have hE := (normalized_stability 1 (by norm_num) le_rfl hw hm).2.2.2.1.2
    (Filter.EventuallyEq.rfl : optimizer 1 =ᵐ[volume.restrict (Icc (1 : ℝ) 2)] optimizer 1)
  have he := (h 1 (by norm_num) le_rfl hw).2.2.2.1
  change 1 * energy 1 (fun x => (mass (optimizer 1))⁻¹ * optimizer 1 x) + 1 ≤
    mass (optimizer 1) * cost 1 (optimizer 1) - sharpConstant 1 at he
  simp only [hm, inv_one, one_mul, hE, hc, sub_self, zero_add] at he
  norm_num at he

def stabilityFamily : Registration stabilityArena (type_of% global_stability) where
  actual := energyActual
  bridge := Iff.rfl
  variation := ⟨global_stability, energyRejected, rejected_stability⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    stabilityArena.Law energyActual energyRejected rejected_stability
  dependence := energy_dependence

def stabilityAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    global_stability (Realization energySignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.Variational.JointReciprocalFunctional.stabilityUnit
  realizationName := `Reg.D5.S3.Analytic.Variational.JointReciprocalFunctional.stabilityFamily
  realizationSource := none
  generated := false
  arena := .source ⟨stabilityArena⟩
  objectArena := .source ⟨stabilityArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source stabilityArena ⟨stabilityFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize energySignature (fun _ b z => b * z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Variational.JointReciprocalFunctional
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
      "arg", "arg", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Analytic.Variational.JointReciprocalFunctional
