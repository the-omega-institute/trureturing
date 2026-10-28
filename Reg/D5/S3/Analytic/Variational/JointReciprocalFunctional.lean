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

end Reg.D5.S3.Analytic.Variational.JointReciprocalFunctional
