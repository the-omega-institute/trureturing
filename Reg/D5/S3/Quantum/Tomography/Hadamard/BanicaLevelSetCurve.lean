import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Tomography.Hadamard.BanicaLevelSetCurve
import Reg.Support.UniverseSingleReadout

/-! Source-bound registrations of positive curve reparametrization and regular level sets. -/

namespace Reg.D5.S3.Quantum.Tomography.Hadamard.BanicaLevelSetCurve
open _root_.D5.S3.Quantum.Tomography.Hadamard.BanicaLevelSetCurve
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators Topology ContDiff
open Filter
noncomputable section
universe u v

namespace globalize_analytic_curve
abbrev signature : Signature :=
  Reg.Support.UniverseSingleReadout.signature Unit
    (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature := realize signature (fun _ _ a b => a < b) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (q : ℝ → E) (v : E) (_hq : ContDiffAt ℝ ⊤ q 0)
    (_hd : HasDerivAt q v 0) (_hzero : q 0 = 0)
    (P : E → Prop) (_hP : ∀ᶠ t in 𝓝 (0 : ℝ), P (q t)),
    ∃ (c : ℝ → E) (κ : ℝ), R.readout () () 0 κ ∧ ContDiff ℝ ⊤ c ∧ c 0 = 0 ∧
      HasDerivAt c (κ • v) 0 ∧ ∀ t, P (c t)
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  obtain ⟨c, κ, hκ, _⟩ := h (E := ULift.{u} ℝ) (fun _ => 0) 0
    contDiffAt_const (hasDerivAt_const (0 : ℝ) (0 : ULift.{u} ℝ)) rfl
    (fun _ => True) (Filter.Eventually.of_forall (fun _ => True.intro))
  exact hκ
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hh := (congrFun h 1).mp (by norm_num : (0 : ℝ) < 1)
  exact (lt_irrefl (1 : ℝ)) hh
def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Tomography.Hadamard.BanicaLevelSetCurve.globalize_analytic_curve)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Tomography.Hadamard.BanicaLevelSetCurve.globalize_analytic_curve, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Quantum.Tomography.Hadamard.BanicaLevelSetCurve.globalize_analytic_curve) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Tomography.Hadamard.BanicaLevelSetCurve.globalize_analytic_curve.unit
  realizationName := `Reg.D5.S3.Quantum.Tomography.Hadamard.BanicaLevelSetCurve.globalize_analytic_curve.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ a b => a < b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Tomography.Hadamard.BanicaLevelSetCurve
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end globalize_analytic_curve

namespace analytic_level_set_curve
abbrev signature : Signature :=
  Reg.Support.UniverseSingleReadout.signature Unit
    (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature := realize signature (fun _ _ a b => a < b) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {E : Type u} {F : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] (Φ : E → F) (_hΦ : ContDiff ℝ ⊤ Φ) (_hzero : Φ 0 = 0)
    (_hsurj : Function.Surjective (fderiv ℝ Φ 0)) (v : E) (_hv : fderiv ℝ Φ 0 v = 0),
    ∃ (c : ℝ → E) (κ : ℝ), R.readout () () 0 κ ∧ ContDiff ℝ ⊤ c ∧ c 0 = 0 ∧
      HasDerivAt c (κ • v) 0 ∧ ∀ t, Φ (c t) = 0
private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  obtain ⟨c, κ, hκ, _⟩ := h (E := ULift.{u} ℝ) (F := ULift.{v} (Fin 0 → ℝ))
    (fun _ => 0) contDiff_const rfl (by
      intro y
      refine ⟨0, ?_⟩
      exact Subsingleton.elim _ _) 0 (by simp)
  exact hκ
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hh := (congrFun h 1).mp (by norm_num : (0 : ℝ) < 1)
  exact (lt_irrefl (1 : ℝ)) hh
def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Tomography.Hadamard.BanicaLevelSetCurve.analytic_level_set_curve)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Tomography.Hadamard.BanicaLevelSetCurve.analytic_level_set_curve, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Quantum.Tomography.Hadamard.BanicaLevelSetCurve.analytic_level_set_curve) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Tomography.Hadamard.BanicaLevelSetCurve.analytic_level_set_curve.unit
  realizationName := `Reg.D5.S3.Quantum.Tomography.Hadamard.BanicaLevelSetCurve.analytic_level_set_curve.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ a b => a < b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Tomography.Hadamard.BanicaLevelSetCurve
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end analytic_level_set_curve

end
end Reg.D5.S3.Quantum.Tomography.Hadamard.BanicaLevelSetCurve
