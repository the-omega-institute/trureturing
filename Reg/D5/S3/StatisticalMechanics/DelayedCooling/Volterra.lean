import LeanInformationAuditInterface.Contract.Registration
import D5.S3.StatisticalMechanics.DelayedCooling.Volterra
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout

/-! Typed whole-family audit attempt for the raw integrated solution bridge.
Source-occurrence reconstruction remains subject to the binding producer. -/

open Set MeasureTheory LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.StatisticalMechanics.DelayedCooling.Volterra

noncomputable section
namespace Reg.D5.S3.StatisticalMechanics.DelayedCooling.Volterra

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature
    (ℝ × ℝ × ℝ × (ℝ → ℝ)) (fun _ => ℝ → ℝ) (fun _ => ℝ → ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ T => T) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => 0) (fun e => nomatch e)

def solutionArena : Arena where
  signature := signature
  Law R := ∀ {τ a q : ℝ} {b T : ℝ → ℝ}, 0 < τ → IntegratedSolution τ a q b T →
    Continuous (R.readout () (τ, a, q, b) T) ∧
    (∀ t, a ≤ t → AbsolutelyContinuousOnInterval (R.readout () (τ, a, q, b) T) a t) ∧
    (∀ t, a ≤ t → IntervalIntegrable b volume a t) ∧
    (∀ t, a < t → ContinuousAt b t → HasDerivAt (R.readout () (τ, a, q, b) T)
      (b t - R.readout () (τ, a, q, b) T (t - τ)) t) ∧
    (∀ U, IntegratedSolution τ a q b U → R.readout () (τ, a, q, b) T = U)

def solutionFamily : Registration solutionArena (type_of% (@integrated_solution_bridge)) := by
  have hone : IntegratedSolution 1 0 1 (fun _ => 1) (fun _ => 1) := by
    constructor
    · intros; rfl
    · intros; simpa using (intervalIntegrable_const (c := (0 : ℝ)))
    · intros; simp
  have hbad : ¬ solutionArena.Law rejected := by
    intro h
    have he := (h (by norm_num : (0 : ℝ) < 1) hone).2.2.2.2 (fun _ => 1) hone
    have hz := congrFun he 0
    norm_num [rejected, realize] at hz
  exact {
    actual := actual
    bridge := Iff.rfl
    variation := ⟨@integrated_solution_bridge, rejected, hbad⟩
    sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
      solutionArena.Law actual rejected hbad
    dependence := by
      intro _
      refine ⟨(1, 0, 0, fun _ => 0), (fun _ => 0), (fun _ => 1), ?_⟩
      intro h
      have hh := congrFun h 0
      norm_num [actual, realize] at hh }

def solutionRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@integrated_solution_bridge)
    (type_of% (realize signature (fun _ _ T => T) (fun e => nomatch e)))
    Type Unit where
  unitName := `D5.S3.StatisticalMechanics.DelayedCooling.Volterra.integrated_solution_bridge.__information_unit
  realizationName := `Reg.D5.S3.StatisticalMechanics.DelayedCooling.Volterra.solutionFamily
  realizationSource := none
  generated := false
  arena := .source ⟨solutionArena⟩
  objectArena := .source ⟨solutionArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source solutionArena ⟨solutionFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ T => T) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (ℝ → ℝ)
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

namespace Existence

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature
    (ℝ × ℝ × ℝ × (ℝ → ℝ)) (fun _ => ℝ → ℝ) (fun _ => Prop)

def actual : Realization signature := realize signature
  (fun _ p T => IntegratedSolution p.1 p.2.1 p.2.2.1 p.2.2.2 T)
  (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

def existenceArena : Arena where
  signature := signature
  Law R := ∀ {τ a q : ℝ}, 0 < τ → ∀ b : ℝ → ℝ,
    (∀ t, a ≤ t → IntervalIntegrable b volume a t) →
    ∃! T, R.readout () (τ, a, q, b) T

def existenceFamily : Registration existenceArena (type_of% (@exists_unique_integrated_solution)) := by
  have hz : IntegratedSolution 1 0 0 (fun _ => 0) (fun _ => 0) := by
    constructor
    · intros; rfl
    · intros; simpa using (intervalIntegrable_const (c := (0 : ℝ)))
    · intros; simp
  have hbad : ¬ existenceArena.Law rejected := by
    intro h
    obtain ⟨T, hT, _⟩ := h (a := 0) (q := 0) (by norm_num : (0 : ℝ) < 1)
      (fun _ => 0) (fun _ _ => intervalIntegrable_const)
    exact hT
  exact {
    actual := actual
    bridge := Iff.rfl
    variation := ⟨@exists_unique_integrated_solution, rejected, hbad⟩
    sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
      existenceArena.Law actual rejected hbad
    dependence := by
      intro _
      refine ⟨(1, 0, 0, fun _ => 0), (fun _ => 0), (fun _ => 1), ?_⟩
      intro he
      change IntegratedSolution 1 0 0 (fun _ => 0) (fun _ => 0) =
        IntegratedSolution 1 0 0 (fun _ => 0) (fun _ => 1) at he
      have hh := (Eq.mp he hz).past 0 le_rfl
      norm_num at hh }

def existenceRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exists_unique_integrated_solution)
    (type_of% (realize signature
      (fun _ p T => IntegratedSolution p.1 p.2.1 p.2.2.1 p.2.2.2 T)
      (fun e => nomatch e))) Type Unit where
  unitName := `D5.S3.StatisticalMechanics.DelayedCooling.Volterra.exists_unique_integrated_solution.__information_unit
  realizationName := `Reg.D5.S3.StatisticalMechanics.DelayedCooling.Volterra.Existence.existenceFamily
  realizationSource := none
  generated := false
  arena := .source ⟨existenceArena⟩
  objectArena := .source ⟨existenceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source existenceArena ⟨existenceFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p T => IntegratedSolution p.1 p.2.1 p.2.2.1 p.2.2.2 T)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (ℝ → ℝ)
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Existence

end Reg.D5.S3.StatisticalMechanics.DelayedCooling.Volterra
end
