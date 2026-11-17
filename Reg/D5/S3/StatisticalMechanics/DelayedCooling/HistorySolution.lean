import LeanInformationAuditInterface.Contract.Registration
import D5.S3.StatisticalMechanics.DelayedCooling.HistorySolution
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout

/-! Typed whole-family audit attempt for Appendix (5) and the history integral.
Source-occurrence reconstruction remains subject to the binding producer. -/

open Set MeasureTheory LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.StatisticalMechanics.DelayedCooling.Kernel
open _root_.D5.S3.StatisticalMechanics.DelayedCooling.ShiftOrder
open _root_.D5.S3.StatisticalMechanics.DelayedCooling.Volterra
open _root_.D5.S3.StatisticalMechanics.DelayedCooling.HistorySolution

noncomputable section
namespace Reg.D5.S3.StatisticalMechanics.DelayedCooling.HistorySolution

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature
    (ℝ × ℝ × ℝ × ℝ × (ℝ → ℝ)) (fun _ => ℝ → ℝ) (fun _ => ℝ → ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ T => T) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => 1) (fun e => nomatch e)

def historyArena : Arena where
  signature := signature
  Law R := ∀ {τ a q c : ℝ} {b T : ℝ → ℝ}, 0 < τ → τ ≤ Real.exp (-1) →
    IntegratedSolution τ a q b T → a ≤ 0 →
    (∀ s, s < a → b s = q) → (∀ s, 0 < s → b s = c) →
    (∀ t, a ≤ t → R.readout () (τ, a, q, c, b) T t =
      c + (q - c) * relaxation τ (t - a) +
        ∫ s in a..min 0 t, (b s - c) * responseKernel τ (t - s)) ∧
    (∀ t, 0 ≤ t →
      IntegrableOn (fun u => responseKernel τ (t + u) * (b (-u) - c)) (Ioi 0) ∧
      R.readout () (τ, a, q, c, b) T t =
        c + ∫ u in Ioi 0, responseKernel τ (t + u) * (b (-u) - c))

def historyFamily : Registration historyArena (type_of% (@raw_history_solution_bridge)) := by
  have hzero : IntegratedSolution (Real.exp (-1)) 0 0 (fun _ => 0) (fun _ => 0) := by
    constructor
    · intros; rfl
    · intros; simpa using (intervalIntegrable_const (c := (0 : ℝ)))
    · intros; simp
  have hbad : ¬ historyArena.Law rejected := by
    intro h
    have he := (h (Real.exp_pos (-1)) le_rfl hzero le_rfl
      (fun _ _ => rfl) (fun _ _ => rfl)).1 0 le_rfl
    norm_num [rejected, realize] at he
  exact {
    actual := actual
    bridge := Iff.rfl
    variation := ⟨@raw_history_solution_bridge, rejected, hbad⟩
    sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
      historyArena.Law actual rejected hbad
    dependence := by
      intro _
      refine ⟨(1, 0, 0, 0, fun _ => 0), (fun _ => 0), (fun _ => 1), ?_⟩
      intro h
      have hh := congrFun h 0
      norm_num [actual, realize] at hh }

def historyRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@raw_history_solution_bridge)
    (type_of% (realize signature (fun _ _ T => T) (fun e => nomatch e)))
    Type Unit where
  unitName := `D5.S3.StatisticalMechanics.DelayedCooling.HistorySolution.raw_history_solution_bridge.__information_unit
  realizationName := `Reg.D5.S3.StatisticalMechanics.DelayedCooling.HistorySolution.historyFamily
  realizationSource := none
  generated := false
  arena := .source ⟨historyArena⟩
  objectArena := .source ⟨historyArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source historyArena ⟨historyFamily⟩
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

namespace Equivalence

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature
    (ℝ × ℝ × ℝ × ℝ × (ℝ → ℝ)) (fun _ => ℝ → ℝ) (fun _ => Prop)

def actual : Realization signature := realize signature
  (fun _ p T => IntegratedSolution p.1 p.2.1 p.2.2.1 p.2.2.2.2 T)
  (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

def equivalenceArena : Arena where
  signature := signature
  Law R := ∀ {τ a q c : ℝ} {b T : ℝ → ℝ}, 0 < τ → τ ≤ Real.exp (-1) → a ≤ 0 →
    (∀ s, s < a → b s = q) → (∀ s, 0 < s → b s = c) →
    (AppendixSolution τ a q c b T ↔ R.readout () (τ, a, q, c, b) T)

def equivalenceFamily : Registration equivalenceArena (type_of% (@appendix5_iff_integrated)) := by
  have hz : IntegratedSolution 1 0 0 (fun _ => 0) (fun _ => 0) := by
    constructor
    · intros; rfl
    · intros; simpa using (intervalIntegrable_const (c := (0 : ℝ)))
    · intros; simp
  have ha : AppendixSolution (Real.exp (-1)) 0 0 0 (fun _ => 0) (fun _ => 0) := by
    constructor
    · intros; rfl
    · simp
    · intros; simp
  have hbad : ¬ equivalenceArena.Law rejected := by
    intro h
    exact (h (Real.exp_pos (-1)) le_rfl le_rfl
      (fun _ _ => rfl) (fun _ _ => rfl)).mp ha
  exact {
    actual := actual
    bridge := Iff.rfl
    variation := ⟨@appendix5_iff_integrated, rejected, hbad⟩
    sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
      equivalenceArena.Law actual rejected hbad
    dependence := by
      intro _
      refine ⟨(1, 0, 0, 0, fun _ => 0), (fun _ => 0), (fun _ => 1), ?_⟩
      intro he
      change IntegratedSolution 1 0 0 (fun _ => 0) (fun _ => 0) =
        IntegratedSolution 1 0 0 (fun _ => 0) (fun _ => 1) at he
      have hh := (Eq.mp he hz).past 0 le_rfl
      norm_num at hh }

def equivalenceRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@appendix5_iff_integrated)
    (type_of% (realize signature
      (fun _ p T => IntegratedSolution p.1 p.2.1 p.2.2.1 p.2.2.2.2 T)
      (fun e => nomatch e))) Type Unit where
  unitName := `D5.S3.StatisticalMechanics.DelayedCooling.HistorySolution.appendix5_iff_integrated.__information_unit
  realizationName := `Reg.D5.S3.StatisticalMechanics.DelayedCooling.HistorySolution.Equivalence.equivalenceFamily
  realizationSource := none
  generated := false
  arena := .source ⟨equivalenceArena⟩
  objectArena := .source ⟨equivalenceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source equivalenceArena ⟨equivalenceFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p T => IntegratedSolution p.1 p.2.1 p.2.2.1 p.2.2.2.2 T)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (ℝ → ℝ)
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Equivalence

end Reg.D5.S3.StatisticalMechanics.DelayedCooling.HistorySolution
end
