import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ObserverMemory.Prediction.OneSidedPredictorMinimum
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.ObserverMemory.Prediction.OneSidedPredictorMinimum
open _root_.D5.S3.ObserverMemory.Prediction.OneSidedPredictorMinimum
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Filter Topology
noncomputable section
universe u

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (ℕ → ℝ) (fun _ => ℕ) (fun _ => ℝ)

def actual : Realization signature := realize signature (fun _ p n => p n) (fun e => nomatch e)
def badOne : Realization signature := realize signature (fun _ _ _ => 1) (fun e => nomatch e)
def badZero : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem dependent (R : Realization signature) (heq : R = actual) :
    ObservationalDependence signature R := by
  subst R
  intro i
  refine ⟨fun n => (n : ℝ),0,1,?_⟩
  norm_num [actual,realize]

namespace Exact

def arena : Arena where
  signature := signature
  Law R := ∀ (x : ℝ) (p : ℕ → ℝ),
    (∀ n, 0 < R.readout () p n) → Tendsto p atTop (𝓝 0) →
    ∀ (S : Type u) [Fintype S] (M : Predictor S), ¬ Correct M x p 0

theorem bad_law : ¬ arena.{u}.Law badOne := by
  intro h
  let M : Predictor (ULift.{u} Unit) := {
    initial := ⟨()⟩
    update := fun _ s => s
    output := fun _ => 0
    output_mem := fun _ => by norm_num }
  apply h 0 (fun _ => 0) (by intro n; norm_num [badOne,realize]) tendsto_const_nhds _ M
  intro w
  simp [M,historyLaw]

def evidence : Registration arena.{u} (arena.{u}.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨exact_prediction_impossible,badOne,bad_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ bad_law
  dependence := dependent actual rfl

end Exact

namespace Sharp

def arena : Arena where
  signature := signature
  Law R := ∀ (x ε : ℝ) (p : ℕ → ℝ) (N : ℕ),
    x ∈ Set.Ioc 0 1 → 0 ≤ ε → 2*ε < x →
    (∀ n, 0 ≤ p n) → (∀ n, R.readout () p n ≤ x) →
    Antitone p → Tendsto p atTop (𝓝 0) →
    (∀ n, p n ≤ 2*ε ↔ N ≤ n) →
    (∃ M : Predictor (Fin (N+1) ⊕ Unit),Correct M x p ε) ∧
    Fintype.card (Fin (N+1) ⊕ Unit) = N+2 ∧
    ∀ (S : Type u) [Fintype S] (M : Predictor S),Correct M x p ε → N+2 ≤ Fintype.card S

theorem bad_law : ¬ arena.{u}.Law badZero := by
  intro h
  let p : ℕ → ℝ := fun n => if n=0 then 2 else 0
  have hm : Antitone p := by
    intro m n hmn
    dsimp [p]
    split_ifs <;> try norm_num
    omega
  have hl : Tendsto p atTop (𝓝 0) := by
    have he : p =ᶠ[atTop] (fun _ : ℕ => (0 : ℝ)) := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      simp [p,show n ≠ 0 by omega]
    exact (tendsto_congr' he).mpr tendsto_const_nhds
  have hc (n : ℕ) : p n ≤ 2*(1/8:ℝ) ↔ 1 ≤ n := by
    by_cases hn : n=0
    · subst n
      norm_num [p]
    · have hge : 1 ≤ n := by omega
      norm_num [p,hn,hge]
  obtain ⟨M,hM⟩ := (h (1/2) (1/8) p 1 (by norm_num) (by norm_num)
    (by norm_num) (by intro n; dsimp [p]; split_ifs <;> norm_num)
    (by intro n; norm_num [badZero,realize]) hm hl hc).1
  have hh := abs_le.mp (hM [])
  have hb := (M.output_mem M.initial).2
  simp [Predictor.run,_root_.D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality.runWord,
    historyLaw,p] at hh
  linarith

def evidence : Registration arena.{u} (arena.{u}.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨sharp_predictor_minimum,badZero,bad_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ bad_law
  dependence := dependent actual rfl

end Sharp

#print axioms Exact.evidence
#print axioms Sharp.evidence
end
end Reg.D5.S3.ObserverMemory.Prediction.OneSidedPredictorMinimum
