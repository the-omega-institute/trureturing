import D5.S3.Quantum.Analysis.HeisenbergCentralRigidity
import Reg.Support.DependentFamily
import Reg.Support.SourceSelection
import LeanInformationAuditInterface.Contract.Registration
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-! Full-family audit evidence for the actual closed Heisenberg graph. -/

open MeasureTheory Set Filter
open scoped ENNReal Topology ComplexConjugate
open _root_.D5.S3.Quantum.Analysis.HeisenbergCentralRigidity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Quantum.Analysis.HeisenbergCentralRigidity

abbrev signature : Signature where
  Params := Unit
  State _ := Ambient
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := State
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ p => p.2 2) (fun a => nomatch a)

def theoremLaw (R : Realization signature) : Prop :=

    Dense (coreOperator.domain : Set State) ∧
    coreOperator.IsClosable ∧ closedOperator.IsClosed ∧
    closedOperator.graph = jointGraph ∧
    (∀ p : Ambient, p ∈ jointGraph ↔ ∃ φ : ℕ → compactCore,
      Tendsto (fun n => (coreJet (φ n)).1) atTop (𝓝 p.1) ∧
      ∀ i, Tendsto (fun n => (coreJet (φ n)).2 i) atTop (𝓝 (p.2 i))) ∧
    (∀ p ∈ jointGraph, ∀ q ∈ jointGraph, p.1 = q.1 → p.2 = q.2) ∧
    (∀ p ∈ jointGraph, ∀ η : Space → ℂ, ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
      (∫ x : Space, (R.readout () () p) x * conj (η x)) =
        -(∫ x : Space, p.1 x * conj (fderiv ℝ η x (axis 2)))) ∧
    (∀ p ∈ jointGraph, R.readout () () p = 0 ↔ p.1 = 0) ∧
    (∀ (f : Space → ℂ) (hs : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f),
      ∃ p ∈ jointGraph, (p.1 : Space → ℂ) =ᵐ[volume] f ∧
        ∀ i, (p.2 i : Space → ℂ) =ᵐ[volume]
          (fun x => fderiv ℝ f x (frame i x)))

abbrev arena : Arena where
  signature := signature
  Law := theoremLaw

def nonzeroVector : State :=
  indicatorConstLp (μ := (volume : Measure Space)) (s := Metric.ball (0 : Space) 1)
    2 measurableSet_ball measure_ball_lt_top.ne (1 : ℂ)

private theorem nonzero_vector_ne : nonzeroVector ≠ 0 := by
  intro hz
  have hn := norm_indicatorConstLp (μ := (volume : Measure Space))
    (s := Metric.ball (0 : Space) 1) (hs := measurableSet_ball)
    (hμs := measure_ball_lt_top.ne) (c := (1 : ℂ))
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  have hp : 0 < (volume : Measure Space).real (Metric.ball (0 : Space) 1) :=
    ENNReal.toReal_pos (Metric.measure_ball_pos volume (0 : Space) (by norm_num)).ne'
      measure_ball_lt_top.ne
  have hpos : 0 < ‖nonzeroVector‖ := by
    rw [nonzeroVector, hn]
    exact mul_pos (by norm_num) (Real.rpow_pos_of_pos hp _)
  simpa [hz] using hpos

def rejected : Realization signature :=
  realize signature (fun _ _ _ => nonzeroVector) (fun a => nomatch a)

private theorem actual_law : arena.Law actual := central_rigidity

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  rcases h with ⟨_, _, _, _, _, _, _, hk, _⟩
  have hz := (hk (0 : Ambient) jointGraph.zero_mem).mpr rfl
  exact nonzero_vector_ne hz

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro role
  rcases central_rigidity with ⟨hd, _, _, hgraph, _, _, _, hk, _⟩
  obtain ⟨u, hu, hune⟩ : ∃ u ∈ coreOperator.domain, u ≠ (0 : State) := by
    by_contra! h
    have hc : closure (coreOperator.domain : Set State) ⊆ ({0} : Set State) :=
      closure_minimal (fun x hx => h x hx) isClosed_singleton
    exact nonzero_vector_ne (hc (hd nonzeroVector))
  let p : Ambient := (u, coreOperator ⟨u, hu⟩)
  have hp : p ∈ jointGraph := by
    rw [← hgraph]
    exact LinearPMap.le_graph_of_le coreOperator.le_closure (coreOperator.mem_graph ⟨u, hu⟩)
  have hn : p.2 2 ≠ 0 := fun hz => hune ((hk p hp).mp hz)
  refine ⟨(), (0 : Ambient), p, ?_⟩
  simpa [actual, realize] using Ne.symm hn

def family : Registration arena (type_of% central_rigidity) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro a
      exact nomatch a
  dependence := actual_dependence

/-- Full-family mathematical evidence; raw occurrence reconstruction remains unspecified. -/
def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    central_rigidity
    (type_of% (realize signature (fun _ _ p => p.2 2) (fun a => nomatch a)))
    Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Analysis.HeisenbergCentralRigidity.unit
  realizationName := `Reg.D5.S3.Quantum.Analysis.HeisenbergCentralRigidity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ p => p.2 2) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms registration
end Reg.D5.S3.Quantum.Analysis.HeisenbergCentralRigidity
