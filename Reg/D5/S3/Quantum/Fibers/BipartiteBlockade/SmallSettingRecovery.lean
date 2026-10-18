import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Quantum.Fibers.BipartiteBlockade.SmallSettingRecovery

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped Classical BigOperators Matrix
namespace Reg.D5.S3.Quantum.Fibers.BipartiteBlockade.SmallSettingRecovery
open _root_.D5.S3.Quantum.Fibers.BipartiteBlockade
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
universe u

structure Parameters where
  Vertex : Type u
  finiteVertex : Fintype Vertex
  equalVertex : DecidableEq Vertex
  graph : SimpleGraph Vertex

@[reducible] def signature : Signature where
  Params := Parameters.{u}
  State p := Matrix (Configuration p.graph) (Configuration p.graph) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.Vertex → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

private def empty (p : Parameters.{u}) : Configuration p.graph := ⟨∅, by simp⟩
private def singleton (p : Parameters.{u}) (v : p.Vertex) : Configuration p.graph := by
  letI := p.equalVertex
  exact ⟨{v}, by simp [p.graph.irrefl]⟩

def actual : Realization signature.{u} := realize signature
  (fun _ p ρ v => by
    letI := p.finiteVertex
    letI := p.equalVertex
    exact blockadeMean p.graph ρ v)
  (fun e => nomatch e)

private def rejected : Realization signature.{u} := realize signature
  (fun _ p ρ v => (ρ (empty p) (singleton p v)).re)
  (fun e => nomatch e)

def fullLaw (r : Realization signature.{u}) : Prop :=
  ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) (color : V → Bool),
    (∀ u v, G.Adj u v → color u ≠ color v) →
    ∀ (Ω : V → ℝ), (∀ v, Ω v ≠ 0) →
    (nonlinearNeighborhoods G = ∅ →
      ∀ ρ σ : Matrix (Configuration G) (Configuration G) ℂ,
      (Matrix.trace ρ).re = (Matrix.trace σ).re →
      (∀ v, occupationMean G ρ v = occupationMean G σ v) →
      ∀ v, r.readout () ⟨V, inferInstance, inferInstance, G⟩ ρ v =
        r.readout () ⟨V, inferInstance, inferInstance, G⟩ σ v) ∧
    ((nonlinearNeighborhoods G).card ≤ 1 →
      ∀ ρ σ : Matrix (Configuration G) (Configuration G) ℂ,
      (Matrix.trace ρ).re = (Matrix.trace σ).re →
      (∀ v, occupationMean G ρ v = occupationMean G σ v) →
      (∀ v, acceleration G Ω ρ v = acceleration G Ω σ v) →
      ∀ v, r.readout () ⟨V, inferInstance, inferInstance, G⟩ ρ v =
        r.readout () ⟨V, inferInstance, inferInstance, G⟩ σ v)

@[reducible] def arena : Arena where
  signature := signature.{u}
  Law := fullLaw

@[reducible] private def sample : Parameters.{u} where
  Vertex := ULift.{u} Unit
  finiteVertex := inferInstance
  equalVertex := inferInstance
  graph := ⊥

set_option maxHeartbeats 1600000 in
private theorem rejected_law : ¬ fullLaw rejected.{u} := by
  intro h
  letI : DecidableRel sample.{u}.graph.Adj := fun _ _ => Classical.propDecidable _
  let E : Matrix (Configuration sample.{u}.graph) (Configuration sample.{u}.graph) ℂ :=
    Matrix.single (empty sample.{u}) (singleton sample.{u} ⟨()⟩) 1
  have hne : empty sample.{u} ≠ singleton sample.{u} ⟨()⟩ := by
    intro he
    have hs := congrArg Subtype.val he
    simpa [empty, singleton] using hs
  have ht : (Matrix.trace (0 : Matrix (Configuration sample.{u}.graph) (Configuration sample.{u}.graph) ℂ)).re =
      (Matrix.trace E).re := by
    simp only [E, Matrix.trace_zero, Matrix.trace_single_eq_of_ne _ _ _ hne, Complex.zero_re]
  have hm : ∀ v, occupationMean sample.{u}.graph 0 v = occupationMean sample.{u}.graph E v := by
    intro v
    simp [occupationMean, E, Matrix.trace_single_mul, number,
      Matrix.diagonal_apply_ne _ hne.symm]
  have hx := (h sample.{u}.Vertex sample.{u}.graph (fun _ => true) (by simp [sample])
    (fun _ => 1) (by simp)).1 (by simp [nonlinearNeighborhoods, sample]) 0 E ht hm ⟨()⟩
  norm_num [rejected, realize, E, Matrix.single_apply, hne] at hx

private theorem actual_law : fullLaw actual.{u} := by
  intro V _ _ G color proper Ω nonzero
  exact small_setting_recovery G color proper Ω nonzero

private theorem actual_dependence : ObservationalDependence signature.{u} actual := by
  rintro ⟨⟩
  refine ⟨sample, 0, Matrix.single (empty sample) (empty sample) 1, ?_⟩
  intro he
  have hx := congrArg (fun f => f ⟨()⟩) he
  norm_num [actual, realize, blockadeMean, Matrix.trace_single_mul, blockade,
    Matrix.diagonal_apply, empty, clear] at hx

def familyRegistration : Registration arena.{u}
    (∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) (color : V → Bool),
      (∀ u v, G.Adj u v → color u ≠ color v) →
      ∀ (Ω : V → ℝ), (∀ v, Ω v ≠ 0) →
      (nonlinearNeighborhoods G = ∅ →
        ∀ ρ σ : Matrix (Configuration G) (Configuration G) ℂ,
        (Matrix.trace ρ).re = (Matrix.trace σ).re →
        (∀ v, occupationMean G ρ v = occupationMean G σ v) →
        ∀ v, blockadeMean G ρ v = blockadeMean G σ v) ∧
      ((nonlinearNeighborhoods G).card ≤ 1 →
        ∀ ρ σ : Matrix (Configuration G) (Configuration G) ℂ,
        (Matrix.trace ρ).re = (Matrix.trace σ).re →
        (∀ v, occupationMean G ρ v = occupationMean G σ v) →
        (∀ v, acceleration G Ω ρ v = acceleration G Ω σ v) →
        ∀ v, blockadeMean G ρ v = blockadeMean G σ v)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, ?_, rejected_law⟩
      · intro j hj; exact (hj (Subsingleton.elim _ _)).elim
      · funext e; exact nomatch e
    · intro e; exact nomatch e
  dependence := actual_dependence

def registration : Contract.Registration
    (@_root_.D5.S3.Quantum.Fibers.BipartiteBlockade.small_setting_recovery.{u})
    (Realization signature.{u}) Type Unit := {
  unitName := `Reg.D5.S3.Quantum.Fibers.BipartiteBlockade.SmallSettingRecovery.small_setting_recovery.__information_unit,
  realizationName := `Reg.D5.S3.Quantum.Fibers.BipartiteBlockade.SmallSettingRecovery.familyRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨familyRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature
    (fun _ p ρ v => by
      letI := p.finiteVertex
      letI := p.equalVertex
      exact blockadeMean p.graph ρ v)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Quantum.Fibers.BipartiteBlockade.SmallSettingRecovery, definition := none, coordinates := #[0, 3], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn"], stateBinder := 9, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }
/-- info: 'Reg.D5.S3.Quantum.Fibers.BipartiteBlockade.SmallSettingRecovery.registration' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms registration

end Reg.D5.S3.Quantum.Fibers.BipartiteBlockade.SmallSettingRecovery
