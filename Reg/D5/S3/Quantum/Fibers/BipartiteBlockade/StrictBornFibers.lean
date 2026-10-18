import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Reg.D5.S3.Quantum.Fibers.BipartiteBlockade.PhysicalSingleSettingLower
import D5.S3.Quantum.Fibers.BipartiteBlockade.StrictBornFibers

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped Classical BigOperators ComplexOrder
namespace Reg.D5.S3.Quantum.Fibers.BipartiteBlockade.StrictBornFibers
open _root_.D5.S3.Quantum.Fibers.BipartiteBlockade
open _root_.D5.S3.Quantum.Fibers.BipartiteBlockade.StrictBornFibers
open _root_.D5.S3.Quantum.Fibers.BipartiteBlockade.DiagonalResidual
open _root_.D5.S3.Quantum.Fibers.BipartiteBlockade.GraphResidualDimension
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open private endpointTask from
  D5.S3.Quantum.Fibers.BipartiteBlockade.StrictBornFibers
open LeanInformationAudit
open private square square_connected square_proper square_left square_right from
  Reg.D5.S3.Quantum.Fibers.BipartiteBlockade.PhysicalSingleSettingLower
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
  Output _ p := p.Vertex → p.Vertex → p.Vertex → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

@[reducible] def actual : Realization signature.{u} := realize signature
  (fun _ p ρ u v w => by
    letI := p.finiteVertex
    letI := p.equalVertex
    exact bornModeLaw p.graph u v w ρ 4)
  (fun e => nomatch e)

def law (r : Realization signature.{u}) : Prop :=
∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (connected : G.Connected)
    (color : V → Bool) (proper : ∀ x y, G.Adj x y → color x ≠ color y)
    (Ω : V → ℝ) (positiveDrive : ∀ v, 0 < Ω v)
    (maximum : ∀ v, (G.neighborFinset v).card ≤ 2)
    (two : 2 ≤ (nonlinearNeighborhoods G).card) (radius : ℝ) (hRadius : 0 < radius),
    ∃ ρ σ : Matrix (Configuration G) (Configuration G) ℂ,
      ρ.PosDef ∧ Matrix.trace ρ = 1 ∧ σ.PosDef ∧ Matrix.trace σ = 1 ∧
      ‖CStarMatrix.ofMatrix (ρ - maximallyMixed G)‖ < radius ∧
      ‖CStarMatrix.ofMatrix (σ - maximallyMixed G)‖ < radius ∧
      (∀ v, occupationMean G ρ v = occupationMean G σ v) ∧
      (∀ v, acceleration G Ω ρ v = acceleration G Ω σ v) ∧
      (∀ u v w, (∀ x, G.Adj v x ↔ x = u ∨ x = w) → u ≠ w →
        ∀ k, 0 < bornModeLaw G u v w ρ k ∧ 0 < bornModeLaw G u v w σ k) ∧
      ∃ u v w, (∀ x, G.Adj v x ↔ x = u ∨ x = w) ∧ u ≠ w ∧
        0 < 1 - occupationMean G ρ v ∧ 0 < 1 - occupationMean G σ v ∧
        0 < min (min (occupationMean G ρ u) (occupationMean G ρ w))
          (min (1 - occupationMean G ρ v - occupationMean G ρ u)
            (1 - occupationMean G ρ v - occupationMean G ρ w)) ∧
        0 < min (min (occupationMean G σ u) (occupationMean G σ w))
          (min (1 - occupationMean G σ v - occupationMean G σ u)
            (1 - occupationMean G σ v - occupationMean G σ w)) ∧
        r.readout () ⟨V, inferInstance, inferInstance, G⟩ ρ u v w ≠
        r.readout () ⟨V, inferInstance, inferInstance, G⟩ σ u v w ∧
        endpointTask 4 - endpointTask 1 - endpointTask 3 + endpointTask 0 = 1 ∧
        (∑ k, bornModeLaw G u v w ρ k * endpointTask k) ≠
          (∑ k, bornModeLaw G u v w σ k * endpointTask k) ∧
        (1 - occupationMean G ρ v) * bornModeLaw G u v w ρ 4 -
          occupationMean G ρ u * occupationMean G ρ w ≠
        (1 - occupationMean G σ v) * bornModeLaw G u v w σ 4 -
          occupationMean G σ u * occupationMean G σ w

@[reducible] def arena : Arena where
  signature := signature.{u}
  Law := law

@[reducible] private def bad : Realization signature.{u} := realize signature
  (fun _ _ _ _ _ _ => 0) (fun e => nomatch e)

private theorem square_degree : ∀ v, (square.{u}.neighborFinset v).card ≤ 2 := by
  intro v
  have hl (x : ULift.{u} (Fin 2)) : square.{u}.neighborFinset (.inl x) =
      square.{u}.neighborFinset (.inl ⟨0⟩) := by
    ext y
    simp only [SimpleGraph.mem_neighborFinset]
    cases y <;> simp [square, completeBipartiteGraph_adj]
  have hr (x : ULift.{u} (Fin 2)) : square.{u}.neighborFinset (.inr x) =
      square.{u}.neighborFinset (.inr ⟨0⟩) := by
    ext y
    simp only [SimpleGraph.mem_neighborFinset]
    cases y <;> simp [square, completeBipartiteGraph_adj]
  cases v with
  | inl x => rw [hl, square_left]; norm_num
  | inr x => rw [hr, square_right]; norm_num

private theorem square_two : 2 ≤ (nonlinearNeighborhoods square.{u}).card := by
  have hl : square.{u}.neighborFinset (.inl ⟨0⟩) ∈ nonlinearNeighborhoods square.{u} := by
    apply Finset.mem_image.mpr
    exact ⟨.inl ⟨0⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [square_left]; norm_num⟩, rfl⟩
  have hr : square.{u}.neighborFinset (.inr ⟨0⟩) ∈ nonlinearNeighborhoods square.{u} := by
    apply Finset.mem_image.mpr
    exact ⟨.inr ⟨0⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [square_right]; norm_num⟩, rfl⟩
  have hne : square.{u}.neighborFinset (.inl ⟨0⟩) ≠ square.{u}.neighborFinset (.inr ⟨0⟩) := by
    rw [square_left, square_right]
    decide
  have hsub : {square.{u}.neighborFinset (.inl ⟨0⟩), square.{u}.neighborFinset (.inr ⟨0⟩)} ⊆
      nonlinearNeighborhoods square.{u} := by
    intro N hN
    simp only [Finset.mem_insert, Finset.mem_singleton] at hN
    rcases hN with rfl | rfl
    · exact hl
    · exact hr
  simpa only [Finset.card_pair hne] using Finset.card_le_card hsub

private theorem bad_law : ¬ law bad.{u} := by
  intro h
  obtain ⟨ρ, σ, _, _, _, _, _, _, _, _, _, u, v, w, _, _, _, _, _, _, hdiff⟩ :=
    h square.{u} square_connected (fun x => x.isLeft) square_proper
      (fun _ => 1) (by simp) square_degree square_two 1 (by norm_num)
  exact hdiff.1 rfl

@[reducible] private def fixtureParameters : Parameters.{u} where
  Vertex := (ULift.{u} (Fin 2)) ⊕ (ULift.{u} (Fin 2))
  finiteVertex := inferInstance
  equalVertex := inferInstance
  graph := square

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  cases i
  obtain ⟨ρ, σ, _, _, _, _, _, _, _, _, _, u, v, w, _, _, _, _, _, _, hdiff⟩ :=
    strict_born_single_setting_fiber square.{u} square_connected (fun x => x.isLeft)
      square_proper (fun _ => 1) (by simp) square_degree square_two 1 (by norm_num)
  refine ⟨fixtureParameters, ρ, σ, ?_⟩
  intro heq
  exact hdiff.1 (congrFun (congrFun (congrFun heq u) v) w)

def family : Registration arena.{u} (type_of% (@strict_born_single_setting_fiber.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@strict_born_single_setting_fiber.{u}, bad, bad_law⟩
  sensitivity := by
    constructor
    · intro i
      cases i
      refine ⟨bad, ?_, ?_, bad_law⟩
      · intro j hj; cases j; exact (hj rfl).elim
      · funext e; exact nomatch e
    · intro e; exact nomatch e
  dependence := dependence

/-- The original strict density-state fiber and actual joint Born mass are retained. -/
def registration : Contract.Registration
    (@strict_born_single_setting_fiber.{u}) (Realization signature.{u}) Type Unit := {
  unitName := `Reg.D5.S3.Quantum.Fibers.BipartiteBlockade.StrictBornFibers.strict_born_single_setting_fiber.__information_unit,
  realizationName := `Reg.D5.S3.Quantum.Fibers.BipartiteBlockade.StrictBornFibers.family,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨family⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature
    (fun _ p ρ u v w => by
      letI := p.finiteVertex
      letI := p.equalVertex
      exact bornModeLaw p.graph u v w ρ 4)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

/-- info: 'Reg.D5.S3.Quantum.Fibers.BipartiteBlockade.StrictBornFibers.family' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms family

/-- info: 'Reg.D5.S3.Quantum.Fibers.BipartiteBlockade.StrictBornFibers.registration' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms registration

end Reg.D5.S3.Quantum.Fibers.BipartiteBlockade.StrictBornFibers
