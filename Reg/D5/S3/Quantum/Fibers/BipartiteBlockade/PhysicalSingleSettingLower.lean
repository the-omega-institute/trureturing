import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Quantum.Fibers.BipartiteBlockade.PhysicalSingleSettingLower

attribute [local instance] LieRing.ofAssociativeRing
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped Classical BigOperators ComplexOrder
namespace Reg.D5.S3.Quantum.Fibers.BipartiteBlockade.PhysicalSingleSettingLower
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

@[reducible] def actual : Realization signature.{u} := realize signature
  (fun _ p ρ v => by
    letI := p.finiteVertex
    letI := p.equalVertex
    exact (Matrix.trace (ρ * blockade p.graph v)).re)
  (fun e => nomatch e)

def zeroLaw (r : Realization signature.{u}) : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (color : V → Bool)
    (proper : ∀ u v, G.Adj u v → color u ≠ color v)
    (v : V) (large : 2 ≤ (G.neighborFinset v).card),
    ∃ ρ σ : Matrix (Configuration G) (Configuration G) ℂ,
      ρ.PosSemidef ∧ Matrix.trace ρ = 1 ∧
      σ.PosSemidef ∧ Matrix.trace σ = 1 ∧
      (∀ x, occupationMean G ρ x = occupationMean G σ x) ∧
      r.readout () ⟨V, inferInstance, inferInstance, G⟩ ρ v ≠ r.readout () ⟨V, inferInstance, inferInstance, G⟩ σ v
def oneLaw (r : Realization signature.{u}) : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (connected : G.Connected) (color : V → Bool)
    (proper : ∀ u v, G.Adj u v → color u ≠ color v)
    (Ω : V → ℝ) (nonzero : ∀ v, Ω v ≠ 0) (u w : V)
    (largeU : 2 ≤ (G.neighborFinset u).card)
    (largeW : 2 ≤ (G.neighborFinset w).card)
    (distinct : G.neighborFinset u ≠ G.neighborFinset w),
    ∃ ρ σ : Matrix (Configuration G) (Configuration G) ℂ,
      ρ.PosSemidef ∧ Matrix.trace ρ = 1 ∧
      σ.PosSemidef ∧ Matrix.trace σ = 1 ∧
      (∀ v, Matrix.trace (ρ * number G v) = Matrix.trace (σ * number G v)) ∧
      (∀ v, Matrix.trace (ρ *
          ⁅hamiltonian G (fun x => (Ω x : ℂ)),
            ⁅hamiltonian G (fun x => (Ω x : ℂ)), number G v⁆⁆) =
        Matrix.trace (σ *
          ⁅hamiltonian G (fun x => (Ω x : ℂ)),
            ⁅hamiltonian G (fun x => (Ω x : ℂ)), number G v⁆⁆)) ∧
      ∃ v, r.readout () ⟨V, inferInstance, inferInstance, G⟩ ρ v ≠
        r.readout () ⟨V, inferInstance, inferInstance, G⟩ σ v

@[reducible] def zeroArena : Arena where
  signature := signature.{u}
  Law := zeroLaw

@[reducible] def oneArena : Arena where
  signature := signature.{u}
  Law := oneLaw

@[reducible] private def bad : Realization signature.{u} := realize signature
  (fun _ _ _ _ => 0) (fun e => nomatch e)

@[reducible] private def square : SimpleGraph ((ULift.{u} (Fin 2)) ⊕ (ULift.{u} (Fin 2))) :=
  completeBipartiteGraph _ _

private theorem square_connected : square.{u}.Connected := by
  constructor
  · intro x y
    cases x with
    | inl x =>
      cases y with
      | inl y =>
        exact (show square.Adj (.inl x) (.inr ⟨0⟩) from by simp [square, completeBipartiteGraph_adj]).reachable.trans
          (show square.Adj (.inr ⟨0⟩) (.inl y) from by simp [square, completeBipartiteGraph_adj]).reachable
      | inr y => exact (show square.Adj (.inl x) (.inr y) from by simp [square, completeBipartiteGraph_adj]).reachable
    | inr x =>
      cases y with
      | inl y => exact (show square.Adj (.inr x) (.inl y) from by simp [square, completeBipartiteGraph_adj]).reachable
      | inr y =>
        exact (show square.Adj (.inr x) (.inl ⟨0⟩) from by simp [square, completeBipartiteGraph_adj]).reachable.trans
          (show square.Adj (.inl ⟨0⟩) (.inr y) from by simp [square, completeBipartiteGraph_adj]).reachable

private theorem square_proper : ∀ x y, square.{u}.Adj x y → x.isLeft ≠ y.isLeft := by
  intro x y h
  cases x <;> cases y <;> simp_all [square, completeBipartiteGraph_adj]

private theorem square_left : square.{u}.neighborFinset (.inl ⟨0⟩) =
    {.inr ⟨0⟩, .inr ⟨1⟩} := by
  ext x
  rw [SimpleGraph.mem_neighborFinset]
  cases x with
  | inl x => simp [square, completeBipartiteGraph_adj]
  | inr x => rcases x with ⟨x⟩; fin_cases x <;> simp [square, completeBipartiteGraph_adj]

private theorem square_right : square.{u}.neighborFinset (.inr ⟨0⟩) =
    {.inl ⟨0⟩, .inl ⟨1⟩} := by
  ext x
  rw [SimpleGraph.mem_neighborFinset]
  cases x with
  | inr x => simp [square, completeBipartiteGraph_adj]
  | inl x => rcases x with ⟨x⟩; fin_cases x <;> simp [square, completeBipartiteGraph_adj]

private theorem zero_bad : ¬ zeroLaw bad.{u} := by
  intro h
  obtain ⟨ρ, σ, _, _, _, _, _, hb⟩ := h square (fun x => x.isLeft)
    square_proper (.inl ⟨0⟩) (by rw [square_left]; norm_num)
  exact hb rfl

private theorem one_bad : ¬ oneLaw bad.{u} := by
  intro h
  obtain ⟨ρ, σ, _, _, _, _, _, _, v, hb⟩ := h square square_connected
    (fun x => x.isLeft) square_proper (fun _ => 1) (by simp)
    (.inl ⟨0⟩) (.inr ⟨0⟩) (by rw [square_left]; norm_num)
    (by rw [square_right]; norm_num) (by rw [square_left, square_right]; decide)
  exact hb rfl

@[reducible] private def fixtureParameters : Parameters.{u} where
  Vertex := (ULift.{u} (Fin 2)) ⊕ (ULift.{u} (Fin 2))
  finiteVertex := inferInstance
  equalVertex := inferInstance
  graph := square

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  cases i
  obtain ⟨ρ, σ, _, _, _, _, _, _, v, hb⟩ :=
    physical_single_setting_lower square.{u} square_connected
      (fun x => x.isLeft) square_proper (fun _ => 1) (by simp)
      (.inl ⟨0⟩) (.inr ⟨0⟩) (by rw [square_left]; norm_num)
      (by rw [square_right]; norm_num) (by rw [square_left, square_right]; decide)
  refine ⟨fixtureParameters, ρ, σ, ?_⟩
  intro h
  exact hb (congrFun h v)

def zeroFamily : Registration zeroArena.{u} (type_of% (@physical_zero_setting_lower.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@physical_zero_setting_lower.{u}, bad, zero_bad⟩
  sensitivity := by
    constructor
    · intro i
      cases i
      refine ⟨bad, ?_, ?_, zero_bad⟩
      · intro j hj; cases j; exact (hj rfl).elim
      · funext e; exact nomatch e
    · intro e; exact nomatch e
  dependence := dependence

/-- The original density-state contract and actual blockade operand are retained. -/
def zeroRegistration : Contract.Registration
    (@physical_zero_setting_lower.{u}) (Realization signature.{u}) Type Unit := {
  unitName := `Reg.D5.S3.Quantum.Fibers.BipartiteBlockade.PhysicalSingleSettingLower.physical_zero_setting_lower.__information_unit,
  realizationName := `Reg.D5.S3.Quantum.Fibers.BipartiteBlockade.PhysicalSingleSettingLower.zeroFamily,
  realizationSource := none,
  generated := false,
  arena := .source ⟨zeroArena⟩,
  objectArena := .source ⟨zeroArena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source zeroArena ⟨zeroFamily⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature
    (fun _ p ρ v => by
      letI := p.finiteVertex
      letI := p.equalVertex
      exact (Matrix.trace (ρ * blockade p.graph v)).re)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

def oneFamily : Registration oneArena.{u} (type_of% (@physical_single_setting_lower.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@physical_single_setting_lower.{u}, bad, one_bad⟩
  sensitivity := by
    constructor
    · intro i
      cases i
      refine ⟨bad, ?_, ?_, one_bad⟩
      · intro j hj; cases j; exact (hj rfl).elim
      · funext e; exact nomatch e
    · intro e; exact nomatch e
  dependence := dependence

/-- The original density-state contract and actual blockade operand are retained. -/
def oneRegistration : Contract.Registration
    (@physical_single_setting_lower.{u}) (Realization signature.{u}) Type Unit := {
  unitName := `Reg.D5.S3.Quantum.Fibers.BipartiteBlockade.PhysicalSingleSettingLower.physical_single_setting_lower.__information_unit,
  realizationName := `Reg.D5.S3.Quantum.Fibers.BipartiteBlockade.PhysicalSingleSettingLower.oneFamily,
  realizationSource := none,
  generated := false,
  arena := .source ⟨oneArena⟩,
  objectArena := .source ⟨oneArena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source oneArena ⟨oneFamily⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature
    (fun _ p ρ v => by
      letI := p.finiteVertex
      letI := p.equalVertex
      exact (Matrix.trace (ρ * blockade p.graph v)).re)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

/-- info: 'Reg.D5.S3.Quantum.Fibers.BipartiteBlockade.PhysicalSingleSettingLower.zeroFamily' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms zeroFamily

/-- info: 'Reg.D5.S3.Quantum.Fibers.BipartiteBlockade.PhysicalSingleSettingLower.oneFamily' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms oneFamily

/-- info: 'Reg.D5.S3.Quantum.Fibers.BipartiteBlockade.PhysicalSingleSettingLower.zeroRegistration' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms zeroRegistration

/-- info: 'Reg.D5.S3.Quantum.Fibers.BipartiteBlockade.PhysicalSingleSettingLower.oneRegistration' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms oneRegistration

end Reg.D5.S3.Quantum.Fibers.BipartiteBlockade.PhysicalSingleSettingLower
