import LeanInformationAuditInterface.Contract.Registration
import LeanInformationAuditInterface.Contract.AuricFib
import Reg.Support.DependentFamily
import D5.S3.Quantum.Fibers.BipartiteBlockade.BornFiveMode

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped Classical BigOperators ComplexOrder
namespace Reg.D5.S3.Quantum.Fibers.BipartiteBlockade.BornFiveMode
open _root_.D5.S3.Quantum.Fibers.BipartiteBlockade
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
universe u

structure Parameters where
  Vertex : Type u
  finiteVertex : Fintype Vertex
  equalVertex : DecidableEq Vertex
  graph : SimpleGraph Vertex
  left : Vertex
  center : Vertex
  right : Vertex

@[reducible] def signature : Signature where
  Params := Parameters.{u}
  State p := Matrix (Configuration p.graph) (Configuration p.graph) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Fin 5 → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} := realize signature
  (fun _ p ρ => by
    letI := p.finiteVertex
    letI := p.equalVertex
    exact bornModeLaw p.graph p.left p.center p.right ρ)
  (fun e => nomatch e)

/-- The source retains every graph, state, coloring and drive premise. -/
def fullLaw (r : Realization signature.{u}) : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (u v w : V)
    (hN : ∀ x, G.Adj v x ↔ x = u ∨ x = w)
    (huw : u ≠ w)
    (color : V → Bool) (hcolor : ∀ x y, G.Adj x y → color x ≠ color y)
    (Ω : V → ℝ) (hΩ : Ω v ≠ 0)
    (ρ : Matrix (Configuration G) (Configuration G) ℂ)
    (hρ : ρ.PosSemidef) (ht : Matrix.trace ρ = 1),
    let β := 2 * occupationMean G ρ v +
      if color v then
        (acceleration G (colorScaledDrive color Ω) ρ v - 2 * acceleration G Ω ρ v) /
          (4 * Ω v ^ 2)
      else
        (2 * acceleration G Ω ρ v - acceleration G (colorScaledDrive color Ω) ρ v) /
          (2 * Ω v ^ 2)
    (∀ k, 0 ≤ r.readout () ⟨V, inferInstance, inferInstance, G, u, v, w⟩ ρ k) ∧
    (∑ k, r.readout () ⟨V, inferInstance, inferInstance, G, u, v, w⟩ ρ k) = 1 ∧
    r.readout () ⟨V, inferInstance, inferInstance, G, u, v, w⟩ ρ =
      ![β - occupationMean G ρ v,
        1 - β - occupationMean G ρ w,
        occupationMean G ρ v,
        1 - β - occupationMean G ρ u,
        β - 1 + occupationMean G ρ u + occupationMean G ρ w] ∧
    ∃ σ τ : Matrix (Configuration G) (Configuration G) ℂ,
      σ.PosSemidef ∧ Matrix.trace σ = 1 ∧
      τ.PosSemidef ∧ Matrix.trace τ = 1 ∧
      (∀ x, occupationMean G σ x = occupationMean G τ x) ∧
      blockadeMean G σ v ≠ blockadeMean G τ v

@[reducible] def arena : Arena where
  signature := signature.{u}
  Law := fullLaw

private def bad : Realization signature.{u} := realize signature
  (fun _ _ _ _ => -1) (fun e => nomatch e)

private def fixtureGraph : SimpleGraph (ULift.{u} (Fin 3)) :=
  SimpleGraph.fromRel (fun a b => a.down = 1 ∧ b.down ≠ 1)

private def fixtureEmpty : Configuration fixtureGraph.{u} := ⟨∅, by simp⟩

private def fixtureDensity : Matrix (Configuration fixtureGraph.{u})
    (Configuration fixtureGraph.{u}) ℂ :=
  Matrix.diagonal (fun S => if S = fixtureEmpty then 1 else 0)

private theorem fixture_psd : fixtureDensity.{u}.PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  intro S
  change (0 : ℂ) ≤ if S = fixtureEmpty then 1 else 0
  split_ifs <;> norm_num

private theorem fixture_trace : Matrix.trace fixtureDensity.{u} = 1 := by
  simp [fixtureDensity, Matrix.trace]

private theorem fixture_neighbors : ∀ x, fixtureGraph.{u}.Adj ⟨1⟩ x ↔
    x = ⟨0⟩ ∨ x = ⟨2⟩ := by
  intro ⟨x⟩
  fin_cases x <;> norm_num [fixtureGraph, SimpleGraph.fromRel_adj]

private theorem fixture_color : ∀ x y, fixtureGraph.{u}.Adj x y →
    (x.down == 1) ≠ (y.down == 1) := by
  intro ⟨x⟩ ⟨y⟩
  fin_cases x <;> fin_cases y <;> norm_num [fixtureGraph, SimpleGraph.fromRel_adj]

private theorem actual_law : fullLaw actual.{u} := by
  exact @born_five_mode_reconstruction.{u}

private theorem bad_law : ¬ fullLaw bad.{u} := by
  intro h
  have hh := (h fixtureGraph ⟨0⟩ ⟨1⟩ ⟨2⟩ fixture_neighbors (by decide)
    (fun x => x.down == 1) fixture_color (fun _ => 1) (by norm_num)
    fixtureDensity fixture_psd fixture_trace).1 0
  norm_num [bad, realize] at hh

private def fixtureParameters : Parameters.{u} where
  Vertex := ULift.{u} (Fin 3)
  finiteVertex := inferInstance
  equalVertex := inferInstance
  graph := fixtureGraph
  left := ⟨0⟩
  center := ⟨1⟩
  right := ⟨2⟩

private theorem fixture_mass :
    actual.readout () fixtureParameters.{u} fixtureDensity 0 = 1 := by
  change (∑ S, if localMode fixtureGraph ⟨0⟩ ⟨1⟩ ⟨2⟩ S = 0 then
    (fixtureDensity S S).re else 0) = 1
  rw [Finset.sum_eq_single fixtureEmpty]
  · norm_num [fixtureDensity, Matrix.diagonal_apply, localMode, fixtureEmpty]
  · intro S _ hS
    simp [fixtureDensity, Matrix.diagonal_apply, hS]
  · simp

private theorem actual_dependence : ObservationalDependence signature.{u} actual := by
  intro i
  cases i
  refine ⟨fixtureParameters, fixtureDensity, 0, ?_⟩
  intro h
  have hh := congrFun h 0
  have hz : actual.readout () fixtureParameters.{u} 0 0 = 0 := by
    change (∑ S, if localMode fixtureGraph ⟨0⟩ ⟨1⟩ ⟨2⟩ S = 0 then
      (0 : ℂ).re else 0) = 0
    simp
  rw [fixture_mass, hz] at hh
  norm_num at hh

/-- Whole-family variation and dependence concern the actual Born-law operand. -/
def familyRegistration : Registration arena.{u}
    (type_of% (@born_five_mode_reconstruction.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, bad, bad_law⟩
  sensitivity := by
    constructor
    · intro i
      cases i
      refine ⟨bad, ?_, ?_, bad_law⟩
      · intro j hj
        cases j
        exact (hj rfl).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := actual_dependence

/-- The actual source family uses the enrolled dependent-family template. -/
def registration : Contract.Registration
    (@born_five_mode_reconstruction.{u}) (Realization signature.{u}) Type Unit := {
  unitName := `Reg.D5.S3.Quantum.Fibers.BipartiteBlockade.BornFiveMode.born_five_mode_reconstruction.__information_unit,
  realizationName := `Reg.D5.S3.Quantum.Fibers.BipartiteBlockade.BornFiveMode.familyRegistration,
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
    (fun _ p ρ => by
      letI := p.finiteVertex
      letI := p.equalVertex
      exact bornModeLaw p.graph p.left p.center p.right ρ)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fibers.BipartiteBlockade.BornFiveMode,
    definition := none,
    coordinates := #[0, 3, 4, 5, 6],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "fn", "arg", "fn", "arg"],
      stateBinder := 13,
      functionOperand := false,
      stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

/-- The same Born law is the task; no finite presentation of arbitrary complex
states or Fibonacci continuation is asserted. -/
def analysisSource : Analysis.Source
    (@born_five_mode_reconstruction.{u}) where
  signature := signature
  actual := actual
  rebuild := fullLaw
  reconstruction := .exact
  selection := {
    owner := `D5.S3.Quantum.Fibers.BipartiteBlockade.BornFiveMode,
    definition := none,
    coordinates := #[0, 3, 4, 5, 6],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "fn", "arg", "fn", "arg"],
      stateBinder := 13,
      functionOperand := false,
      stateOperand := none,
      booleanPredicate := false }] }

def analysis : AuricFib.Contract.Application
    (@born_five_mode_reconstruction.{u}) where
  evidence := .typed {
    source := analysisSource
    plan := { task := (), initial := [], additions := [[()]] }
    acquisition := .unavailable "No complete finite presentation of the complex density-state family; no native Fibonacci continuation bridge" }

/-- info: 'Reg.D5.S3.Quantum.Fibers.BipartiteBlockade.BornFiveMode.familyRegistration' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms familyRegistration
/-- info: 'Reg.D5.S3.Quantum.Fibers.BipartiteBlockade.BornFiveMode.registration' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms registration
/-- info: 'Reg.D5.S3.Quantum.Fibers.BipartiteBlockade.BornFiveMode.analysis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms analysis

end Reg.D5.S3.Quantum.Fibers.BipartiteBlockade.BornFiveMode
