import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Quantum.Fibers.BipartiteBlockade.TwoColorReadout

attribute [local instance] LieRing.ofAssociativeRing
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped Classical BigOperators Matrix
namespace Reg.D5.S3.Quantum.Fibers.BipartiteBlockade.TwoColorReadout
open _root_.D5.S3.Quantum.Fibers.BipartiteBlockade
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
universe u

structure Parameters where
  Vertex : Type u
  finiteVertex : Fintype Vertex
  equalVertex : DecidableEq Vertex
  graph : SimpleGraph Vertex
  color : Vertex → Bool
  drive : Vertex → ℝ

@[reducible] def signature : Signature where
  Params := Parameters.{u}
  State p := Matrix (Configuration p.graph) (Configuration p.graph) ℂ
  Role := Fin 3
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.Vertex → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} := realize signature
  (fun i p ρ v => by
    letI := p.finiteVertex
    letI := p.equalVertex
    exact if i = 0 then occupationMean p.graph ρ v else if i = 1 then
      acceleration p.graph p.drive ρ v else
      acceleration p.graph (colorScaledDrive p.color p.drive) ρ v)
  (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature.{u}
  Law O := ∀ (p : Parameters),
    letI : Fintype p.Vertex := p.finiteVertex
    letI : DecidableEq p.Vertex := p.equalVertex
    (∀ v w, p.graph.Adj v w → p.color v ≠ p.color w) →
    ∀ (ρ : Matrix (Configuration p.graph) (Configuration p.graph) ℂ) (v : p.Vertex),
    p.drive v ≠ 0 →
    blockadeMean p.graph ρ v = 2 * O.readout 0 p ρ v +
      if p.color v then
        (O.readout 2 p ρ v - 2 * O.readout 1 p ρ v) / (4 * p.drive v ^ 2)
      else (2 * O.readout 1 p ρ v - O.readout 2 p ρ v) / (2 * p.drive v ^ 2)

private def bad (i : Fin 3) : Realization signature.{u} := realize signature
  (fun j p ρ v => actual.readout j p ρ v + if j = i then 1 else 0)
  (fun e => nomatch e)

@[reducible] private def unitParameters : Parameters.{u} where
  Vertex := ULift.{u} Unit
  finiteVertex := inferInstance
  equalVertex := inferInstance
  graph := ⊥
  color := fun _ => true
  drive := fun _ => 1

private def vacuum : Configuration unitParameters.graph := ⟨∅, by simp⟩
private def occupied : Configuration unitParameters.graph := ⟨{⟨()⟩}, by simp⟩

private theorem bad_law (i : Fin 3) : ¬ arena.{u}.Law (bad i) := by
  intro h
  have he := h unitParameters (by simp [unitParameters]) 0 ⟨()⟩ (by norm_num [unitParameters])
  fin_cases i <;>
    norm_num [bad, actual, realize, unitParameters, occupationMean, blockadeMean,
      acceleration, Fin.ext_iff, show (2 : Fin 3) ≠ 0 by decide,
      show (2 : Fin 3) ≠ 1 by decide, show (0 : Fin 3) ≠ 2 by decide,
      show (1 : Fin 3) ≠ 2 by decide] at he

private theorem actual_law : arena.{u}.Law actual := by
  intro p hc ρ v hΩ
  letI := p.finiteVertex
  letI := p.equalVertex
  simpa [actual, realize] using two_color_readout_inverse p.graph p.color hc p.drive ρ v hΩ

private theorem actual_dependence : ObservationalDependence signature.{u} actual := by
  have hvac (Ω : unitParameters.Vertex → ℝ) (v : unitParameters.Vertex) :
      acceleration unitParameters.graph Ω (Matrix.single vacuum vacuum 1) v =
        2 * Ω v ^ 2 := by
    unfold acceleration
    rw [general_double_commutator]
    simp [unitParameters, Matrix.trace_single_mul, number, blockade, clear, vacuum,
      ← Complex.ofReal_pow]
  intro i
  fin_cases i
  · refine ⟨unitParameters, 0, Matrix.single occupied occupied 1, ?_⟩
    intro he
    have hx := congrArg (fun f => f ⟨()⟩) he
    norm_num [actual, realize, unitParameters, occupationMean, Matrix.trace_single_mul,
      number, occupied, Matrix.diagonal_apply] at hx
  · refine ⟨unitParameters, 0, Matrix.single vacuum vacuum 1, ?_⟩
    intro he
    have hx := congrArg (fun f => f ⟨()⟩) he
    change acceleration unitParameters.graph unitParameters.drive 0 ⟨()⟩ =
      acceleration unitParameters.graph unitParameters.drive
        (Matrix.single vacuum vacuum 1) ⟨()⟩ at hx
    have hz : acceleration unitParameters.graph unitParameters.drive 0 ⟨()⟩ = 0 := by
      simp [acceleration, Matrix.mul_apply]
    rw [hz, hvac] at hx
    norm_num [unitParameters] at hx
  · refine ⟨unitParameters, 0, Matrix.single vacuum vacuum 1, ?_⟩
    intro he
    have hx := congrArg (fun f => f ⟨()⟩) he
    change acceleration unitParameters.graph
        (colorScaledDrive unitParameters.color unitParameters.drive) 0 ⟨()⟩ =
      acceleration unitParameters.graph
        (colorScaledDrive unitParameters.color unitParameters.drive)
        (Matrix.single vacuum vacuum 1) ⟨()⟩ at hx
    have hz : acceleration unitParameters.graph
        (colorScaledDrive unitParameters.color unitParameters.drive) 0 ⟨()⟩ = 0 := by
      simp [acceleration, Matrix.mul_apply]
    rw [hz, hvac] at hx
    norm_num [unitParameters, colorScaledDrive] at hx

def familyRegistration : Registration arena.{u}
    (∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) (color : V → Bool),
      (∀ v w, G.Adj v w → color v ≠ color w) →
      ∀ (Ω : V → ℝ) (ρ : Matrix (Configuration G) (Configuration G) ℂ) (v : V),
      Ω v ≠ 0 → blockadeMean G ρ v = 2 * occupationMean G ρ v +
        if color v then
          (acceleration G (colorScaledDrive color Ω) ρ v - 2 * acceleration G Ω ρ v) /
            (4 * Ω v ^ 2)
        else (2 * acceleration G Ω ρ v - acceleration G (colorScaledDrive color Ω) ρ v) /
          (2 * Ω v ^ 2)) where
  actual := actual
  bridge := by
    constructor
    · intro h p hc ρ v hΩ
      letI := p.finiteVertex
      letI := p.equalVertex
      simpa [actual, realize] using h p.Vertex p.graph p.color hc p.drive ρ v hΩ
    · intro h V _ _ G color hc Ω ρ v hΩ
      simpa [actual, realize] using h ⟨V, inferInstance, inferInstance, G, color, Ω⟩ hc ρ v hΩ
  variation := ⟨actual_law, bad 0, bad_law 0⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad i, ?_, ?_, bad_law i⟩
      · intro j hj
        funext p ρ v
        simp [bad, realize, hj]
      · funext e; exact nomatch e
    · intro e; exact nomatch e
  dependence := actual_dependence

/-- The readouts select the source occupation and both acceleration functions. -/
def registration : Contract.Registration
    (@_root_.D5.S3.Quantum.Fibers.BipartiteBlockade.two_color_readout_inverse.{u})
    (Realization signature.{u}) Type Unit := {
  unitName := `Reg.D5.S3.Quantum.Fibers.BipartiteBlockade.TwoColorReadout.two_color_readout_inverse.__information_unit,
  realizationName := `Reg.D5.S3.Quantum.Fibers.BipartiteBlockade.TwoColorReadout.familyRegistration,
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
    (fun i p ρ v => by
      letI := p.finiteVertex
      letI := p.equalVertex
      exact if i = 0 then occupationMean p.graph ρ v else if i = 1 then
        acceleration p.graph p.drive ρ v else
        acceleration p.graph (colorScaledDrive p.color p.drive) ρ v)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Quantum.Fibers.BipartiteBlockade.TwoColorReadout, definition := none, coordinates := #[0, 3, 4, 6], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg", "arg", "fn"], stateBinder := 7, functionOperand := false, stateOperand := none, booleanPredicate := false }, { path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "fn", "arg", "fn", "arg", "arg", "arg", "fn"], stateBinder := 7, functionOperand := false, stateOperand := none, booleanPredicate := false }, { path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "fn", "arg", "fn", "arg", "fn", "arg", "fn"], stateBinder := 7, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

/-- info: 'Reg.D5.S3.Quantum.Fibers.BipartiteBlockade.TwoColorReadout.registration' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms registration

end Reg.D5.S3.Quantum.Fibers.BipartiteBlockade.TwoColorReadout
