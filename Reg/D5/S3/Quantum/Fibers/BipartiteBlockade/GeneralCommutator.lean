import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Quantum.Fibers.BipartiteBlockade.GeneralCommutator

attribute [local instance] LieRing.ofAssociativeRing
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped Classical BigOperators Matrix
namespace Reg.D5.S3.Quantum.Fibers.BipartiteBlockade.GeneralCommutator
open _root_.D5.S3.Quantum.Fibers.BipartiteBlockade
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open private flip_indicator from D5.S3.Quantum.Fibers.BipartiteBlockade.GeneralCommutator
universe u

structure Parameters where
  Vertex : Type u
  finiteVertex : Fintype Vertex
  equalVertex : DecidableEq Vertex
  graph : SimpleGraph Vertex

@[reducible] def signature : Signature where
  Params := Parameters.{u}
  State p := p.Vertex → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Matrix (Configuration p.graph) (Configuration p.graph) ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} := realize signature
  (fun _ p Ω => by
    letI := p.finiteVertex
    letI := p.equalVertex
    exact hamiltonian p.graph Ω)
  (fun e => nomatch e)

def rejected : Realization signature.{u} := realize signature
  (fun _ _ _ => 0) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature.{u}
  Law O := ∀ (p : Parameters),
    letI : Fintype p.Vertex := p.finiteVertex
    letI : DecidableEq p.Vertex := p.equalVertex
    ∀ (Ω : p.Vertex → ℂ) (v : p.Vertex),
    ⁅O.readout () p Ω, ⁅O.readout () p Ω, number p.graph v⁆⁆ =
      (2 * Ω v ^ 2) • ((2 : ℂ) • number p.graph v - blockade p.graph v) +
      ∑ w, if p.graph.Adj w v then (Ω w * Ω v) • exchange p.graph w v else 0

@[reducible] private def unitParameters : Parameters.{u} where
  Vertex := ULift.{u} Unit
  finiteVertex := inferInstance
  equalVertex := inferInstance
  graph := ⊥

private def vacuum : Configuration unitParameters.graph := ⟨∅, by simp⟩
private def occupied : Configuration unitParameters.graph := ⟨{⟨()⟩}, by simp⟩

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  letI : DecidableRel unitParameters.{u}.graph.Adj := fun _ _ => Classical.propDecidable _
  have he := congrArg (fun M => M vacuum vacuum)
    (h unitParameters.{u} (fun _ => 1) ⟨()⟩)
  norm_num [rejected, realize, unitParameters, vacuum, number, blockade, clear,
    Matrix.diagonal_apply, Matrix.zero_apply, Ring.lie_def, Matrix.mul_apply] at he
  change (0 : ℂ) = -2 at he
  norm_num at he

private theorem actual_law : arena.{u}.Law actual := by
  intro p Ω v
  letI := p.finiteVertex
  letI := p.equalVertex
  exact general_double_commutator p.graph Ω v

private theorem actual_dependence : ObservationalDependence signature.{u} actual := by
  rintro ⟨⟩
  refine ⟨unitParameters, (fun _ => 0), (fun _ => 1), ?_⟩
  intro he
  have hx := congrArg (fun M => M vacuum occupied) he
  norm_num [actual, realize, hamiltonian, unitParameters, flip_indicator,
    vacuum, occupied] at hx

def familyRegistration : Registration arena.{u}
    (∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) (Ω : V → ℂ) (v : V),
      ⁅hamiltonian G Ω, ⁅hamiltonian G Ω, number G v⁆⁆ =
        (2 * Ω v ^ 2) • ((2 : ℂ) • number G v - blockade G v) +
        ∑ w, if G.Adj w v then (Ω w * Ω v) • exchange G w v else 0) where
  actual := actual
  bridge := by
    constructor
    · intro h p Ω v
      letI := p.finiteVertex
      letI := p.equalVertex
      exact h p.Vertex p.graph Ω v
    · intro h V _ _ G Ω v
      exact h ⟨V, inferInstance, inferInstance, G⟩ Ω v
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, ?_, rejected_law⟩
      · intro j hj; exact (hj (Subsingleton.elim _ _)).elim
      · funext e; exact nomatch e
    · intro e; exact nomatch e
  dependence := actual_dependence

/-- The readout is the Hamiltonian selected inside the source commutator. -/
def registration : Contract.Registration
    (@_root_.D5.S3.Quantum.Fibers.BipartiteBlockade.general_double_commutator.{u})
    (Realization signature.{u}) Type Unit := {
  unitName := `Reg.D5.S3.Quantum.Fibers.BipartiteBlockade.GeneralCommutator.general_double_commutator.__information_unit,
  realizationName := `Reg.D5.S3.Quantum.Fibers.BipartiteBlockade.GeneralCommutator.familyRegistration,
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
    (fun _ p Ω => by
      letI := p.finiteVertex
      letI := p.equalVertex
      exact hamiltonian p.graph Ω)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Quantum.Fibers.BipartiteBlockade.GeneralCommutator, definition := none, coordinates := #[0, 3], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg"], stateBinder := 4, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

/-- info: 'Reg.D5.S3.Quantum.Fibers.BipartiteBlockade.GeneralCommutator.registration' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms registration

end Reg.D5.S3.Quantum.Fibers.BipartiteBlockade.GeneralCommutator
