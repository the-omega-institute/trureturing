import D5.S3.StatisticalMechanics.Percolation.ThreeTerminalFaceBound
import Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond
import LeanInformationAuditInterface.Contract.AuricFib

/-! The finite-edge bound retains the complete independent source family. -/

namespace Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalFaceBound

open _root_.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond
open _root_.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalFaceBound
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond.Probability
open LeanInformationAudit
universe u v
noncomputable section

/-- A whole-family intervention violating the quantitative source law. -/
def bad : Realization signature.{u,v} := realize _
  (fun _ _ s => match s with | .separate | .all => 1 | _ => 0)
  (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u,v}
  Law R := ∀ {V : Type u} {E : Type v} [hV : Fintype V] [dV : DecidableEq V]
    [hE : Fintype E] [dE : DecidableEq E] (ends : E → V × V) (a b c : V)
    (θ : E → ℝ) (_hθ : ∀ e, θ e ∈ Set.Icc 0 1) (_hm : 0 < Fintype.card E),
    |delta (R.readout () ⟨V,E,hV,dV,hE,dE,ends,a,b,c,θ⟩)| ≤
      (2 : ℝ)^(Fintype.card E-1) * R.readout () ⟨V,E,hV,dV,hE,dE,ends,a,b,c,θ⟩ .ac

private theorem rejected : ¬ arena.{u,v}.Law bad := by
  intro h
  have hh := h
    (fun _ : PUnit.{v+1} => ((PUnit.unit : PUnit.{u+1}),PUnit.unit))
    PUnit.unit PUnit.unit PUnit.unit (fun _ => 0)
    (fun _ => by norm_num) (by simp)
  norm_num [bad,realize,delta] at hh

def registration : Registration arena.{u,v} (type_of% @edge_count_bound.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨edge_count_bound,bad,rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad,?_,?_,rejected⟩
      · intro j h
        exact (h (Subsingleton.elim _ _)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence :=
    Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond.Probability.registration.dependence

def register_edge_count_bound : Contract.Registration (@edge_count_bound.{u,v})
    (Realization signature.{u,v}) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalFaceBound.register_edge_count_bound
  realizationName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalFaceBound.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p => by
    letI := p.finiteVertices
    letI := p.decidableVertices
    letI := p.finiteEdges
    letI := p.decidableEdges
    exact law p.ends p.a p.b p.c p.rate) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

/-- info: 'Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalFaceBound.register_edge_count_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms register_edge_count_bound


/-- The selected occurrence is the same full Bernoulli partition law as in the bound. -/
def analysisSource : Analysis.Source (@edge_count_bound.{u,v}) :=
  Analysis.Source.ofRegistration _ registration (by
    unfold registration arena
    exact .exact) {
    owner := `D5.S3.StatisticalMechanics.Percolation.ThreeTerminalFaceBound
    definition := none
    coordinates := #[0,1,6,7,8,9,10]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body",
        "body","body","body","body","body","fn","arg","arg","arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }

/-- The generic real-rate family lacks the finite native reader and reply adapter. -/
def analysis : AuricFib.Contract.Application (@edge_count_bound.{u,v}) where
  evidence := .typed {
    source := analysisSource
    plan := {task := (),initial := [],additions := [[()]]}
    acquisition := .unavailable
      "Actual finite-edge partition-law family: raw coordinate binding and reflected finite readout table unacquired; no native Fibonacci reader and total suffix reply bridge" }

/-- info: 'Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalFaceBound.analysis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms analysis

end
end Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalFaceBound
