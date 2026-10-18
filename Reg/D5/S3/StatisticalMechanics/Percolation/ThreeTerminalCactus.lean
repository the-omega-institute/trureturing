import D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCactus
import Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTree
import LeanInformationAuditInterface.Contract.AuricFib

/-! The sharp cactus invariant retains the entire actual independent-edge source family. -/

namespace Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCactus

open _root_.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond
open _root_.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTree
open _root_.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCactusSharpness
open _root_.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCactus
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTree
open SimpleGraph LeanInformationAudit
universe u
noncomputable section

local instance classical_decidable (P : Prop) : Decidable P := Classical.propDecidable P

private theorem singleton_connected : (⊥ : SimpleGraph PUnit.{u+1}).Connected :=
  connected_bot_iff.mpr ⟨inferInstance,inferInstance⟩

private theorem singleton_cactus : IsCactus (⊥ : SimpleGraph PUnit.{u+1}) := by
  intro v w p q hp _ _
  exact (isAcyclic_bot p hp).elim

abbrev invariantArena : Arena where
  signature := signature.{u}
  Law R := ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (_hG : G.Connected) (_hcactus : IsCactus G)
    (a b c : V) (θ : G.edgeSet → ℝ) (_hθ : ∀ e, θ e ∈ Set.Icc 0 1),
    0 ≤ delta (R.readout () ⟨V,G,inferInstance,a,b,c,θ⟩) ∧
      delta (R.readout () ⟨V,G,inferInstance,a,b,c,θ⟩)+
        R.readout () ⟨V,G,inferInstance,a,b,c,θ⟩ .all *
        R.readout () ⟨V,G,inferInstance,a,b,c,θ⟩ .ac ≤
      2*R.readout () ⟨V,G,inferInstance,a,b,c,θ⟩ .ac ∧
      delta (R.readout () ⟨V,G,inferInstance,a,b,c,θ⟩) ≤
        2*R.readout () ⟨V,G,inferInstance,a,b,c,θ⟩ .ac

private theorem invariant_rejected : ¬ invariantArena.{u}.Law negative := by
  intro h
  have hh := (h (⊥ : SimpleGraph PUnit.{u+1}) singleton_connected singleton_cactus
    PUnit.unit PUnit.unit PUnit.unit (fun _ => 0) (fun _ => by norm_num)).1
  norm_num [negative,realize,delta] at hh

def invariantRegistration : Registration invariantArena.{u}
    (type_of% @cactus_invariant.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨cactus_invariant,negative,invariant_rejected⟩
  sensitivity := single_sensitivity _ negative invariant_rejected
  dependence := dependence

def register_cactus_invariant : Contract.Registration (@cactus_invariant.{u})
    (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCactus.register_cactus_invariant
  realizationName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCactus.invariantRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨invariantArena⟩
  objectArena := .source ⟨invariantArena⟩
  catalog := .anonymous
  localNames := false
  realization := .source invariantArena ⟨invariantRegistration⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p => @bondLaw p.Vertices p.graph p.finiteEdges p.a p.b p.c p.rate)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

/-- info: 'Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCactus.register_cactus_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms register_cactus_invariant

/-- The observed operation queries the actual five partition masses of the
same cactus source. The full finite-graph telescope is reconstructed. -/
def analysisSource : Analysis.Source (@cactus_invariant.{u}) :=
  Analysis.Source.ofRegistration _ invariantRegistration .exact {
    owner := `D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCactus
    definition := none
    coordinates := #[0,3,6,7,8,9]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body",
        "body","body","body","fn","arg","arg","arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }

/-- Exact source reconstruction does not provide a reflected finite table or
a native Fibonacci reader and total suffix reply for these graph laws. -/
def analysis : AuricFib.Contract.Application (@cactus_invariant.{u}) where
  evidence := .typed {
    source := analysisSource
    plan := {task := (),initial := [],additions := [[()]]}
    acquisition := .unavailable
      "Actual cactus-law family: raw coordinate binding and a reflected finite readout table unacquired; arbitrary real rate evaluation and the native Fibonacci reader/reply bridge are absent" }

/-- info: 'Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCactus.analysis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms analysis

end
end Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCactus
