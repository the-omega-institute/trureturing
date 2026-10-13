import D5.S3.ObserverMemory.Prediction.EventualCycleAverage
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

open D5.S3.ObserverMemory.Prediction.EventualCycleAverage
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators

namespace Reg.D5.S3.ObserverMemory.Prediction.EventualCycleAverage

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

@[reducible] def signature : Signature where
  Params := Σ p : Nat, Fin p → Real
  State param := Fin param.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Real
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ ⟨_p, value⟩ index => value index)
  (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ => 0) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law F := ∀ {p : Nat} (hp : 0 < p) (value : Fin p → Real) (n : Nat),
    (∑ i ∈ Finset.range n, F.readout () ⟨p, value⟩ ⟨i % p, Nat.mod_lt i hp⟩) =
      ((n / p : Nat) : Real) *
      (∑ i ∈ Finset.range p, value ⟨i % p, Nat.mod_lt i hp⟩) +
      ∑ i ∈ Finset.range (n % p), value ⟨i % p, Nat.mod_lt i hp⟩

private theorem positive : arena.Law actual := by
  intro p hp value n
  exact sum_cycle_mod_eq_blocks_remainder hp value n

private theorem negative : ¬ arena.Law rejected := by
  intro law
  have impossible := law (p := 1) (by omega) (fun _ => 1) 1
  norm_num [rejected, realize] at impossible

def evidence : Registration arena
    (type_of% (@_root_.D5.S3.ObserverMemory.Prediction.EventualCycleAverage.sum_cycle_mod_eq_blocks_remainder)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positive, rejected, negative⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, negative⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨⟨2, fun i => (i.val : Real)⟩, 0, 1, ?_⟩
    norm_num [actual, realize]

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.ObserverMemory.Prediction.EventualCycleAverage.sum_cycle_mod_eq_blocks_remainder)
    (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := `Reg.D5.S3.ObserverMemory.Prediction.EventualCycleAverage.sum_cycle_mod_eq_blocks_remainder,
  realizationName := `Reg.D5.S3.ObserverMemory.Prediction.EventualCycleAverage.evidence,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Prediction.EventualCycleAverage,
    definition := none, coordinates := #[0, 2],
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "arg", "body", "fn"],
      stateBinder := 0, functionOperand := true, stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

#print axioms evidence
#print axioms registration
end
end Reg.D5.S3.ObserverMemory.Prediction.EventualCycleAverage
