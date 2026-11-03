import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.TwoAdjacentLowTailLabels
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition
open D5.S3.ObserverMemory.Algorithms.KBonacciIrreversibleAcquisition
open D5.S0.Tower.DBonacci.Names
open LiteralModel EndpointCells OriginalNarrowCost OriginalExecutionBridge DonorCorrection
open TwoAdjacentLowTailLabels
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.TwoAdjacentLowTailLabels
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

@[reducible] def signature : Signature where
  Params := Σ Y : Type u, Σ _Q : ℕ, Σ _m : ℕ, Σ _labels : Fin 4 → Y, Y
  State p := Option (LiveRecord (p.2.1 * p.2.2.1))
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} := realize signature
  (fun _ p => initialLabel p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) (fun e => nomatch e)

def rejected : Realization signature.{u} := realize signature
  (fun _ p _ => p.2.2.2.2) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature.{u}
  Law R := ∀ {Y : Type u} (Q m : ℕ) (hQ : 2 ≤ Q) (hm : 4 ≤ m)
    (even : Even m) (labels : Fin 4 → Y) (distinct : Function.Injective labels)
    (bottom : Y) (alphabet : Bool) (d : ℕ),
    OriginalAdaptiveFeasible (Q * m) m (by nlinarith) alphabet
      (R.readout () ⟨Y, Q, m, labels, bottom⟩) d → Q + 2 ≤ d

private theorem positive : arena.{u}.Law actual := even_adaptive_lower

private theorem negative : ¬ arena.{u}.Law rejected := by
  intro law
  let labels : Fin 4 → ULift.{u} (Fin 4) := ULift.up
  let bottom : ULift.{u} (Fin 4) := ⟨0⟩
  have feasible : OriginalAdaptiveFeasible 8 4 (by omega) false (fun _ => bottom) 0 := by
    refine ⟨fun _ _ => .inl bottom, ?_, rfl, ?_⟩
    · intro free ar B eq
      cases eq
    · intro history
      exact ⟨0, le_rfl, rfl⟩
  have bad := law 2 4 (by omega) (by omega) (by decide) labels
    (by intro i j eq; exact ULift.up_injective eq) bottom false 0 feasible
  omega

def evidence : Registration arena.{u}
    (type_of% (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.TwoAdjacentLowTailLabels.even_adaptive_lower.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positive, rejected, negative⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, negative⟩,
    fun e => nomatch e⟩
  dependence := by
    intro i
    cases i
    refine ⟨⟨ULift.{u} (Fin 4), 2, 4, ULift.up, ULift.up 0⟩,
      none, some ⟨0, 0, 5⟩, ?_⟩
    decide

noncomputable def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.TwoAdjacentLowTailLabels.even_adaptive_lower.{u})
    (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.TwoAdjacentLowTailLabels.even_adaptive_lower.__information_unit,
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.TwoAdjacentLowTailLabels.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena.{u}⟩,
  objectArena := .source ⟨arena.{u}⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena.{u} ⟨evidence.{u}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.TwoAdjacentLowTailLabels,
    definition := none,
    coordinates := #[0, 1, 2, 6, 8],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "type", "fn", "arg"],
      stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

#print axioms evidence
#print axioms registration
end Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.TwoAdjacentLowTailLabels
