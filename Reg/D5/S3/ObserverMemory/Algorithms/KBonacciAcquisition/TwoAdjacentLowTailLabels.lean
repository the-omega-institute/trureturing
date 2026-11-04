import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.TwoAdjacentLowTailLabels
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

/-! Dependent-family readouts for the threshold-three lower bound and complete price law. -/

open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition
open D5.S3.ObserverMemory.Algorithms.KBonacciIrreversibleAcquisition
open D5.S0.Tower.DBonacci.Names
open LiteralModel EndpointCells OriginalNarrowCost OriginalExecutionBridge DonorCorrection
open PhysicalWindowDecoder OriginalAcquiredTrace GlobalPresetObstruction
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
    (type_of% (realize signature.{u} actual.{u}.readout actual.{u}.anchor)) Unit Unit := {
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
  readout := some (realize signature.{u} actual.{u}.readout actual.{u}.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.TwoAdjacentLowTailLabels,
    definition := none,
    coordinates := #[0, 1, 2, 6, 8],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "domain", "fn", "arg"],
      stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

#print axioms evidence
#print axioms registration

namespace Whole
@[reducible] def signature : Signature where
  Params := Σ _Q : ℕ, ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ∞
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ d => (d : ℕ∞)) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => 0) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ {Y : Type u} (Q m : ℕ) (hQ : 2 ≤ Q) (hm : 4 ≤ m)
    (labels : Fin 4 → Y) (distinct : Function.Injective labels) (bottom : Y)
    (alphabet : Bool),
    let fee := Q + 1 + (if m % 2 = 0 then 1 else 0)
    GlobalAdaptivePrice (Q * m) m (by nlinarith) alphabet (initialLabel Q m labels bottom) =
      R.readout () ⟨Q, m⟩ fee ∧
    GlobalPresetPrice (Q * m) m (by nlinarith) alphabet (initialLabel Q m labels bottom) =
      (fee : ℕ∞) ∧
    (attainingWords Q m).length = fee ∧
    (∀ s, tailAfter s (queryWord m) = 0 ∧ tailAfter s (finalWord m) = 0) ∧
    (attainingWords 2 4).map List.ofFn =
      [[true,true,true,false], [false,true,false,true],
        [false,true,false,false], [true,false,false,false]] ∧
    (attainingWords 2 5).map List.ofFn =
      [[true,true,true,false,true], [true,false,true,false,true],
        [false,true,false,false,false]] ∧
    ∀ history : List (AllowedBlock (Q * m) m alphabet),
      let w := history.flatMap (fun a => List.ofFn a.val)
      let f := initialLabel Q m labels bottom
      let decode := archiveDecoder Q m labels bottom
      let pi : NarrowWindowCost.Selector m Y := fun free ar =>
        match free with
        | none => .inl bottom
        | some v => finalSelector 0 (attainingWords Q m) (decode v) free ar
      let q := OriginalRecord (Q * m) (by nlinarith) w
      let issued := if q = none then [] else scriptArchive (attainingWords Q m) q
      PaidTrace pi (NarrowWindowCost.output (Q * m) (by nlinarith) w) q [] issued (f q) ∧
      issued.map Prod.fst = (if q = none then [] else attainingWords Q m) ∧
      issued.length = (if q = none then 0 else fee) ∧
      NarrowWindowCost.execute (Q * m) (by nlinarith) pi fee w
        (NarrowWindowCost.output (Q * m) (by nlinarith) w) [] =
          some (f q, issued.length)

private theorem positive : arena.{u}.Law actual := original_threshold_three
private theorem negative : ¬ arena.{u}.Law rejected := by
  intro law
  have bad := (law 2 4 (by omega) (by omega)
    (fun a => (ULift.up a : ULift.{u} (Fin 4)))
    (by intro a b eq; exact congrArg ULift.down eq) (ULift.up 0) false).1
  have good := (original_threshold_three 2 4 (by omega) (by omega)
    (fun a => (ULift.up a : ULift.{u} (Fin 4)))
    (by intro a b eq; exact congrArg ULift.down eq) (ULift.up 0) false).1
  rw [good] at bad
  norm_num [rejected, realize, signature] at bad

def evidence : Registration arena.{u}
    (type_of% (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.TwoAdjacentLowTailLabels.original_threshold_three.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positive, rejected, negative⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, negative⟩,
    fun e => nomatch e⟩
  dependence := by
    intro i
    cases i
    exact ⟨⟨2, 4⟩, 0, 1, by decide⟩

noncomputable def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.TwoAdjacentLowTailLabels.original_threshold_three.{u})
    (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.TwoAdjacentLowTailLabels.original_threshold_three.__information_unit,
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.TwoAdjacentLowTailLabels.Whole.evidence,
  realizationSource := none, generated := false,
  arena := .source ⟨arena.{u}⟩, objectArena := .source ⟨arena.{u}⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena.{u} ⟨evidence.{u}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence }, bundleNonempty := .absent,
  readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.TwoAdjacentLowTailLabels,
    definition := none, coordinates := #[1, 2],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "arg"],
      stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

#print axioms evidence
#print axioms registration
end Whole
end
end Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.TwoAdjacentLowTailLabels

namespace Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.TwoAdjacentLowTailLabels.FirstZeroForm
noncomputable section

@[reducible] def signature : Signature where
  Params := Unit
  State _ := List Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := List Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ _ bits => bits) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => []) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ bits : List Bool,
    R.readout () () bits = List.replicate bits.length true ∨
      ∃ a rest, R.readout () () bits = List.replicate a true ++ false :: rest

private theorem positive : arena.Law actual :=
  _root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.TwoAdjacentLowTailLabels.first_zero_form
private theorem negative : ¬ arena.Law rejected := by
  intro law
  rcases law [true] with equal | ⟨a, rest, equal⟩
  · cases equal
  · change ([] : List Bool) = List.replicate a true ++ false :: rest at equal
    have impossible := congrArg List.length equal
    simp at impossible

def evidence : Registration arena
    (type_of% (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.TwoAdjacentLowTailLabels.first_zero_form)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positive, rejected, negative⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, negative⟩,
    fun e => nomatch e⟩
  dependence := by
    intro i
    cases i
    exact ⟨(), [], [true], by decide⟩

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.TwoAdjacentLowTailLabels.first_zero_form)
    (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.TwoAdjacentLowTailLabels.first_zero_form.__information_unit,
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.TwoAdjacentLowTailLabels.FirstZeroForm.evidence,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.TwoAdjacentLowTailLabels,
    definition := none, coordinates := #[],
    readouts := #[{
      path := #["body", "fn", "arg", "fn", "arg"],
      stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

#print axioms evidence
#print axioms registration
end
end Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.TwoAdjacentLowTailLabels.FirstZeroForm
