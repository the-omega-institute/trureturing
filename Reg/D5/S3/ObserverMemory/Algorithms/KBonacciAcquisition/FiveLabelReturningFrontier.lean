import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FiveLabelReturningFrontier
import Reg.Support.DependentFamily

/-! The complete width-seven price and trace law under a dependent-family readout. -/

open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition
open D5.S3.ObserverMemory.Algorithms.KBonacciIrreversibleAcquisition
open LiteralModel EndpointCells OriginalNarrowCost OriginalExecutionBridge
open PhysicalWindowDecoder OriginalAcquiredTrace GlobalPresetObstruction DonorCorrection
open FiveLabelReturningFrontier
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
namespace Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FiveLabelReturningFrontier
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

@[reducible] def signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ∞
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ d => (d : ℕ∞)) (fun e => nomatch e)
def oracle : Realization signature := realize signature
  (fun _ _ _ => 0) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ {Y : Type u} (Q : ℕ) (hQ : 2 ≤ Q)
    (labels : Fin 7 → Y) (distinct : Function.Injective labels) (bottom : Y)
    (alphabet : Bool),
    GlobalAdaptivePrice (7 * Q) 7 (by omega) alphabet (initialLabel Q labels bottom) =
      R.readout () Q (2 * Q + 2) ∧
    GlobalPresetPrice (7 * Q) 7 (by omega) alphabet (initialLabel Q labels bottom) =
      ((2 * Q + 2 : ℕ) : ℕ∞) ∧
    (attainingWords Q).length = 2 * Q + 2 ∧
    ∀ history : List (AllowedBlock (7 * Q) 7 alphabet),
      let w := history.flatMap (fun a => List.ofFn a.val)
      let f := initialLabel Q labels bottom
      let decode := archiveDecoder Q labels bottom
      let pi : NarrowWindowCost.Selector 7 Y := fun free ar =>
        match free with
        | none => .inl bottom
        | some v => finalSelector 0 (attainingWords Q) (decode v) free ar
      let q := OriginalRecord (7 * Q) (by omega) w
      let issued := if q = none then [] else scriptArchive (attainingWords Q) q
      PaidTrace pi (NarrowWindowCost.output (7 * Q) (by omega) w) q [] issued (f q) ∧
      issued.map Prod.fst = (if q = none then [] else attainingWords Q) ∧
      issued.length = (if q = none then 0 else 2 * Q + 2) ∧
      NarrowWindowCost.execute (7 * Q) (by omega) pi (2 * Q + 2) w
        (NarrowWindowCost.output (7 * Q) (by omega) w) [] =
          some (f q, issued.length)

private theorem positive : arena.{u}.Law actual := original_five_label_returning_frontier
private theorem negative : ¬ arena.{u}.Law oracle := by
  intro law
  have bad := (law 2 (by omega) (fun a => (ULift.up a : ULift.{u} (Fin 7)))
    (by intro a b eq; exact congrArg ULift.down eq) (ULift.up 0) false).1
  have good := (original_five_label_returning_frontier 2 (by omega)
    (fun a => (ULift.up a : ULift.{u} (Fin 7)))
    (by intro a b eq; exact congrArg ULift.down eq) (ULift.up 0) false).1
  rw [good] at bad
  norm_num [oracle, realize, signature] at bad

def evidence : Registration arena.{u}
    (type_of% (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FiveLabelReturningFrontier.original_five_label_returning_frontier.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positive, oracle, negative⟩
  sensitivity := ⟨fun i => ⟨oracle,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, negative⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    cases i
    exact ⟨2, 0, 1, by decide⟩

noncomputable def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FiveLabelReturningFrontier.original_five_label_returning_frontier.{u})
    (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FiveLabelReturningFrontier.original_five_label_returning_frontier,
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FiveLabelReturningFrontier.evidence,
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
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FiveLabelReturningFrontier,
    definition := none,
    coordinates := #[1],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg"],
      stateBinder := 0,
      functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms evidence
#print axioms registration
end
end Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FiveLabelReturningFrontier
