import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OwnPathCharges
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition
open LiteralModel EndpointCells OriginalNarrowCost OwnPathCharges
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OwnPathCharges
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

@[reducible] def signature : Signature where
  Params := Σ Y : Type u, Σ m : ℕ, Σ table : ZMod (2 * m - 2 + 1) → Y,
    Σ _π : NarrowWindowCost.Selector m Y, Σ _d : ℕ, ℕ
  State p := ZMod (2 * p.2.1 - 2 + 1)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ZMod 2
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ ⟨_Y, _m, table, π, d, t⟩ j => phaseCharges table π d t j)
  (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ => 1) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ {Y : Type u} (m : ℕ) (hm : 5 ≤ m) (alphabet : Bool)
    (f : Option (LiveRecord (2 * m - 2)) → Y)
    (table : ZMod (2 * m - 2 + 1) → Y)
    (target : ∀ (v : ZMod 2) (j : ZMod (2 * m - 2 + 1)) (s : ℕ),
      s < 2 * m - 2 → f (some ⟨v, -j, s⟩) = table j)
    (π : NarrowWindowCost.Selector m Y) (d : ℕ)
    (correct : ∀ history : List (AllowedBlock (2 * m - 2) m alphabet),
      let w := history.flatMap (fun a => List.ofFn a.val)
      NarrowWindowCost.output (2 * m - 2) (by omega) w = some 0 →
      ∃ c ≤ d, NarrowWindowCost.execute (2 * m - 2) (by omega) π d w (some 0) [] =
        some (f (OriginalRecord (2 * m - 2) (by omega) w), c)),
    (∀ t j, m < (j - ((t * m : ℕ) : ZMod (2 * m - 2 + 1))).val →
      R.readout () ⟨Y, m, table, π, d, t⟩ j = 0) ∧
    phaseCharges table π d 0 0 = 0 ∧
    (∀ j j', (∀ t < d, phaseCharges table π d t j = phaseCharges table π d t j') →
      table j = table j')

private theorem positive : arena.Law actual := original_adaptive_charge_array

private theorem negative : ¬ arena.Law rejected := by
  intro law
  have instanceLaw := law 5 (by decide) false (fun _ => PUnit.unit)
    (fun _ => PUnit.unit) (by intros; rfl) (fun _ _ => .inl PUnit.unit) 0
    (by intro history; dsimp only; intro _; exact ⟨0, le_rfl, rfl⟩)
  have impossible := instanceLaw.1 0 (6 : ZMod 9) (by decide)
  exact one_ne_zero impossible

def evidence : Registration arena
    (type_of% (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OwnPathCharges.original_adaptive_charge_array.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positive, rejected, negative⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, negative⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    let word : Fin 5 → Bool := fun j => decide (j.val = 1)
    let π : NarrowWindowCost.Selector 5 (ULift.{u} (ZMod 2)) := fun free archive =>
      match archive with
      | [] => .inr word
      | (_, reply) :: _ => .inl ⟨reply.getD 0 - free.getD 0⟩
    let labels : ZMod 9 → ULift.{u} (ZMod 2) := fun j => ⟨wordIncrement 8 (-j) word⟩
    have different : labels 0 ≠ labels 1 := by
      decide +kernel
    have distinct : ¬ ∃ y, ∀ j, labels j = y := by
      rintro ⟨y, same⟩
      exact different ((same 0).trans (same 1).symm)
    refine ⟨⟨ULift.{u} (ZMod 2), 5, labels, π, 1, 0⟩, (0 : ZMod 9), 1, ?_⟩
    change phaseCharges labels π 1 0 0 ≠ phaseCharges labels π 1 0 1
    rw [phaseCharges, if_neg distinct, phaseCharges, if_neg distinct]
    change ownCharge π 1 0 0 0 (some 0) [] 0 ≠
      ownCharge π 1 0 (-1) 0 (some 0) [] 0
    decide +kernel

#print axioms evidence

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OwnPathCharges.original_adaptive_charge_array.{u})
    (type_of% (realize signature.{u} actual.{u}.readout actual.{u}.anchor)) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str
    `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OwnPathCharges.original_adaptive_charge_array
    "Reg/D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OwnPathCharges/Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OwnPathCharges.arena/[anonymous]")
    "__information_unit",
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OwnPathCharges.evidence,
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
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OwnPathCharges,
    definition := none,
    coordinates := #[0, 1, 5, 7, 8, 10],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "body", "body", "body", "fn", "arg"],
      stateBinder := 0, functionOperand := false, stateOperand := some #["arg"],
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms registration
end
end Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OwnPathCharges
