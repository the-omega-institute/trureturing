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


namespace NativeFiberAudit
noncomputable section
universe u
open OriginalExecutionBridge
open D5.S3.ObserverMemory.Algorithms.KBonacciIrreversibleAcquisition
open D5.S0.Tower.DBonacci.Names
@[reducible] def signature : Signature where
  Params := Σ Y : Type u, Σ k : ℕ, Σ _m : ℕ,
    ZMod 2 × ℕ × ZMod (k + 1) × ℕ
  State p := NarrowWindowCost.Selector p.2.2.1 p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Option (p.1 × ℕ)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} := realize signature
  (fun _ ⟨_Y, k, _m, v, d, phase, s⟩ pi =>
    NativeExecute pi d (some (LiveRecord.mk (k := k) v phase s)) (some v) [])
  (fun e => nomatch e)
def oracle : Realization signature.{u} := realize signature
  (fun _ _ _ => none) (fun e => nomatch e)
@[reducible] def arena : Arena where
  signature := signature.{u}
  Law R := ∀ {Y : Type u} (k m : ℕ) (hk : 2 ≤ k) (hm : 1 ≤ m)
    (alphabet : Bool) (f : Option (LiveRecord k) → Y) (v : ZMod 2) (d : ℕ)
    (pi : NarrowWindowCost.Selector m Y)
    (correct : ∀ history : List (AllowedBlock k m alphabet),
      let w := history.flatMap (fun a => List.ofFn a.val)
      NarrowWindowCost.output k (by omega) w = some v →
      ∃ c ≤ d, NarrowWindowCost.execute k (by omega) pi d w (some v) [] =
        some (f (OriginalRecord k (by omega) w), c))
    (phase : ZMod (k + 1)) (s : ℕ) (hs : s < k)
    (actual : Nat.gcd m (k + 1) ∣ phase.val),
    ∃ c ≤ d, R.readout () ⟨Y, k, m, v, d, phase, s⟩ pi =
      some (f (some ⟨v, phase, s⟩), c)
private theorem positive : arena.{u}.Law actual := native_fiber
private theorem negative : ¬ arena.{u}.Law oracle := by
  intro law
  have bad := law 2 1 (by omega) (by omega) false
    (fun _ => (ULift.up false : ULift.{u} Bool)) 0 0 (fun _ _ => .inl ⟨false⟩)
    (by intro history; dsimp only; intro _; exact ⟨0, by omega, rfl⟩)
    0 0 (by omega) (by norm_num)
  obtain ⟨c, _, impossible⟩ := bad
  cases impossible

def evidence : Registration arena.{u} (type_of% (@native_fiber.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positive, oracle, negative⟩
  sensitivity := ⟨fun i => ⟨oracle, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, negative⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨⟨ULift.{u} Bool, 2, 1, 0, 0, 0, 0⟩,
      (fun _ _ => .inl ⟨false⟩), (fun _ _ => .inl ⟨true⟩), ?_⟩
    intro impossible
    have eq := congrArg (fun r : Option (ULift.{u} Bool × ℕ) => r.map (fun p => p.1.down)) impossible
    cases eq

noncomputable def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OwnPathCharges.native_fiber.{u})
    (type_of% (realize signature.{u} actual.{u}.readout actual.{u}.anchor)) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OwnPathCharges.native_fiber
    "Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OwnPathCharges.NativeFiberAudit/Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OwnPathCharges.NativeFiberAudit.arena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OwnPathCharges.NativeFiberAudit.evidence,
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
    coordinates := #[0, 1, 2, 7, 8, 11, 12],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "fn", "arg"],
      stateBinder := 0,
      functionOperand := false, stateOperand := some #["fn", "fn", "fn", "fn", "arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms evidence
#print axioms registration
end
end NativeFiberAudit
#print axioms _root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OwnPathCharges.native_fiber

end Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OwnPathCharges
