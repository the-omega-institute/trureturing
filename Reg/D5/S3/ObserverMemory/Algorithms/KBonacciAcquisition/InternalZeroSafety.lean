import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.InternalZeroSafety
import Reg.Support.DependentFamily

open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition
open LiteralModel EndpointCells WindowChargeInverse InternalZeroSafety
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S0.Tower.DBonacci.Names
open scoped BigOperators

namespace Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.InternalZeroSafety

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

@[reducible] def executionSignature : Signature where
  Params := Σ k : ℕ, Σ m : ℕ, Fin m → Bool
  State p := Option (LiveRecord p.1)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Option (LiveRecord p.1)
  Anchor := Empty
  finiteAnchor := inferInstance

def executionActual : Realization executionSignature :=
  realize executionSignature (fun _ p q => runBits p.1 p.2.2 q) (fun e => nomatch e)

def executionRejected : Realization executionSignature :=
  realize executionSignature (fun _ _ _ => none) (fun e => nomatch e)

/-- The original complete telescope and terminal-tail bound remain in the law. -/
@[reducible] def executionArena : Arena where
  signature := executionSignature
  Law R := ∀ (k : ℕ) (hk : 2 ≤ k) (m : ℕ) (hshort : m < k)
    (w : Fin m → Bool) (i : Fin m) (zero : w i = false)
    (v : ZMod 2) (phase : ZMod (k + 1)) (s : ℕ) (hs : s < k)
    (incoming : s + i.val < k ∨ w ⟨0, by have := i.isLt; omega⟩ = false),
    R.readout () ⟨k, m, w⟩ (some ⟨v, phase, s⟩) =
      some ⟨v + wordIncrement k phase w, phase + (m : ℕ), tailAfter 0 w⟩ ∧
    tailAfter 0 w ≤ m - 1 - i.val

private theorem executionPositive : executionArena.Law executionActual :=
  internal_zero_execution

private theorem executionNegative : ¬ executionArena.Law executionRejected := by
  intro law
  have impossible := (law 3 (by decide) 2 (by decide) (fun _ => false)
    ⟨1, by decide⟩ rfl 0 0 0 (by decide) (Or.inl (by decide))).1
  cases impossible

def executionEvidence : Registration executionArena
    (type_of% (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.InternalZeroSafety.internal_zero_execution)) where
  actual := executionActual
  bridge := Iff.rfl
  variation := ⟨executionPositive, executionRejected, executionNegative⟩
  sensitivity := ⟨fun i => ⟨executionRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, executionNegative⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨⟨3, 2, (fun _ => false)⟩, some ⟨0, 0, 0⟩, some ⟨1, 0, 0⟩, ?_⟩
    change runBits 3 (fun _ : Fin 2 => false) (some ⟨0, 0, 0⟩) ≠
      runBits 3 (fun _ : Fin 2 => false) (some ⟨1, 0, 0⟩)
    rw [(internal_zero_execution 3 (by decide) 2 (by decide) (fun _ => false)
        ⟨1, by decide⟩ rfl 0 0 0 (by decide) (Or.inl (by decide))).1,
      (internal_zero_execution 3 (by decide) 2 (by decide) (fun _ => false)
        ⟨1, by decide⟩ rfl 1 0 0 (by decide) (Or.inl (by decide))).1]
    intro same
    have values := congrArg (fun q : Option (LiveRecord 3) => q.map LiveRecord.value) same
    norm_num [wordIncrement] at values

def executionRegistration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.InternalZeroSafety.internal_zero_execution)
    (type_of% (realize executionSignature executionActual.readout executionActual.anchor)) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str
    `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.InternalZeroSafety.internal_zero_execution
    "Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.InternalZeroSafety/\
    Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.InternalZeroSafety.executionArena/[anonymous]")
    "__information_unit",
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.InternalZeroSafety.executionEvidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨executionArena⟩,
  objectArena := .source ⟨executionArena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source executionArena ⟨executionEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize executionSignature executionActual.readout executionActual.anchor),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.InternalZeroSafety,
    definition := none,
    coordinates := #[0, 2, 4],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "fn", "arg", "fn", "arg"],
      stateBinder := 0, functionOperand := false, stateOperand := some #["arg"],
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

@[reducible] def archiveSignature : Signature where
  Params := Σ k : ℕ, Σ _m : ℕ, Σ _alphabet : Bool,
    Σ _v : ZMod 2, Σ _j : ZMod (k + 1), ℕ
  State p := List (AllowedBlock p.1 p.2.1 p.2.2.1)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := List (Option (ZMod 2))
  Anchor := Empty
  finiteAnchor := inferInstance

def archiveActual : Realization archiveSignature :=
  realize archiveSignature (fun _ ⟨_k, _m, _alphabet, v, j, s⟩ actions =>
    fixedBlockArchive actions (some ⟨v, -j, s⟩))
    (fun e => nomatch e)

def archiveRejected : Realization archiveSignature :=
  realize archiveSignature (fun _ _ _ => [none]) (fun e => nomatch e)

/-- Only the native archive equality is intervened upon. All the other
conjuncts, source witnesses, proof premises and the empty-list case remain. -/
@[reducible] def archiveArena : Arena where
  signature := archiveSignature
  Law R := ∀ (k : ℕ) (hk : 3 ≤ k) (m : ℕ)
    (hm : 1 ≤ m) (hshort : m < k) (localAlphabet : Bool)
    (marked : List ((ℕ → ZMod 2) × Fin m))
    (even : ∀ entry ∈ marked, ∑ h ∈ Finset.range (m + 1), entry.1 h = 0)
    (zero : ∀ entry ∈ marked, prefixWord m entry.1 entry.2 = false)
    (seams : marked.IsChain (fun a b => m + b.2.val ≤ k + a.2.val))
    (v : ZMod 2) (j : ZMod (k + 1)) (s : ℕ) (hs : s < k)
    (incoming : ∀ entry ∈ marked.head?, s + entry.2.val < k ∨ entry.1 0 = 0)
    (actualPhase : Nat.gcd m (k + 1) ∣ (-j).val),
    let rows := marked.map Prod.fst
    let actions := chargeBlocks k m (by omega) hshort localAlphabet rows
    actions.length = marked.length ∧
    R.readout () ⟨k, m, localAlphabet, v, j, s⟩ actions =
      chargeArchive k m rows v j ∧
    (fixedBlockArchive actions (some ⟨v, -j, s⟩)).length = marked.length ∧
    none ∉ fixedBlockArchive actions (some ⟨v, -j, s⟩) ∧
    ∃ (N : ℕ) (source : Fin N → Bool),
      m ∣ N ∧ DBonacciAdmissible k N source ∧
      runBits k source (some ⟨0, 0, 0⟩) = some ⟨v, -j, s⟩ ∧
      originalWordValue k source = v ∧ tailAfter 0 source = s ∧
      (∀ (b : ℕ) (hb : (b + 1) * m ≤ N),
        DBonacciAdmissible k m (fun i : Fin m =>
          source ⟨b * m + i.val, by nlinarith [i.isLt]⟩)) ∧
      fixedBlockArchive actions (runBits k source (some ⟨0, 0, 0⟩)) =
        chargeArchive k m rows v j

private theorem archivePositive : archiveArena.Law archiveActual :=
  actual_internal_zero_charge_suffix

private theorem archiveNegative : ¬ archiveArena.Law archiveRejected := by
  intro law
  have impossible := (law 3 (by decide) 2 (by decide) (by decide) false []
    (by simp) (by simp) (by simp) 0 0 0 (by decide) (by simp) (by simp)).2.1
  cases impossible

def archiveEvidence : Registration archiveArena
    (type_of% (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.InternalZeroSafety.actual_internal_zero_charge_suffix)) where
  actual := archiveActual
  bridge := Iff.rfl
  variation := ⟨archivePositive, archiveRejected, archiveNegative⟩
  sensitivity := ⟨fun i => ⟨archiveRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, archiveNegative⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨⟨3, 2, false, 0, 0, 0⟩,
      [], [⟨(fun _ => false), fun _ => by decide⟩], ?_⟩
    change ([] : List (Option (ZMod 2))) ≠ _ :: _
    intro same
    cases same

def archiveRegistration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.InternalZeroSafety.actual_internal_zero_charge_suffix)
    (type_of% (realize archiveSignature archiveActual.readout archiveActual.anchor)) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str
    `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.InternalZeroSafety.actual_internal_zero_charge_suffix
    "Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.InternalZeroSafety/\
    Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.InternalZeroSafety.archiveArena/[anonymous]")
    "__information_unit",
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.InternalZeroSafety.archiveEvidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨archiveArena⟩,
  objectArena := .source ⟨archiveArena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source archiveArena ⟨archiveEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize archiveSignature archiveActual.readout archiveActual.anchor),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.InternalZeroSafety,
    definition := none,
    coordinates := #[0, 2, 5, 10, 11, 12],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "fn", "arg", "fn", "arg"],
      stateBinder := 0, functionOperand := false, stateOperand := some #["fn", "arg"],
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms executionEvidence
#print axioms executionRegistration
#print axioms archiveEvidence
#print axioms archiveRegistration

end
end Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.InternalZeroSafety
