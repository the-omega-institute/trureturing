import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.WindowChargeInverse
import Reg.Support.DependentFamily

open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.WindowChargeInverse
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.WindowChargeInverse

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- The parameters retain both widths, the scalar and the modular phase. -/
@[reducible] def archiveSignature : Signature where
  Params := Σ k : ℕ, ℕ × ZMod 2 × ZMod (k + 1)
  State _ := List (ℕ → ZMod 2)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def archiveActual : Realization archiveSignature :=
  realize archiveSignature
    (fun _ p rows => (chargeArchive p.1 p.2.1 rows p.2.2.1 p.2.2.2).length)
    (fun e => nomatch e)

def archiveRejected : Realization archiveSignature :=
  realize archiveSignature (fun _ _ rows => rows.length + 1) (fun e => nomatch e)

/-- Only the archive-length occurrence varies; the complete conjunction remains. -/
@[reducible] def archiveArena : Arena where
  signature := archiveSignature
  Law R := ∀ (k m : ℕ) (rows : List (ℕ → ZMod 2))
    (v : ZMod 2) (j : ZMod (k + 1)),
    R.readout () ⟨k, m, v, j⟩ rows = rows.length ∧
    none ∉ chargeArchive k m rows v j

private theorem archivePositive : archiveArena.Law archiveActual := by
  intro k m rows v j
  exact charge_archive_live k m rows v j

private theorem archiveNegative : ¬ archiveArena.Law archiveRejected := by
  intro law
  have impossible := (law 3 1 [] 0 0).1
  cases impossible

def archiveEvidence : Registration archiveArena
    (type_of% (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.WindowChargeInverse.charge_archive_live)) where
  actual := archiveActual
  bridge := Iff.rfl
  variation := ⟨archivePositive, archiveRejected, archiveNegative⟩
  sensitivity := ⟨fun i => ⟨archiveRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, archiveNegative⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨⟨3, 1, 0, 0⟩, [], [fun _ => 0], ?_⟩
    simp [archiveActual, realize, chargeArchive]

noncomputable def archiveRegistration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.WindowChargeInverse.charge_archive_live)
    (type_of% (realize archiveSignature archiveActual.readout archiveActual.anchor)) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str
    `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.WindowChargeInverse.charge_archive_live
    "Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.WindowChargeInverse/\
    Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.WindowChargeInverse.archiveArena/[anonymous]")
    "__information_unit",
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.WindowChargeInverse.archiveEvidence,
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
    owner := `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.WindowChargeInverse,
    definition := none,
    coordinates := #[0, 1, 3, 4],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "fn", "arg"],
      stateBinder := 2, functionOperand := false, stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms archiveEvidence
#print axioms archiveRegistration

open _root_.D5.S0.Tower.DBonacci.Names
open _root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.LiteralModel

/-- Widths and phase are fixed while the original word operand varies. -/
@[reducible] def incrementSignature : Signature where
  Params := Σ k : ℕ, Σ _m : ℕ, ZMod (k + 1)
  State p := Fin p.2.1 → Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ZMod 2
  Anchor := Empty
  finiteAnchor := inferInstance

def incrementActual : Realization incrementSignature :=
  realize incrementSignature (fun _ p w => wordIncrement p.1 (-p.2.2) w)
    (fun e => nomatch e)

def incrementRejected : Realization incrementSignature :=
  realize incrementSignature (fun _ _ _ => 0) (fun e => nomatch e)

@[reducible] def incrementArena : Arena where
  signature := incrementSignature
  Law R := ∀ (k : ℕ) (hk : 3 ≤ k) (m : ℕ) (hshort : m < k)
    (w : Fin m → Bool) (j : ZMod (k + 1)),
    R.readout () ⟨k, m, j⟩ w = extendedBit w j.val +
      (if j.val = 0 then 0 else extendedBit w (j.val - 1))

private theorem incrementPositive : incrementArena.Law incrementActual := by
  intro k hk m hshort w j
  exact increment_derivative k hk m hshort w j

private theorem incrementNegative : ¬ incrementArena.Law incrementRejected := by
  intro law
  have impossible := law 3 (by decide) 1 (by decide) (fun _ => true) 0
  norm_num [incrementRejected, realize, extendedBit, bitScalar] at impossible

def incrementEvidence : Registration incrementArena
    (type_of% (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.WindowChargeInverse.increment_derivative)) where
  actual := incrementActual
  bridge := Iff.rfl
  variation := ⟨incrementPositive, incrementRejected, incrementNegative⟩
  sensitivity := ⟨fun i => ⟨incrementRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, incrementNegative⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨⟨3, 1, 0⟩, (fun _ => false), (fun _ => true), ?_⟩
    change wordIncrement 3 (-0) (fun _ : Fin 1 => false) ≠
      wordIncrement 3 (-0) (fun _ : Fin 1 => true)
    rw [increment_derivative 3 (by decide) 1 (by decide),
      increment_derivative 3 (by decide) 1 (by decide)]
    norm_num [extendedBit, bitScalar]

noncomputable def incrementRegistration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.WindowChargeInverse.increment_derivative)
    (type_of% (realize incrementSignature incrementActual.readout incrementActual.anchor)) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str
    `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.WindowChargeInverse.increment_derivative
    "Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.WindowChargeInverse/\
    Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.WindowChargeInverse.incrementArena/[anonymous]")
    "__information_unit",
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.WindowChargeInverse.incrementEvidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨incrementArena⟩,
  objectArena := .source ⟨incrementArena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source incrementArena ⟨incrementEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize incrementSignature incrementActual.readout incrementActual.anchor),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.WindowChargeInverse,
    definition := none,
    coordinates := #[0, 2, 5],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"],
      stateBinder := 0, functionOperand := false, stateOperand := some #["arg"],
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

/-- The original legality predicate is observed without restricting its state family. -/
@[reducible] def legalSignature : Signature where
  Params := Σ _k : ℕ, ℕ
  State p := Fin p.2 → Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def legalActual : Realization legalSignature :=
  realize legalSignature (fun _ p w => decide (DBonacciAdmissible p.1 p.2 w))
    (fun e => nomatch e)

def legalRejected : Realization legalSignature :=
  realize legalSignature (fun _ _ _ => false) (fun e => nomatch e)

@[reducible] def legalArena : Arena where
  signature := legalSignature
  Law R := ∀ (k m : ℕ) (hk : 2 ≤ k) (hshort : m < k) (w : Fin m → Bool),
    R.readout () ⟨k, m⟩ w = true

private theorem legalPositive : legalArena.Law legalActual := by
  intro k m hk hshort w
  simpa [legalActual, realize] using short_legal k m hk hshort w

private theorem legalNegative : ¬ legalArena.Law legalRejected := by
  intro law
  have impossible := law 2 1 (by decide) (by decide) (fun _ => false)
  cases impossible

def legalEvidence : Registration legalArena
    (type_of% (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.WindowChargeInverse.short_legal)) where
  actual := legalActual
  bridge := by simp [legalArena, legalActual, realize]
  variation := ⟨legalPositive, legalRejected, legalNegative⟩
  sensitivity := ⟨fun i => ⟨legalRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, legalNegative⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨⟨2, 2⟩, (fun _ => false), (fun _ => true), ?_⟩
    norm_num [legalActual, realize, DBonacciAdmissible, runAdmissible, Fin.tail]
    change (true : Bool) ≠ false
    decide

noncomputable def legalRegistration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.WindowChargeInverse.short_legal)
    (type_of% (realize legalSignature legalActual.readout legalActual.anchor)) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str
    `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.WindowChargeInverse.short_legal
    "Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.WindowChargeInverse/\
    Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.WindowChargeInverse.legalArena/[anonymous]")
    "__information_unit",
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.WindowChargeInverse.legalEvidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨legalArena⟩,
  objectArena := .source ⟨legalArena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source legalArena ⟨legalEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize legalSignature legalActual.readout legalActual.anchor),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.WindowChargeInverse,
    definition := none,
    coordinates := #[0, 1],
    readouts := #[{
      path := #["body", "body", "body", "body", "body"],
      stateBinder := 0, functionOperand := false, stateOperand := some #["arg"],
      booleanPredicate := true }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

/-- A fixed word is executed from varying actual live records. -/
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
  realize executionSignature (fun _ p q => runBits p.1 p.2.2 q)
    (fun e => nomatch e)

def executionRejected : Realization executionSignature :=
  realize executionSignature (fun _ _ _ => none) (fun e => nomatch e)

@[reducible] def executionArena : Arena where
  signature := executionSignature
  Law R := ∀ (k : ℕ) (hk : 2 ≤ k) (m : ℕ) (hm : 1 ≤ m) (hshort : m < k)
    (w : Fin m → Bool) (v : ZMod 2) (phase : ZMod (k + 1)) (s : ℕ) (hs : s < k)
    (incoming : s = 0 ∨ w ⟨0, by omega⟩ = false),
    R.readout () ⟨k, m, w⟩ (some ⟨v, phase, s⟩) =
      some ⟨v + wordIncrement k phase w, phase + (m : ℕ), tailAfter 0 w⟩ ∧
    tailAfter 0 w < k

private theorem executionPositive : executionArena.Law executionActual := by
  intro k hk m hm hshort w v phase s hs incoming
  exact short_safe_execution k hk m hm hshort w v phase s hs incoming

private theorem executionNegative : ¬ executionArena.Law executionRejected := by
  intro law
  have impossible := (law 2 (by decide) 1 (by decide) (by decide)
    (fun _ => false) 0 0 0 (by decide) (Or.inl rfl)).1
  cases impossible

def executionEvidence : Registration executionArena
    (type_of% (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.WindowChargeInverse.short_safe_execution)) where
  actual := executionActual
  bridge := Iff.rfl
  variation := ⟨executionPositive, executionRejected, executionNegative⟩
  sensitivity := ⟨fun i => ⟨executionRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, executionNegative⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨⟨2, 1, (fun _ => false)⟩,
      some ⟨0, 0, 0⟩, some ⟨1, 0, 0⟩, ?_⟩
    change runBits 2 (fun _ : Fin 1 => false) (some ⟨0, 0, 0⟩) ≠
      runBits 2 (fun _ : Fin 1 => false) (some ⟨1, 0, 0⟩)
    rw [(short_safe_execution 2 (by decide) 1 (by decide) (by decide)
        (fun _ => false) 0 0 0 (by decide) (Or.inl rfl)).1,
      (short_safe_execution 2 (by decide) 1 (by decide) (by decide)
        (fun _ => false) 1 0 0 (by decide) (Or.inl rfl)).1]
    intro same
    have values := congrArg (fun q : Option (LiveRecord 2) => q.map LiveRecord.value) same
    norm_num [wordIncrement] at values

noncomputable def executionRegistration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.WindowChargeInverse.short_safe_execution)
    (type_of% (realize executionSignature executionActual.readout executionActual.anchor)) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str
    `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.WindowChargeInverse.short_safe_execution
    "Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.WindowChargeInverse/\
    Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.WindowChargeInverse.executionArena/[anonymous]")
    "__information_unit",
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.WindowChargeInverse.executionEvidence,
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
    owner := `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.WindowChargeInverse,
    definition := none,
    coordinates := #[0, 2, 5],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg"],
      stateBinder := 0, functionOperand := false, stateOperand := some #["arg"],
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms incrementEvidence
#print axioms incrementRegistration
#print axioms legalEvidence
#print axioms legalRegistration
#print axioms executionEvidence
#print axioms executionRegistration

end
end Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.WindowChargeInverse
