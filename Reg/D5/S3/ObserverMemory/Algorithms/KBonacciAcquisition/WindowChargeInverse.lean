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

end
end Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.WindowChargeInverse
