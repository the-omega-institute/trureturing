import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.Marginals.BinaryDeletionSignTensor
import Reg.Support.DependentFamily

set_option autoImplicit false

namespace Reg.D5.S3.Quantum.Entanglement.Marginals.BinaryDeletionSignTensor

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Entanglement.Marginals.BinaryDeletionSignTensor

noncomputable section

private abbrev deletionSignature : Signature where
  Params := List Site
  State _ := Int
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Int → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

private def deletionActual : Realization deletionSignature :=
  realize deletionSignature (fun _ _ x y => x = y) (fun anchor => nomatch anchor)

private def deletionRejected : Realization deletionSignature :=
  realize deletionSignature (fun _ _ _ _ => False) (fun anchor => nomatch anchor)

private abbrev deletionArena : Arena where
  signature := deletionSignature
  Law F := ∀ (before after : List Site) (p : Site) (x y u v : List Bool),
    x.length = before.length → y.length = before.length →
    F.readout () before
      (asInt (coefficient (before ++ p :: after) (x ++ false :: u) (y ++ false :: v)) +
        asInt (coefficient (before ++ p :: after) (x ++ true :: u) (y ++ true :: v))) 0

private theorem deletionCounterexample : ¬ deletionArena.Law deletionRejected :=
  fun h => h [] [] .common [] [] [] [] rfl rfl

def deletionFamily : Registration deletionArena (type_of% @deleteSite) where
  actual := deletionActual
  bridge := Iff.rfl
  variation := ⟨@deleteSite, deletionRejected, deletionCounterexample⟩
  sensitivity := ⟨fun i => ⟨deletionRejected, fun j h =>
    (h (Subsingleton.elim j i)).elim, rfl, deletionCounterexample⟩,
    fun anchor => nomatch anchor⟩
  dependence := by
    intro i
    refine ⟨[], 0, 1, ?_⟩
    intro h
    exact Int.one_ne_zero (Eq.mp (congrFun h 0) rfl)

def deletionAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@deleteSite) (Realization deletionSignature) Unit Unit where
  unitName := `D5.S3.Quantum.Entanglement.Marginals.BinaryDeletionSignTensor.deleteSite.audit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.Marginals.BinaryDeletionSignTensor.deletionFamily
  realizationSource := none
  generated := false
  arena := .source ⟨deletionArena⟩
  objectArena := .source ⟨deletionArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source deletionArena ⟨deletionFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize deletionSignature (fun _ _ x y => x = y) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.Marginals.BinaryDeletionSignTensor
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

private abbrev entrySignature : Signature where
  Params := List Site
  State _ := Sign
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Sign → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

private def entryActual : Realization entrySignature :=
  realize entrySignature (fun _ _ x y => x = y) (fun anchor => nomatch anchor)

private def entryRejected : Realization entrySignature :=
  realize entrySignature (fun _ _ _ _ => False) (fun anchor => nomatch anchor)

private abbrev entryArena : Arena where
  signature := entrySignature
  Law F := ∀ pattern : List Site, F.readout () pattern
      (coefficient pattern (pattern.map leftBit) (pattern.map rightBit)) .positive

private theorem entryCounterexample : ¬ entryArena.Law entryRejected :=
  fun h => h []

def entryFamily : Registration entryArena (type_of% @actualEntry) where
  actual := entryActual
  bridge := Iff.rfl
  variation := ⟨@actualEntry, entryRejected, entryCounterexample⟩
  sensitivity := ⟨fun i => ⟨entryRejected, fun j h =>
    (h (Subsingleton.elim j i)).elim, rfl, entryCounterexample⟩,
    fun anchor => nomatch anchor⟩
  dependence := by
    intro i
    refine ⟨[], .positive, .zero, ?_⟩
    intro h
    exact (fun hc : Sign.zero = Sign.positive => Sign.noConfusion hc) (Eq.mp (congrFun h .positive) rfl)

def entryAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actualEntry) (Realization entrySignature) Unit Unit where
  unitName := `D5.S3.Quantum.Entanglement.Marginals.BinaryDeletionSignTensor.actualEntry.audit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.Marginals.BinaryDeletionSignTensor.entryFamily
  realizationSource := none
  generated := false
  arena := .source ⟨entryArena⟩
  objectArena := .source ⟨entryArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source entryArena ⟨entryFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize entrySignature (fun _ _ x y => x = y) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.Marginals.BinaryDeletionSignTensor
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Quantum.Entanglement.Marginals.BinaryDeletionSignTensor
