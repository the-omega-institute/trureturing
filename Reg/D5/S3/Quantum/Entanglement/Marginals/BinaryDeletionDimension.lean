import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.Marginals.BinaryDeletionDimension
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Quantum.Entanglement.Marginals.BinaryDeletionDimension

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Entanglement.Marginals.BinaryDeletionDimension

noncomputable section
universe u

private abbrev dimensionSignature : Signature where
  Params := Σ V : Type u, (V → Bool) → Prop
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

private def dimensionActual : Realization dimensionSignature.{u} :=
  realize dimensionSignature (fun _ _ x y => x = y) (fun anchor => nomatch anchor)

private def dimensionRejected : Realization dimensionSignature.{u} :=
  realize dimensionSignature (fun _ _ _ _ => False) (fun anchor => nomatch anchor)

private abbrev dimensionArena : Arena where
  signature := dimensionSignature.{u}
  Law F := ∀ {V : Type u} [DecidableEq V] [Finite V] (Allowed : (V → Bool) → Prop),
    F.readout () ⟨V, Allowed⟩ (Module.finrank ℂ (SupportedKernel Allowed))
      (Nat.card {p // AllowedPattern Allowed p})

private theorem dimensionRejected_law : ¬ dimensionArena.{u}.Law dimensionRejected.{u} := by
  intro h
  exact h (V := ULift.{u} Unit) (fun _ => True)

def dimensionFamily : Registration dimensionArena.{u} (type_of% @supportedKernel_finrank.{u}) where
  actual := dimensionActual
  bridge := Iff.rfl
  variation := ⟨@supportedKernel_finrank.{u}, dimensionRejected, dimensionRejected_law⟩
  sensitivity := ⟨fun i => ⟨dimensionRejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, dimensionRejected_law⟩, fun anchor => nomatch anchor⟩
  dependence := by
    intro i
    let p : dimensionSignature.Params := ⟨ULift.{u} Unit, fun _ => True⟩
    refine ⟨p, 0, 1, ?_⟩
    intro h
    exact Nat.one_ne_zero (Eq.mp (congrFun h 0) rfl)

def dimensionAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@supportedKernel_finrank.{u}) (Realization dimensionSignature.{u}) Unit Unit where
  unitName := `D5.S3.Quantum.Entanglement.Marginals.BinaryDeletionDimension.supportedKernel_finrank.audit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.Marginals.BinaryDeletionDimension.dimensionFamily
  realizationSource := none
  generated := false
  arena := .source ⟨dimensionArena.{u}⟩
  objectArena := .source ⟨dimensionArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source dimensionArena.{u} ⟨dimensionFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize dimensionSignature (fun _ _ x y => x = y) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.Marginals.BinaryDeletionDimension
    definition := none
    coordinates := #[0, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

private abbrev recurrenceSignature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

private def recurrenceActual : Realization recurrenceSignature :=
  realize recurrenceSignature (fun _ _ x y => x = y) (fun anchor => nomatch anchor)

private def recurrenceRejected : Realization recurrenceSignature :=
  realize recurrenceSignature (fun _ _ _ _ => False) (fun anchor => nomatch anchor)

private abbrev dim (k : ℕ) : ℕ := Module.finrank ℂ (SupportedKernel (NoTriple k))

private abbrev recurrenceArena : Arena where
  signature := recurrenceSignature
  Law F := ∀ k : ℕ, dim 1 = 12 ∧ dim 2 = 24 ∧ dim 3 = 44 ∧
    F.readout () k (dim (k + 4)) (dim (k + 3) + dim (k + 2) + dim (k + 1))

private theorem recurrenceRejected_law : ¬ recurrenceArena.Law recurrenceRejected :=
  fun h => (h 0).2.2.2

def recurrenceFamily : Registration recurrenceArena (type_of% @noTriple_finrank) where
  actual := recurrenceActual
  bridge := Iff.rfl
  variation := ⟨@noTriple_finrank, recurrenceRejected, recurrenceRejected_law⟩
  sensitivity := ⟨fun i => ⟨recurrenceRejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, recurrenceRejected_law⟩, fun anchor => nomatch anchor⟩
  dependence := by
    intro i
    refine ⟨0, 0, 1, ?_⟩
    intro h
    exact Nat.one_ne_zero (Eq.mp (congrFun h 0) rfl)

def recurrenceAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@noTriple_finrank) (Realization recurrenceSignature) Unit Unit where
  unitName := `D5.S3.Quantum.Entanglement.Marginals.BinaryDeletionDimension.noTriple_finrank.audit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.Marginals.BinaryDeletionDimension.recurrenceFamily
  realizationSource := none
  generated := false
  arena := .source ⟨recurrenceArena⟩
  objectArena := .source ⟨recurrenceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source recurrenceArena ⟨recurrenceFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize recurrenceSignature (fun _ _ x y => x = y) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.Marginals.BinaryDeletionDimension
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "arg", "arg", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Quantum.Entanglement.Marginals.BinaryDeletionDimension
