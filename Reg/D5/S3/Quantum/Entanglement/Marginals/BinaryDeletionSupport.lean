import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.Marginals.BinaryDeletionSupport
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Quantum.Entanglement.Marginals.BinaryDeletionSupport

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Entanglement.Marginals.BinaryDeletionSupport

noncomputable section
universe u

private abbrev signature : Signature where
  Params := Σ V : Type u, Σ _ : V → Bool, V → Bool
  State p := Matrix (p.1 → Bool) (p.1 → Bool) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization signature.{u} :=
  realize signature (fun _ p R => R p.2.1 p.2.2) (fun a => nomatch a)

private def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) (fun a => nomatch a)

private abbrev arena : Arena where
  signature := signature.{u}
  Law F := ∀ {V : Type u} [DecidableEq V] [Finite V]
    (Allowed : (V → Bool) → Prop) (x y : V → Bool),
    (∃ R : Matrix (V → Bool) (V → Bool) ℂ, InDeletionKernel R ∧
      F.readout () ⟨V, x, y⟩ R ≠ 0 ∧ ∀ u v, R u v ≠ 0 → Allowed u ∧ Allowed v) ↔
    ∀ u v, SamePattern x y u v → Allowed u ∧ Allowed v

private theorem rejected_law : ¬ arena.{u}.Law rejected.{u} := by
  intro h
  let x : ULift.{u} Unit → Bool := fun _ => false
  obtain ⟨_, _, hzero, _⟩ := (h (fun _ => True) x x).2
    (fun _ _ _ => ⟨True.intro, True.intro⟩)
  exact hzero rfl

def family : Registration arena.{u} (type_of% @survives_iff.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@survives_iff.{u}, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun a => nomatch a⟩
  dependence := by
    intro i
    let p : signature.Params := ⟨ULift.{u} Unit, (fun _ => false), fun _ => false⟩
    exact ⟨p, (fun _ _ => 0), (fun _ _ => 1), zero_ne_one⟩

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@survives_iff.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `D5.S3.Quantum.Entanglement.Marginals.BinaryDeletionSupport.survives_iff.audit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.Marginals.BinaryDeletionSupport.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p R => R p.2.1 p.2.2) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.Marginals.BinaryDeletionSupport
    definition := none
    coordinates := #[0, 4, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "arg", "body",
        "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "fn"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Quantum.Entanglement.Marginals.BinaryDeletionSupport
