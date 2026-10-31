import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.CoherentHistorySchmidt
import Reg.Support.DependentFamily

/-! Source-bound audit of the occupation of a legal word's prefix. -/

set_option linter.style.longLine false

set_option pp.proofs false in
#print D5.S3.Quantum.Entanglement.CoherentHistorySchmidt.legal_iff

namespace Reg.D5.S3.Quantum.Entanglement.CoherentHistorySchmidt

open _root_.D5.S3.Quantum.Entanglement.CoherentHistorySchmidt
open _root_.D5.S3.Quantum.Entanglement.OccupancyWordSectors
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Retain the alphabet and prefix length as parameters. -/
abbrev signature.{u} : Signature where
  Params := Σ α : Type u, ℕ
  State p := Word p.1 p.2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Multiset p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual.{u} : Realization signature.{u} :=
  realize signature (fun _ _ w => occupation w) (fun e => nomatch e)

def rejected.{u} : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Retain the complete legal-word equivalence and every boundary condition. -/
abbrev arena.{u} : Arena where
  signature := signature.{u}
  Law R := ∀ {α : Type u} [DecidableEq α] {a : Multiset α} {t s : ℕ}
    (w : Word α t) (v : Word α s),
    occupation (Fin.append w v) = a ↔
      ∃ b : Boundary a t, R.readout () ⟨α, t⟩ w = b.val ∧ occupation v = a - b.val

private theorem rejected_law.{u} : ¬ arena.{u}.Law rejected := by
  intro h
  let w : Word (ULift.{u} Unit) 1 := fun _ => ⟨()⟩
  let v : Word (ULift.{u} Unit) 0 := fun i => Fin.elim0 i
  obtain ⟨b, hb, _⟩ :=
    (@h (ULift.{u} Unit) inferInstance (occupation (Fin.append w v)) 1 0 w v).mp rfl
  change (0 : Multiset (ULift.{u} Unit)) = b.val at hb
  have hc := (boundary_spec (occupation (Fin.append w v)) 1 b).2
  rw [← hb] at hc
  norm_num at hc

private theorem dependence.{u} : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨⟨ULift.{u} Bool, 1⟩, (fun _ => ⟨false⟩), (fun _ => ⟨true⟩), ?_⟩
  change occupation (fun _ : Fin 1 => (⟨false⟩ : ULift.{u} Bool)) ≠
    occupation (fun _ : Fin 1 => (⟨true⟩ : ULift.{u} Bool))
  simp [occupation]

def source_registration.{u} : Registration arena
    (type_of% (@_root_.D5.S3.Quantum.Entanglement.CoherentHistorySchmidt.legal_iff.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Entanglement.CoherentHistorySchmidt.legal_iff.{u},
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration.{u} :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Entanglement.CoherentHistorySchmidt.legal_iff.{u})
      (Realization signature.{u}) Unit Unit where
  unitName := `D5.S3.Quantum.Entanglement.CoherentHistorySchmidt.legal_iff.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.CoherentHistorySchmidt.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ _ w => occupation w) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.CoherentHistorySchmidt
    definition := none
    coordinates := #[0, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "arg", "arg", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Entanglement.CoherentHistorySchmidt
