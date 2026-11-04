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
abbrev signature.{u_1} : Signature where
  Params := Σ _ : Type u_1, ℕ
  State p := Word p.1 p.2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Multiset p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual.{u_1} : Realization signature.{u_1} :=
  realize signature (fun _ _ w => occupation w) (fun e => nomatch e)

def rejected.{u_1} : Realization signature.{u_1} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Retain the complete legal-word equivalence and every boundary condition. -/
abbrev arena.{u_1} : Arena where
  signature := signature.{u_1}
  Law R := ∀ {α : Type u_1} [DecidableEq α] {a : Multiset α} {t s : ℕ}
    (w : Word α t) (v : Word α s),
    occupation (Fin.append w v) = a ↔
      ∃ b : Boundary a t, R.readout () ⟨α, t⟩ w = b.val ∧ occupation v = a - b.val

private theorem rejected_law.{u_1} : ¬ arena.{u_1}.Law rejected := by
  intro h
  let w : Word (ULift.{u_1} Unit) 1 := fun _ => ⟨()⟩
  let v : Word (ULift.{u_1} Unit) 0 := fun i => Fin.elim0 i
  obtain ⟨b, hb, _⟩ :=
    (@h (ULift.{u_1} Unit) inferInstance (occupation (Fin.append w v)) 1 0 w v).mp rfl
  change (0 : Multiset (ULift.{u_1} Unit)) = b.val at hb
  have hc := (boundary_spec (occupation (Fin.append w v)) 1 b).2
  rw [← hb] at hc
  norm_num at hc

private theorem dependence.{u_1} : ObservationalDependence signature.{u_1} actual := by
  intro i
  refine ⟨⟨ULift.{u_1} Bool, 1⟩, (fun _ => ⟨false⟩), (fun _ => ⟨true⟩), ?_⟩
  change occupation (fun _ : Fin 1 => (⟨false⟩ : ULift.{u_1} Bool)) ≠
    occupation (fun _ : Fin 1 => (⟨true⟩ : ULift.{u_1} Bool))
  simp [occupation]

def source_registration.{u_1} : Registration arena
    (type_of% (@_root_.D5.S3.Quantum.Entanglement.CoherentHistorySchmidt.legal_iff.{u_1})) where
  actual := realize signature.{u_1} (fun _ _ w => occupation w) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Entanglement.CoherentHistorySchmidt.legal_iff.{u_1},
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration.{u_1} :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Entanglement.CoherentHistorySchmidt.legal_iff.{u_1})
      (Realization signature.{u_1}) Unit Unit where
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
  readout := some (realize signature.{u_1} (fun _ _ w => occupation w) (fun e => nomatch e))
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
