import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Transportation.SupportedBooleanCycleEquivalence
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Combinatorics.Transportation.SupportedBooleanCycleEquivalence

open _root_.D5.S3.Combinatorics.Transportation.SupportedBooleanCycles
open _root_.D5.S3.Combinatorics.Transportation.SupportedBooleanCycleEquivalence
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

set_option autoImplicit false
universe u v
noncomputable section

abbrev signature : Signature where
  Params := Σ _R : Type u, Type v
  State p := Table p.1 p.2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Table p.1 p.2
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u,v} :=
  realize.{max (u + 1) (v + 1), max u v, 0, max u v, 0}
    signature (fun _ _ A => A) (fun e => Empty.elim e)

def rejected : Realization signature.{u,v} :=
  realize.{max (u + 1) (v + 1), max u v, 0, max u v, 0}
    signature (fun _ _ _ => fun _ _ => false) (fun e => Empty.elim e)

/-- Only the first table operand of the final SameMargins occurrence is observed. -/
abbrev arena : Arena where
  signature := signature.{u,v}
  Law Z := ∀ {R : Type u} {C : Type v} [fr : Fintype R] [fc : Fintype C]
    (E : R → C → Prop) (A B : Table R C),
    (∃ n : ℕ, Chain E B A n ∧ n ≤ distance A B / 4) ↔
      (Supported E A ∧ Supported E B ∧
        SameMargins (Z.readout () ⟨R, C⟩ A) B)

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  let P : Table (ULift.{u} Unit) (ULift.{v} Unit) := fun _ _ => true
  have hs : Supported (fun (_ : ULift.{u} Unit) (_ : ULift.{v} Unit) => True) P := by
    intro a b hab
    trivial
  have hc : ∃ n : ℕ,
      Chain (fun (_ : ULift.{u} Unit) (_ : ULift.{v} Unit) => True) P P n ∧
        n ≤ distance P P / 4 := ⟨0, Chain.done hs, Nat.zero_le _⟩
  have hm := ((h (fun (_ : ULift.{u} Unit) (_ : ULift.{v} Unit) => True) P P).mp hc).2.2
  have hx := hm.1 ⟨()⟩
  simp [rejected, realize, P,
    _root_.D5.S3.Combinatorics.Transportation.SupportedCycleSupplier.rowSum] at hx

def registration : Registration arena.{u,v}
    (type_of% (@bounded_conformal_chain_iff.{u,v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@bounded_conformal_chain_iff.{u,v}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨ULift.{u} Unit, ULift.{v} Unit⟩,
      (fun _ _ => false), (fun _ _ => true), ?_⟩
    intro h
    have hx := congrFun (congrFun h ⟨()⟩) ⟨()⟩
    exact Bool.false_ne_true hx

def registration_contract : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@bounded_conformal_chain_iff.{u,v})
    (type_of% (realize.{max (u + 1) (v + 1), max u v, 0, max u v, 0}
      signature.{u,v} (fun _ _ A => A) (fun e => Empty.elim e)))
    Unit Unit := {
  unitName :=
    `D5.S3.Combinatorics.Transportation.SupportedBooleanCycleEquivalence.bounded_conformal_chain_iff.__information_unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.Transportation.SupportedBooleanCycleEquivalence.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v}⟩
  objectArena := .source ⟨arena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v} ⟨registration.{u,v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{max (u + 1) (v + 1), max u v, 0, max u v, 0}
    signature.{u,v} (fun _ _ A => A) (fun e => Empty.elim e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    definition := none
    owner := `D5.S3.Combinatorics.Transportation.SupportedBooleanCycleEquivalence
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "arg", "arg", "arg", "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Combinatorics.Transportation.SupportedBooleanCycleEquivalence
