import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.ConstraintRelations.PrimitivePositive
import Mathlib.Data.Fin.VecNotation

/-! # Source-bound observation of primitive-positive definitions -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Combinatorics.ConstraintRelations.PrimitivePositive

open LeanInformationAudit
open _root_.D5.S3.Combinatorics.ConstraintRelations.PrimitivePositive
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

universe u v

abbrev Parameters := Σ D : Type u, Σ S : Type v, Σ arity : S → Nat,
  Σ n : Nat, Σ m : Nat, Σ _relations : (s : S) → (Fin (arity s) → D) → Prop,
    List (Atom arity (n + m))

def signature : Signature where
  Params := Parameters.{u, v}
  State p := Fin p.2.2.2.1 → p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u, v} :=
  realize signature (fun _ p a => Defines p.2.2.2.2.2.1 p.2.2.2.2.2.2 a)
    (fun e => nomatch e)

def rejected : Realization signature.{u, v} :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

def arena : Arena where
  signature := signature.{u, v}
  Law R := ∀ {D : Type u} {S : Type v} {arity : S → Nat} {k n m : Nat}
    (relations : (s : S) → (Fin (arity s) → D) → Prop)
    (operation : (Fin k → D) → D),
    (∀ s, Preserves operation (relations s)) →
    ∀ atoms : List (Atom arity (n + m)),
      Preserves operation (R.readout () ⟨D, S, arity, n, m, relations, atoms⟩)

private theorem rejected_law : ¬ arena.{u, v}.Law rejected := by
  intro h
  let D : Type u := PUnit
  let S : Type v := PEmpty
  have hp := h (D := D) (S := S) (arity := fun _ => 1) (k := 0) (n := 1) (m := 0)
    (fun s => nomatch s) (fun _ => PUnit.unit) (fun s => nomatch s) []
  exact hp (fun j => Fin.elim0 j) (fun j => Fin.elim0 j)

def family : Registration arena.{u, v} (type_of% (@polymorphism_preserves_pp.{u, v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@polymorphism_preserves_pp, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨ULift.{u} Bool, ULift.{v} Unit, (fun _ => 1), 1, 0,
      (fun _ a => a 0 = ⟨true⟩), [⟨⟨()⟩, ![0]⟩]⟩,
      ![⟨true⟩], ![⟨false⟩], ?_⟩
    intro h
    dsimp [actual, realize] at h
    have htrue : Defines (fun _ : ULift.{v} Unit => fun a : Fin 1 → ULift.{u} Bool =>
        a 0 = ⟨true⟩) [⟨⟨()⟩, ![0]⟩] ![⟨true⟩] :=
      ⟨Fin.elim0, rfl, trivial⟩
    have hfalse := Eq.mp h htrue
    obtain ⟨w, hw, _⟩ := hfalse
    exact Bool.noConfusion (congrArg ULift.down hw)

noncomputable def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@polymorphism_preserves_pp.{u, v}) (Realization signature.{u, v}) Type Unit where
  unitName := `D5.S3.Combinatorics.ConstraintRelations.PrimitivePositive.polymorphism_preserves_pp.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.ConstraintRelations.PrimitivePositive.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p a => Defines p.2.2.2.2.2.1 p.2.2.2.2.2.2 a) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.ConstraintRelations.PrimitivePositive
    definition := none
    coordinates := #[0, 1, 2, 4, 5, 6, 9]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.ConstraintRelations.PrimitivePositive
