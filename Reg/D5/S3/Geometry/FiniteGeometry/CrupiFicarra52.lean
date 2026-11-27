import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Geometry.FiniteGeometry.CrupiFicarra52
import Reg.Support.DependentFamily
import Mathlib.Algebra.Field.ULift

/-! Source-bound audit of the cardinality of a candidate blocking set. -/

namespace Reg.D5.S3.Geometry.FiniteGeometry.CrupiFicarra52

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.FiniteGeometry.CrupiFicarra52
open scoped LinearAlgebra.Projectivization

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

abbrev signature : Signature where
  Params := Σ F : Type u, Field F
  State p :=
    letI : Field p.1 := p.2
    Finset (ℙ p.1 (Fin 3 → p.1))
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ B => B.card) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ {F : Type u} [field : Field F] [Fintype F], 5 ≤ Fintype.card F →
    IsGreatest {n : ℕ | ∃ B : Finset (ℙ F (Fin 3 → F)),
      BlockingSet B ∧ RInfinity B ∧ r.readout () ⟨F, field⟩ B = n}
      (Fintype.card F ^ 2 - Fintype.card F + 1) ∧
    3 * (Fintype.card F - 1) < Fintype.card F ^ 2 - Fintype.card F + 1

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hcard : Fintype.card (ULift.{u} (ZMod 5)) = 5 := by
    rw [Fintype.card_ulift, ZMod.card]
  obtain ⟨⟨⟨B, _, _, heq⟩, _⟩, _⟩ :=
    h (F := ULift.{u} (ZMod 5)) (by rw [hcard])
  change 0 = Fintype.card (ULift.{u} (ZMod 5)) ^ 2 -
    Fintype.card (ULift.{u} (ZMod 5)) + 1 at heq
  rw [hcard] at heq
  omega

def evidence : Registration arena.{u} (type_of% @result.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := by
    rintro ⟨⟩
    let : Fact (Nat.Prime 5) := ⟨by decide⟩
    let p : signature.{u}.Params := ⟨ULift.{u} (ZMod 5), inferInstance⟩
    let : Field p.1 := p.2
    let x : ℙ p.1 (Fin 3 → p.1) := Projectivization.mk p.1 ![0, 0, 1] (by
      intro h
      have hz := congrFun h (2 : Fin 3)
      simp at hz)
    exact ⟨p, ∅, {x}, by simp [actual, realize]⟩

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@result.{u}) (Realization signature.{u}) Unit Unit := {
  unitName := `D5.S3.Geometry.FiniteGeometry.CrupiFicarra52.result.__information_unit
  realizationName := `Reg.D5.S3.Geometry.FiniteGeometry.CrupiFicarra52.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ B => B.card) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.FiniteGeometry.CrupiFicarra52
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn", "arg", "arg", "body",
        "arg", "body", "arg", "arg", "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.Geometry.FiniteGeometry.CrupiFicarra52
