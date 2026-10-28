import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Coding.PrimitiveLifts.NilpotentRootAmalgamation
import Reg.Support.DependentFamily
import Mathlib.Algebra.Group.ULift

/-! Source-bound audit of the actual power observation in the full group telescope. -/

namespace Reg.D5.S3.ConceptDynamics.Coding.PrimitiveLifts.NilpotentRootAmalgamation

open _root_.D5.S3.ConceptDynamics.Coding.PrimitiveLifts.NilpotentRootAmalgamation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

abbrev signature : Signature where
  Params := Σ G : Type u, Σ _g : Group G, ℕ
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p x => letI := p.2.1; x ^ p.2.2) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ p _ => letI := p.2.1; 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ {G : Type u} [g : Group G] [Group.IsNilpotent G]
    (x y : G) (m n : ℕ), m.Coprime n →
    (r.readout () ⟨G,g,m⟩ x = y ^ n ↔ ∃! z : G, x = z ^ n ∧ y = z ^ m)

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let G := Multiplicative (ULift.{u} ℤ)
  let x : G := Multiplicative.ofAdd ⟨1⟩
  have bad := (@h G _ _ x 1 1 1 (by decide)).mp (by rfl)
  obtain ⟨z, hz, _⟩ := bad
  have eq : x = (1 : G) := by simpa using hz.1.trans hz.2.symm
  have down := congrArg (fun a : G => a.toAdd.down) eq
  norm_num [x] at down

noncomputable def registration : Registration arena.{u}
    (type_of% (@pow_eq_pow_iff_exists_unique.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@pow_eq_pow_iff_exists_unique, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    let G := Multiplicative (ULift.{u} ℤ)
    refine ⟨⟨G,inferInstance,1⟩,1,Multiplicative.ofAdd ⟨1⟩,?_⟩
    intro he
    change (1 : G) ^ 1 = (Multiplicative.ofAdd ⟨1⟩ : G) ^ 1 at he
    simp only [pow_one] at he
    have down := congrArg (fun a : G => a.toAdd.down) he
    exact (show (0 : ℤ) ≠ 1 by decide) down

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@pow_eq_pow_iff_exists_unique.{u})
    (type_of% (realize.{u+1,u,0,u,0} signature.{u}
      (fun _ p x => letI := p.2.1; x ^ p.2.2) (fun e => nomatch e))) (Type (u+1)) Unit where
  unitName :=
    `Reg.D5.S3.ConceptDynamics.Coding.PrimitiveLifts.NilpotentRootAmalgamation.audit
  realizationName := Lean.Name.str
    `Reg.D5.S3.ConceptDynamics.Coding.PrimitiveLifts.NilpotentRootAmalgamation
    "registration"
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨registration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{u+1,u,0,u,0} signature.{u}
    (fun _ p x => letI := p.2.1; x ^ p.2.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (Type u)
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.PrimitiveLifts.NilpotentRootAmalgamation
    definition := none
    coordinates := #[0,1,5]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","fn","arg","fn","arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.ConceptDynamics.Coding.PrimitiveLifts.NilpotentRootAmalgamation
