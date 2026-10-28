import D5.S3.ConceptDynamics.Coding.PrimitiveLifts.FiniteNilpotentAmalgamation
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration
import Mathlib.Algebra.Group.ULift

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.ConceptDynamics.Coding.PrimitiveLifts.FiniteNilpotentAmalgamation

namespace Reg.D5.S3.ConceptDynamics.Coding.PrimitiveLifts.FiniteNilpotentAmalgamation

universe u

structure PowerData where
  G : Type u
  groupG : Group G
  exponent : ℕ

abbrev signature : Signature where
  Params := PowerData.{u}
  State p := p.G
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.G
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p x => by
    letI := p.groupG
    exact x ^ p.exponent) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ x => x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {G : Type u} [g : Group G] [Finite G],
    (∀ x y : G, ∀ m n : ℕ, Nat.Coprime m n →
      R.readout () ⟨G,g,m⟩ x = R.readout () ⟨G,g,n⟩ y →
      ∃ z : G, x = R.readout () ⟨G,g,n⟩ z ∧ y = R.readout () ⟨G,g,m⟩ z) →
      Group.IsNilpotent G

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let H := ULift.{u} (Equiv.Perm (Fin 3))
  let a : H := ULift.up (Equiv.swap (0 : Fin 3) 1)
  let b : H := ULift.up (Equiv.swap (0 : Fin 3) 1 * Equiv.swap (1 : Fin 3) 2)
  have hn : Group.IsNilpotent H := h (fun _ y _ _ _ he => ⟨y, he, rfl⟩)
  letI := hn
  have ha : a ^ 2 = 1 := by apply ULift.ext; decide
  have hb : b ^ 3 = 1 := by apply ULift.ext; decide
  have hc : Nat.Coprime (orderOf a) (orderOf b) :=
    (by decide : Nat.Coprime 2 3).of_dvd
      (orderOf_dvd_of_pow_eq_one ha) (orderOf_dvd_of_pow_eq_one hb)
  have he := (Group.IsNilpotent.commute_of_orderOf_coprime hc).eq
  have hne : a * b ≠ b * a := by
    intro heq
    have hz := congrArg (fun f : H => f.down (0 : Fin 3)) heq
    change (0 : Fin 3) = 2 at hz
    exact (by decide : (0 : Fin 3) ≠ 2) hz
  exact hne he

def family : Registration arena.{u} (type_of% @nilpotent_of_coprime_power_amalgamation.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨nilpotent_of_coprime_power_amalgamation, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := by
    intro i
    let H := ULift.{u} (Equiv.Perm (Fin 3))
    refine ⟨⟨H, inferInstance, 1⟩, 1, ULift.up (Equiv.swap (0 : Fin 3) 1), ?_⟩
    intro he
    have hz := congrArg (fun f : H => f.down (0 : Fin 3)) he
    change (0 : Fin 3) = 1 at hz
    exact (by decide : (0 : Fin 3) ≠ 1) hz

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@nilpotent_of_coprime_power_amalgamation.{u})
    (type_of% (realize signature.{u} (fun _ p x => by
      letI := p.groupG
      exact x ^ p.exponent) (fun e => nomatch e)))
    (type_of% (@HPow.hPow.{u,0,u})) Unit where
  unitName := `D5.S3.ConceptDynamics.Coding.PrimitiveLifts.FiniteNilpotentAmalgamation.nilpotent_of_coprime_power_amalgamation.audit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.PrimitiveLifts.FiniteNilpotentAmalgamation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ p x => by
    letI := p.groupG
    exact x ^ p.exponent) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (@HPow.hPow.{u,0,u})
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.PrimitiveLifts.FiniteNilpotentAmalgamation
    definition := none
    coordinates := #[0,1,5,6]
    readouts := #[{
      path := #["body","body","body","type","body","body","body","body","body","type","fn","arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := some #["fn","arg"]
      booleanPredicate := false}, {
      path := #["body","body","body","type","body","body","body","body","body","type","arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := some #["fn","arg"]
      booleanPredicate := false}, {
      path := #["body","body","body","type","body","body","body","body","body","body","arg","body","fn","arg","arg"]
      stateBinder := 9
      functionOperand := false
      stateOperand := some #["fn","arg"]
      booleanPredicate := false}, {
      path := #["body","body","body","type","body","body","body","body","body","body","arg","body","arg","arg"]
      stateBinder := 9
      functionOperand := false
      stateOperand := some #["fn","arg"]
      booleanPredicate := false}]}
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.ConceptDynamics.Coding.PrimitiveLifts.FiniteNilpotentAmalgamation
