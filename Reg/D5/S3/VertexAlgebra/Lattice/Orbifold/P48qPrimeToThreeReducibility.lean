import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qPrimeToThreeReducibility
import LeanInformationAuditInterface.Contract.Registration
import Mathlib.Algebra.Group.PUnit
import Mathlib.Algebra.Module.ULift
import Mathlib.Tactic.Linarith
import Reg.Support.SingleDependentReadout

/-! Source-bound audits of the cyclotomic degree and the group order readouts. -/

namespace Reg.D5.S3.VertexAlgebra.Lattice.Orbifold.P48qPrimeToThreeReducibility

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open ExtremalC48 LeanInformationAudit Module

noncomputable section

namespace CyclotomicDegree

universe u

abbrev signature := Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature := realize signature (fun _ _ p => p - 1) (fun e => nomatch e)

private def rejected : Realization signature := realize signature (fun _ _ _ => 2) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {V : Type u} [AddCommGroup V] [Module ℚ V]
    (p : ℕ) [Fact p.Prime] (T : Module.End ℚ V),
    T ^ p = 1 → LinearMap.ker (T - 1) = ⊥ → R.readout () () p ∣ finrank ℚ V

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let V := ULift.{u} ℚ
  let T : Module.End ℚ V := -1
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hperiod : T ^ 2 = 1 := by
    change (-1 : Module.End ℚ V) ^ 2 = 1
    rw [pow_two, neg_mul_neg, one_mul]
  have hker : LinearMap.ker (T - 1) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    apply ULift.ext
    change -x.down - x.down = 0 at hx
    change x.down = 0
    linarith
  have hdim : finrank ℚ V = 1 := by
    let e : V ≃ₗ[ℚ] ℚ := ULift.moduleEquiv
    simpa using e.finrank_eq
  have hd : 2 ∣ finrank ℚ V := h 2 T hperiod hker
  rw [hdim] at hd
  exact (by decide : ¬ (2 : ℕ) ∣ 1) hd

def family : Registration arena.{u} (type_of% @prime_sub_one_dvd_finrank_of_ker_sub_one_eq_bot.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@prime_sub_one_dvd_finrank_of_ker_sub_one_eq_bot.{u}, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro _
    exact ⟨(), 2, 3, by decide⟩

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@prime_sub_one_dvd_finrank_of_ker_sub_one_eq_bot.{u}) (Realization signature) Unit Unit where
  unitName := `ExtremalC48.prime_sub_one_dvd_finrank_of_ker_sub_one_eq_bot.__information_unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.Orbifold.P48qPrimeToThreeReducibility.CyclotomicDegree.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ p => p - 1) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Lattice.Orbifold.P48qPrimeToThreeReducibility
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 3
    }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

end CyclotomicDegree

namespace GroupOrder

universe u

abbrev signature : Signature where
  Params := Unit
  State _ := Type u
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} := realize signature (fun _ _ G => Nat.card G)
  (fun e => nomatch e)

private def rejected : Realization signature.{u} := realize signature (fun _ _ _ => 33)
  (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {G : Type u} [Group G] [Finite G], Nat.card G ∣ 32 * 23 * 47 →
    R.readout () () G ≤ 32 ∨ ∃ x : G, (orderOf x = 23 ∨ orderOf x = 47) ∧
      (Subgroup.zpowers x).Normal

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hd : Nat.card PUnit.{u+1} ∣ 32 * 23 * 47 := by
    rw [Nat.card_unique]
    exact one_dvd _
  rcases h hd with hle | ⟨x, hx, _⟩
  · exact (by decide : ¬ 33 ≤ 32) hle
  · rw [Subsingleton.orderOf_eq] at hx
    exact (by decide : ¬ ((1 : ℕ) = 23 ∨ 1 = 47)) hx

def family : Registration arena.{u} (type_of% @card_le_32_or_exists_normal_zpowers.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@card_le_32_or_exists_normal_zpowers.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro _
    refine ⟨(), ULift.{u} (Fin 1), ULift.{u} (Fin 2), ?_⟩
    change Nat.card (ULift.{u} (Fin 1)) ≠ Nat.card (ULift.{u} (Fin 2))
    simpa only [Nat.card_ulift, Nat.card_fin] using (by decide : (1 : ℕ) ≠ 2)

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@card_le_32_or_exists_normal_zpowers.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `ExtremalC48.card_le_32_or_exists_normal_zpowers.__information_unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.Orbifold.P48qPrimeToThreeReducibility.GroupOrder.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ G => Nat.card G) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Lattice.Orbifold.P48qPrimeToThreeReducibility
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
    }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

end GroupOrder

end
end Reg.D5.S3.VertexAlgebra.Lattice.Orbifold.P48qPrimeToThreeReducibility
