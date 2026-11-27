import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qPrimeToThreeReducibility
import LeanInformationAuditInterface.Contract.Registration
import Mathlib.Algebra.Group.PUnit
import Mathlib.Algebra.Module.ULift
import Mathlib.Tactic.Linarith
import Reg.Support.SingleDependentReadout

/-! Source-bound audits of the degree, group order, and invariant-subspace readouts. -/

namespace Reg.D5.S3.VertexAlgebra.Lattice.Orbifold.P48qPrimeToThreeReducibility

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open ExtremalC48 LeanInformationAudit Module

noncomputable section

namespace CyclotomicDegree

universe u

abbrev signature := Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature := realize signature (fun _ _ p => p - 1) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

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
    simp only [T, LinearMap.sub_apply, LinearMap.neg_apply, Module.End.one_apply] at hx
    have hdown : -x.down - x.down = 0 := congrArg ULift.down hx
    apply ULift.ext
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
    refine ⟨(), 2, 3, ?_⟩
    change (2 : ℕ) - 1 ≠ 3 - 1
    decide

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
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false
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
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false
    }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

end GroupOrder

namespace InvariantSubspace

universe u v

private abbrev Params := Σ V : Type v, Σ addition : AddCommGroup V,
  letI := addition
  Module ℚ V

private abbrev Block (p : Params.{v}) :=
  letI := p.2.1
  letI := p.2.2
  Submodule ℚ p.1

private abbrev Endomorphism (p : Params.{v}) :=
  letI := p.2.1
  letI := p.2.2
  Module.End ℚ p.1

abbrev signature : Signature where
  Params := Params.{v}
  State := Endomorphism
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Block p → Block p
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{v} := realize signature
  (fun _ p T =>
    letI := p.2.1
    letI := p.2.2
    Submodule.comap T) (fun e => nomatch e)

private def rejected : Realization signature.{v} := realize signature
  (fun _ p _ _ =>
    letI := p.2.1
    letI := p.2.2
    ⊥) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature.{v} actual := by
  intro _
  let W : Submodule ℚ (ULift.{v} ℚ) := ⊥
  refine ⟨⟨ULift.{v} ℚ, inferInstance, inferInstance⟩, 0, 1, ?_⟩
  intro heq
  let x : ULift.{v} ℚ := ULift.up 1
  have h := congrFun heq W
  change W.comap (0 : Module.End ℚ (ULift.{v} ℚ)) = W.comap 1 at h
  have hz : x ∈ W.comap (0 : Module.End ℚ (ULift.{v} ℚ)) := by
    rw [Submodule.comap_zero]
    exact Submodule.mem_top
  rw [h] at hz
  have he : x = 0 := by
    rw [Submodule.mem_comap, Module.End.one_apply] at hz
    exact (Submodule.mem_bot ℚ).mp hz
  exact one_ne_zero (congrArg ULift.down he)

private abbrev TestSpace := ULift.{v} (Fin 48 → ℚ)

private theorem test_dim : finrank ℚ TestSpace.{v} = 48 := by
  let e : TestSpace.{v} ≃ₗ[ℚ] (Fin 48 → ℚ) := ULift.moduleEquiv
  rw [e.finrank_eq, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]

namespace OrderDivisor

abbrev arena : Arena where
  signature := signature.{v}
  Law R := ∀ {G : Type u} {V : Type v} [Group G] [AddCommGroup V] [Module ℚ V] [Finite G]
    (ρ : Representation ℚ G V), Function.Injective ρ → finrank ℚ V = 48 →
    Nat.card G ∣ 32 * 23 * 47 → ∃ W : Submodule ℚ V, W ≠ ⊥ ∧ W ≠ ⊤ ∧
      ∀ g, W ≤ R.readout () ⟨V, inferInstance, inferInstance⟩ (ρ g) W

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  let ρ := Representation.trivial ℚ PUnit.{u+1} TestSpace.{v}
  have hinj : Function.Injective ρ := fun _ _ _ => Subsingleton.elim _ _
  have horder : Nat.card PUnit.{u+1} ∣ 32 * 23 * 47 := by
    rw [Nat.card_unique]
    exact one_dvd _
  obtain ⟨W, hbot, _, hW⟩ := h ρ hinj test_dim horder
  exact hbot (le_antisymm (hW 1) bot_le)

def family : Registration arena.{u,v} (type_of% @exists_invariant_subspace_of_card_dvd.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_invariant_subspace_of_card_dvd.{u,v}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exists_invariant_subspace_of_card_dvd.{u,v}) (Realization signature.{v}) Unit Unit where
  unitName := `ExtremalC48.exists_invariant_subspace_of_card_dvd.__information_unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.Orbifold.P48qPrimeToThreeReducibility.InvariantSubspace.OrderDivisor.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v}⟩
  objectArena := .source ⟨arena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v} ⟨family.{u,v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p T =>
      letI := p.2.1
      letI := p.2.2
      Submodule.comap T) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Lattice.Orbifold.P48qPrimeToThreeReducibility
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "arg", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false
    }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

end OrderDivisor

namespace SL47

private abbrev AmbientGroup := Matrix.SpecialLinearGroup (Fin 2) (ZMod 47)

abbrev arena : Arena where
  signature := signature.{v}
  Law R := ∀ {V : Type v} [AddCommGroup V] [Module ℚ V]
    (H : Subgroup AmbientGroup), ¬ 3 ∣ Nat.card H →
    ∀ (ρ : Representation ℚ H V), Function.Injective ρ → finrank ℚ V = 48 →
    ∃ W : Submodule ℚ V, W ≠ ⊥ ∧ W ≠ ⊤ ∧
      ∀ g, W ≤ R.readout () ⟨V, inferInstance, inferInstance⟩ (ρ g) W

private theorem rejected_law : ¬ arena.{v}.Law rejected := by
  intro h
  let H : Subgroup AmbientGroup := ⊥
  let ρ := Representation.trivial ℚ H TestSpace.{v}
  have hinj : Function.Injective ρ := fun _ _ _ => Subsingleton.elim _ _
  have horder : ¬ 3 ∣ Nat.card H := by
    rw [Nat.card_unique]
    decide
  obtain ⟨W, hbot, _, hW⟩ := h H horder ρ hinj test_dim
  exact hbot (le_antisymm (hW 1) bot_le)

def family : Registration arena.{v} (type_of% @sl47_prime_to_three_exists_invariant_subspace.{v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@sl47_prime_to_three_exists_invariant_subspace.{v}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@sl47_prime_to_three_exists_invariant_subspace.{v}) (Realization signature.{v}) Unit Unit where
  unitName := `ExtremalC48.sl47_prime_to_three_exists_invariant_subspace.__information_unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.Orbifold.P48qPrimeToThreeReducibility.InvariantSubspace.SL47.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{v}⟩
  objectArena := .source ⟨arena.{v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{v} ⟨family.{v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p T =>
      letI := p.2.1
      letI := p.2.2
      Submodule.comap T) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Lattice.Orbifold.P48qPrimeToThreeReducibility
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "arg", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false
    }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

end SL47

end InvariantSubspace

end
end Reg.D5.S3.VertexAlgebra.Lattice.Orbifold.P48qPrimeToThreeReducibility
