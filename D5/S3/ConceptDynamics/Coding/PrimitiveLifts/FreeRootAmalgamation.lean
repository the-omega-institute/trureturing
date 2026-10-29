/- GID: D5/S3/ConceptDynamics/Coding/PrimitiveLifts/FreeRootAmalgamation
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/PrimitiveLifts/FreeRootAmalgamation
   mirror-E: none(waiver:symbolic-structural-theorems)
   anchors: [mathlib/module/Mathlib.GroupTheory.FreeGroup.CyclicallyReduced, mathlib/module/Mathlib.GroupTheory.SpecificGroups.Dihedral, mathlib/module/Mathlib.GroupTheory.Subgroup.Centralizer]
   utility: none
   digest: The actual free group on Bool is an infinite nonnilpotent sharpness countermodel with unique coprime roots. -/

import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.GroupTheory.Subgroup.Centralizer
import D5.S3.ConceptDynamics.Coding.PrimitiveLifts.NilpotentRootAmalgamation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Coding.PrimitiveLifts.FreeRootAmalgamation

open Subgroup

private theorem commute_of_equal_coprime_powers {G : Type*} [Group G] [HasUniqueRoots G]
    {x y : G} {m n : ℕ} (hmn : m.Coprime n) (h : x ^ m = y ^ n) : Commute x y := by
  by_cases hm : m = 0
  · have hn : n = 1 := n.coprime_zero_left.mp (hm ▸ hmn)
    have hy : y = 1 := by
      simpa [hm, hn] using h.symm
    rw [hy]
    exact Commute.one_right x
  · have hconj : (y * x * y⁻¹) ^ m = x ^ m := by
      rw [conj_pow, h]
      have hpowcomm : Commute y (y ^ n) := (Commute.refl y).pow_right n
      rw [hpowcomm.eq]
      simp
    have heq : y * x * y⁻¹ = x := pow_left_injective hm hconj
    have hmul : y * x = x * y := by
      calc
        y * x = (y * x * y⁻¹) * y := by simp [mul_assoc]
        _ = x * y := by rw [heq]
    exact hmul.symm

private theorem free_root_amalgamation {x y : FreeGroup Bool} {m n : ℕ}
    (hmn : m.Coprime n) (h : x ^ m = y ^ n) :
    ∃! z : FreeGroup Bool, x = z ^ n ∧ y = z ^ m := by
  by_cases hm : m = 0
  · have hn : n = 1 := n.coprime_zero_left.mp (hm ▸ hmn)
    have hy : y = 1 := by
      simpa [hm, hn] using h.symm
    refine ⟨x, ?_, ?_⟩
    · simp [hm, hn, hy]
    · intro z hz
      simpa [hn] using hz.1.symm
  · have hxy : Commute x y := commute_of_equal_coprime_powers hmn h
    let H : Subgroup (FreeGroup Bool) := Subgroup.closure ({x, y} : Set (FreeGroup Bool))
    have hset : ({x, y} : Set (FreeGroup Bool)).Pairwise Commute := by
      intro a ha b hb hab
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact Commute.refl _
      · exact hxy
      · exact hxy.symm
      · exact Commute.refl _
    letI : IsMulCommutative H := by
      exact Subgroup.isMulCommutative_closure hset
    let hx : H := ⟨x, by exact Subgroup.subset_closure (by simp)⟩
    let hy : H := ⟨y, by exact Subgroup.subset_closure (by simp)⟩
    have hp : hx ^ m = hy ^ n := Subtype.ext h
    obtain ⟨z, hz, hzuniq⟩ :=
      (D5.S3.ConceptDynamics.Coding.PrimitiveLifts.NilpotentRootAmalgamation.pow_eq_pow_iff_exists_unique
        hx hy m n hmn).mp hp
    refine ⟨(z : FreeGroup Bool), ?_, ?_⟩
    · exact ⟨congrArg Subtype.val hz.1, congrArg Subtype.val hz.2⟩
    · intro w hw
      have hwm : w ^ m = (z : FreeGroup Bool) ^ m := by
        exact hw.2.symm.trans (congrArg Subtype.val hz.2)
      exact pow_left_injective hm hwm

private def freeToDihedral : FreeGroup Bool →* DihedralGroup 0 :=
  FreeGroup.lift (fun b => if b then DihedralGroup.sr 0 else DihedralGroup.r 1)

private theorem freeToDihedral_surjective : Function.Surjective freeToDihedral := by
  intro g
  cases g with
  | r i =>
      refine ⟨(FreeGroup.of false) ^ (ZMod.cast i : ℤ), ?_⟩
      simp [freeToDihedral, DihedralGroup.r_one_zpow]
  | sr i =>
      refine ⟨FreeGroup.of true * (FreeGroup.of false) ^ (ZMod.cast i : ℤ), ?_⟩
      simp [freeToDihedral, DihedralGroup.r_one_zpow]

private theorem freeGroupBool_infinite : Infinite (FreeGroup Bool) :=
  Infinite.of_surjective freeToDihedral freeToDihedral_surjective

private theorem freeGroupBool_not_nilpotent : ¬ Group.IsNilpotent (FreeGroup Bool) := by
  intro h
  letI : Group.IsNilpotent (FreeGroup Bool) := h
  letI : Group.IsNilpotent (DihedralGroup 0) :=
    Group.nilpotent_of_surjective freeToDihedral freeToDihedral_surjective
  have hc : Subgroup.center (DihedralGroup 0) ≠ ⊥ :=
    Group.IsNilpotent.center_ne_bot (DihedralGroup 0)
  rw [DihedralGroup.center_eq_bot_of_zero] at hc
  exact hc rfl

/-- The free group on Bool is an explicit infinite nonnilpotent sharpness countermodel:
equal coprime powers have exactly one common root, including the zero-exponent boundaries. -/
theorem freeGroupBool_infinite_not_nilpotent_coprime_root :
    Infinite (FreeGroup Bool) ∧
      ¬ Group.IsNilpotent (FreeGroup Bool) ∧
      ∀ (x y : FreeGroup Bool) (m n : ℕ), m.Coprime n →
        (x ^ m = y ^ n ↔ ∃! z : FreeGroup Bool, x = z ^ n ∧ y = z ^ m) := by
  refine ⟨freeGroupBool_infinite, freeGroupBool_not_nilpotent, ?_⟩
  intro x y m n hmn
  constructor
  · exact free_root_amalgamation hmn
  · rintro ⟨z, ⟨rfl, rfl⟩, _⟩
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]

end D5.S3.ConceptDynamics.Coding.PrimitiveLifts.FreeRootAmalgamation
