/- GID: D5/S3/FiniteGroups/HeadleyElementaryCycles
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/HeadleyElementaryCycles
   mirror-E: none(waiver:induction-leaves)
   anchors: []
   utility: none
   digest: Finite-field cycles and the two small leaves of two-primary induction. -/

import D5.S3.FiniteGroups.HeadleyExtension
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup
import Mathlib.GroupTheory.Perm.List
import Mathlib.Algebra.Group.Action.End
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Algebra.GroupWithZero.Units.Equiv

/-! Primitive field orbits and the small leaves used by two-primary induction. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.FiniteGroups.HeadleyElementaryCycles
open HeadleyExtension Function

private noncomputable def fieldCycle (F : Type*) [Field F] [Finite F]
    (hcard : 2 < Nat.card F) : RCycle F := by
  classical
  let z : Fˣ := Classical.choose (IsCyclic.exists_generator (α := Fˣ))
  have hz : ∀ x : Fˣ, x ∈ Subgroup.zpowers z :=
    Classical.choose_spec (IsCyclic.exists_generator (α := Fˣ))
  have hz1 : z ≠ 1 := by
    intro he
    have hc := orderOf_eq_card_of_forall_mem_zpowers hz
    rw [he, orderOf_one, Nat.card_units] at hc
    omega
  have hzv : (z : F) ≠ 1 := fun he => hz1 (Units.ext he)
  let S := MulAction.toPermHom Fˣ F
  refine {
    successor := S z
    successor_zero := ?_
    nonzero_cycle := ?_
    difference := Equiv.mulLeft₀ ((z : F) - 1) (sub_ne_zero.mpr hzv)
    difference_spec := ?_ }
  · change (z : F) * 0 = 0
    exact mul_zero _
  · refine ⟨?_, ?_⟩
    · have hzero : S z 0 = 0 := by change (z : F) * 0 = 0; exact mul_zero _
      exact HeadleyExtension.bijOn_complement _ 0 hzero
    · intro x hx y hy
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp
        (hz (Units.mk0 y hy / Units.mk0 x hx))
      refine ⟨k, ?_⟩
      rw [← map_zpow]
      change ((z ^ k : Fˣ) : F) * x = y
      rw [hk]
      simp only [Units.val_div_eq_div_val, Units.val_mk0]
      exact div_mul_cancel₀ y hx
  · intro x
    change ((z : F) - 1) * x = (z : F) * x - x
    ring

/-- A primitive multiplicative orbit supplies the additive cycle in every elementary rank. -/
noncomputable def elementaryCycle (k : ℕ) (hk : 2 ≤ k) :
    RCycle (Fin k → ZMod 2) := by
  classical
  let F := GaloisField 2 k
  letI : Fintype F := Fintype.ofFinite F
  have hk0 : k ≠ 0 := by omega
  have hc : 2 < Nat.card F := by
    rw [GaloisField.card 2 k hk0]
    have hp : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hk
    norm_num at hp ⊢
    omega
  let b := Module.finBasisOfFinrankEq (ZMod 2) F (GaloisField.finrank 2 hk0)
  exact transportCycle b.equivFun.toAddEquiv (fieldCycle F hc)

private def e4Word : List (ZMod 2 × ZMod 2) := [(1,0), (1,1), (0,1)]

private noncomputable def e4Cycle : RCycle (ZMod 2 × ZMod 2) where
  successor := e4Word.formPerm
  successor_zero := by decide
  nonzero_cycle := by
    have hn : e4Word.Nodup := by decide
    have hm : ∀ x : ZMod 2 × ZMod 2, x ∈ e4Word ↔ x ≠ 0 := by decide
    simpa only [hm] using hn.isCycleOn_formPerm
  difference := Equiv.ofBijective (fun x => e4Word.formPerm x - x) (by decide)
  difference_spec _ := rfl

/-- The quotient seed has the consecutive triple (1,0),(1,1),(0,1). -/
noncomputable def e4RStar : RStar (ZMod 2 × ZMod 2) where
  toRCycle := e4Cycle
  even_card := by norm_num [Nat.card_prod]
  a := (1,0)
  b := (1,1)
  c := (0,1)
  a_ne_zero := by decide
  b_ne_zero := by decide
  c_ne_zero := by decide
  pairwise_distinct := by decide
  successor_a := by decide
  successor_b := by decide
  triple_sum := by decide

private def c2c4Word : List (ZMod 2 × ZMod 4) :=
  [(0,2), (1,3), (0,3), (1,1), (1,0), (1,2), (0,1)]

/-- The seven-vertex R-only leaf includes the final edge back to (0,2). -/
noncomputable def c2c4Cycle : RCycle (ZMod 2 × ZMod 4) where
  successor := c2c4Word.formPerm
  successor_zero := by decide
  nonzero_cycle := by
    have hn : c2c4Word.Nodup := by decide
    have hm : ∀ x : ZMod 2 × ZMod 4, x ∈ c2c4Word ↔ x ≠ 0 := by decide
    simpa only [hm] using hn.isCycleOn_formPerm
  difference := Equiv.ofBijective (fun x => c2c4Word.formPerm x - x) (by decide)
  difference_spec _ := rfl

end D5.S3.FiniteGroups.HeadleyElementaryCycles
