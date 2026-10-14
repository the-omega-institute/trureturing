/- GID: D5/S3/Arith/APNBreakingRefutation
   generality: I
   mirror-B: D5/B/S3/Arith/APNBreakingRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.FieldTheory.Finite.GaloisField, mathlib/module/Mathlib.LinearAlgebra.Dimension.Free, mathlib/module/Mathlib.LinearAlgebra.Dimension.Finrank, mathlib/module/Mathlib.Tactic]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Arith/APNBreakingRefutation.claim; result=D5/S3/Arith/APNBreakingRefutation.result; claim=D5/S3/Arith/APNBreakingRefutation.claim
   digest: An APN map on a field of order sixteen maps a three-dimensional flat onto a flat. -/

import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Tactic

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace D5.S3.Arith.APNBreakingRefutation

/-- Every nonzero derivative has fibers of size at most two. -/
def APN {M : Type*} [AddCommGroup M] [Fintype M] [DecidableEq M]
    (F : M → M) : Prop :=
  ∀ a b : M, a ≠ 0 →
    (Finset.univ.filter fun x : M => F (x + a) + F x = b).card ≤ 2

/-- The coset a + V, expressed by subtraction membership. -/
def affineFlat {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    (a : M) (V : Submodule (ZMod 2) M) : Set M := {x | x - a ∈ V}

/-- The image is a coset of a binary subspace of arbitrary dimension. -/
def IsFlat {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] (A : Set M) : Prop :=
  ∃ a V, A = affineFlat a V

/-- Conjecture 3.1 over all finite fields of binary prime-power order. -/
def claim : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] [CharP K 2],
    let : Algebra (ZMod 2) K := ZMod.algebra K 2
    ∀ n : ℕ, Fintype.card K = 2 ^ n → ∀ F : K → K, APN F →
    ∀ k : ℕ, n / 2 + 1 ≤ k → k ≤ n - 1 →
    ∀ a : K, ∀ V : Submodule (ZMod 2) K, Module.finrank (ZMod 2) V = k →
      ¬ IsFlat (F '' affineFlat a V)

/-- Additive coordinate changes preserve the complete APN condition. -/
theorem apn_conjugate_iff {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Fintype M] [Fintype N] [DecidableEq M] [DecidableEq N]
    (e : M ≃+ N) (F : M → M) :
    APN (fun y => e (F (e.symm y))) ↔ APN F := by
  have fibers (a b : M) :
      (Finset.univ.filter fun x : M => F (x + a) + F x = b).card =
      (Finset.univ.filter fun y : N =>
        e (F (e.symm (y + e a))) + e (F (e.symm y)) = e b).card := by
    apply Finset.card_equiv e.toEquiv
    intro x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change F (x + a) + F x = b ↔
      e (F (e.symm (e x + e a))) + e (F (e.symm (e x))) = e b
    simp only [← e.map_add, e.symm_apply_apply]
    exact e.injective.eq_iff.symm
  constructor
  · intro h a b ha
    rw [fibers]
    exact h (e a) (e b) (by simpa using ha)
  · intro h a b ha
    obtain ⟨a, rfl⟩ := e.surjective a
    obtain ⟨b, rfl⟩ := e.surjective b
    rw [← fibers]
    exact h a b (by simpa using ha)

/-- A binary linear coordinate change maps cosets to cosets of the same dimension. -/
theorem affineFlat_image {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module (ZMod 2) M] [Module (ZMod 2) N]
    (e : M ≃ₗ[ZMod 2] N) (a : M) (V : Submodule (ZMod 2) M) :
    e '' affineFlat a V = affineFlat (e a) (V.map e.toLinearMap) ∧
      Module.finrank (ZMod 2) (V.map e.toLinearMap) = Module.finrank (ZMod 2) V := by
  constructor
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x - a, hx, e.map_sub x a⟩
    · rintro ⟨v, hv, he⟩
      refine ⟨v + a, ?_, ?_⟩
      · change v ∈ V at hv
        change v + a - a ∈ V
        rw [add_sub_cancel_right]
        exact hv
      · change e v = y - e a at he
        rw [map_add, he, sub_add_cancel]
  · exact e.finrank_map_eq V

abbrev W := Fin 4 → ZMod 2

/-- Binary labels specify the sixteen values independently of field multiplication. -/
def G (v : W) : W :=
  let label := (v 0).val + 2 * (v 1).val + 4 * (v 2).val + 8 * (v 3).val
  let value := ([0, 9, 4, 11, 0, 14, 1, 9, 15, 2, 6, 13, 1, 11, 13, 1] : List ℕ).getD label 0
  fun i => ((value / 2 ^ i.val) : ℕ)

private def inputSpace : Submodule (ZMod 2) W where
  carrier := {v | v 2 = 0}
  zero_mem' := rfl
  add_mem' := by intro x y hx hy; simp_all
  smul_mem' := by intro c x hx; simp_all

private def outputSpace : Submodule (ZMod 2) W where
  carrier := {v | v 0 = v 3}
  zero_mem' := rfl
  add_mem' := by intro x y hx hy; simp_all
  smul_mem' := by intro c x hx; simp_all

/-- The universal conjecture fails at n = 4 and k = 3. -/
theorem result : ¬ claim := by
  have hapn : APN G := by
    unfold APN
    decide +kernel
  have himage : G '' affineFlat 0 inputSpace = affineFlat 0 outputSpace := by
    ext v
    change (∃ x : W, x - 0 ∈ inputSpace ∧ G x = v) ↔ v - 0 ∈ outputSpace
    simp only [sub_zero]
    change (∃ x : W, x 2 = 0 ∧ G x = v) ↔ v 0 = v 3
    revert v
    decide +kernel
  have hcardInput : Fintype.card {v : W // v 2 = 0} = 8 := by decide +kernel
  classical
  let K := GaloisField 2 4
  let : Fintype K := Fintype.ofFinite K
  let : Algebra (ZMod 2) K := ZMod.algebra K 2
  have hcardK : Fintype.card K = 2 ^ 4 := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 2 4 (by decide)
  have hdimK : Module.finrank (ZMod 2) K = 4 :=
    Nat.pow_right_injective (by decide : 1 < 2)
      ((FiniteField.pow_finrank_eq_card 2 K).trans hcardK)
  let e : W ≃ₗ[ZMod 2] K := LinearEquiv.ofFinrankEq W K (by
    rw [Module.finrank_fin_fun, hdimK])
  have hdim : Module.finrank (ZMod 2) inputSpace = 3 := by
    have hc : Fintype.card inputSpace = 2 ^ Module.finrank (ZMod 2) inputSpace :=
      Module.card_eq_pow_finrank
    have hc8 : Fintype.card inputSpace = 8 := by
      have heq : (inputSpace : Set W) = {v : W | v 2 = 0} := rfl
      exact (Fintype.card_congr (Set.equivOfEq heq)).trans hcardInput
    rw [hc8] at hc
    exact Nat.pow_right_injective (by decide : 1 < 2) (by simpa using hc.symm)
  let F : K → K := fun x => e (G (e.symm x))
  have hF : APN F := (apn_conjugate_iff e.toAddEquiv G).mpr hapn
  have hA := affineFlat_image e 0 inputSpace
  have hB := (affineFlat_image e 0 outputSpace).1
  have hbad : IsFlat (F '' affineFlat 0 (inputSpace.map e.toLinearMap)) := by
    refine ⟨0, outputSpace.map e.toLinearMap, ?_⟩
    have hi : F '' (e '' affineFlat 0 inputSpace) = e '' (G '' affineFlat 0 inputSpace) := by
      rw [Set.image_image, Set.image_image]
      congr 1
      funext x
      exact congrArg e (congrArg G (e.symm_apply_apply x))
    simpa only [map_zero, hA.1, himage, hB] using hi
  intro hclaim
  exact hclaim K 4 hcardK F hF 3 (by decide) (by decide) 0
    (inputSpace.map e.toLinearMap) (hA.2.trans hdim) hbad

end D5.S3.Arith.APNBreakingRefutation
