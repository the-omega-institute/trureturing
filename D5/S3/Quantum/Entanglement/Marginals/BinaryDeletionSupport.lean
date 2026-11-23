/- GID: D5/S3/Quantum/Entanglement/Marginals/BinaryDeletionSupport
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/Marginals/BinaryDeletionSupport
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: A deletion-invisible entry forces its entire agreeing-coordinate family into support. -/

import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Matrix.Basic

/-! Entry support for matrices with vanishing binary deletion traces. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.Marginals.BinaryDeletionSupport

open Function (update)
open scoped BigOperators

variable {V : Type*} [DecidableEq V]

/-- Two ordered binary pairs have the same differing coordinates and orientations. -/
def SamePattern (x y u v : V → Bool) : Prop :=
  ∀ i, if x i = y i then u i = v i else u i = x i ∧ v i = y i

/-- The two summands for each one-site deletion cancel at every retained entry. -/
def InDeletionKernel (R : Matrix (V → Bool) (V → Bool) ℂ) : Prop :=
  ∀ i x y, R (update x i false) (update y i false) +
    R (update x i true) (update y i true) = 0

private theorem change_common_bit {R : Matrix (V → Bool) (V → Bool) ℂ}
    (hR : InDeletionKernel R) {u v : V → Bool} {i : V} (heq : u i = v i)
    (h : R u v ≠ 0) (b : Bool) : R (update u i b) (update v i b) ≠ 0 := by
  intro hz
  have htrace := hR i u v
  cases b <;> rw [hz] at htrace <;> simp only [zero_add, add_zero] at htrace
  all_goals
    apply h
    cases hu : u i
    · have hv : v i = false := heq.symm.trans hu
      have h1 : update u i false = u := by rw [← hu, Function.update_eq_self]
      have h2 : update v i false = v := by rw [← hv, Function.update_eq_self]
      first | simpa only [h1, h2] using hz | simpa only [h1, h2] using htrace
    · have hv : v i = true := heq.symm.trans hu
      have h1 : update u i true = u := by rw [← hu, Function.update_eq_self]
      have h2 : update v i true = v := by rw [← hv, Function.update_eq_self]
      first | simpa only [h1, h2] using hz | simpa only [h1, h2] using htrace

private theorem nonzero_on_pattern {R : Matrix (V → Bool) (V → Bool) ℂ}
    [Finite V] (hR : InDeletionKernel R) {x y u v : V → Bool} (hnz : R x y ≠ 0)
    (hmatch : SamePattern x y u v) : R u v ≠ 0 := by
  letI := Fintype.ofFinite V
  let put (z : V → Bool) (s : Finset V) : V → Bool := fun j =>
    if j ∈ s then u j else z j
  have preserve (s : Finset V) (hs : ∀ i ∈ s, x i = y i) :
      R (put x s) (put y s) ≠ 0 := by
    induction s using Finset.induction_on with
    | empty => simpa [put] using hnz
    | @insert i s hi ih =>
      have agree : put x s i = put y s i := by
        simpa [put, hi] using hs i (Finset.mem_insert_self i s)
      have step := change_common_bit hR agree (ih (fun j hj => hs j (Finset.mem_insert_of_mem hj)))
        (u i)
      have inserted (z : V → Bool) : put z (insert i s) = update (put z s) i (u i) := by
        funext j
        by_cases hji : j = i
        · subst j
          simp [put]
        · simp [put, hji, Function.update_of_ne]
      simpa only [← inserted x, ← inserted y] using step
  let agreeing : Finset V := Finset.univ.filter fun i => x i = y i
  have hl : put x agreeing = u := by
    funext i
    by_cases heq : x i = y i
    · simp [put, agreeing, heq]
    · have hi := hmatch i
      simp only [ite_eq_right heq] at hi
      simp [put, agreeing, heq, hi.1]
  have hr : put y agreeing = v := by
    funext i
    have hi := hmatch i
    by_cases heq : x i = y i
    · simp only [ite_eq_left heq] at hi
      simpa [put, agreeing, heq] using hi
    · simp only [ite_eq_right heq] at hi
      simp [put, agreeing, heq, hi.2]
  simpa only [hl, hr] using preserve agreeing (fun i hi => (Finset.mem_filter.mp hi).2)

/-- A matrix entry can survive all deletion constraints exactly when both words stay allowed
throughout the set of pairs with that differing-coordinate pattern. -/
theorem survives_iff [Finite V] (Allowed : (V → Bool) → Prop) (x y : V → Bool) :
    (∃ R : Matrix (V → Bool) (V → Bool) ℂ, InDeletionKernel R ∧ R x y ≠ 0 ∧
      ∀ u v, R u v ≠ 0 → Allowed u ∧ Allowed v) ↔
    ∀ u v, SamePattern x y u v → Allowed u ∧ Allowed v := by
  classical
  letI := Fintype.ofFinite V
  constructor
  · rintro ⟨R, hR, hnz, hs⟩ u v huv
    exact hs u v (nonzero_on_pattern hR hnz huv)
  · intro allowed
    let sign (u : V → Bool) (j : V) : ℂ :=
      if x j = y j ∧ u j = true then -1 else 1
    let R : Matrix (V → Bool) (V → Bool) ℂ := fun u v =>
      if SamePattern x y u v then ∏ j, sign u j else 0
    have hself : SamePattern x y x y := by
      intro i
      split <;> simp_all
    refine ⟨R, ?_, ?_, ?_⟩
    · intro i u v
      have change (b : Bool) (c : Bool)
          (h : SamePattern x y (update u i b) (update v i b)) :
          SamePattern x y (update u i c) (update v i c) := by
        intro j
        by_cases hji : j = i
        · subst j
          have hj := h i
          by_cases he : x i = y i
          · simp [he]
          · simp [he] at hj
            exact (he (hj.1.symm.trans hj.2)).elim
        · simpa [Function.update_of_ne hji] using h j
      by_cases hf : SamePattern x y (update u i false) (update v i false)
      · have ht := change false true hf
        have he : x i = y i := by
          have hi := hf i
          by_contra hh
          simp [hh] at hi
          exact hh (hi.1.trans hi.2.symm)
        simp only [R, ite_eq_left hf, ite_eq_left ht]
        rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i),
          ← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
        have products :
            (∏ j ∈ Finset.univ.erase i, sign (update u i false) j) =
              ∏ j ∈ Finset.univ.erase i, sign (update u i true) j := by
          apply Finset.prod_congr rfl
          intro j hj
          simp [sign, Function.update_of_ne (Finset.ne_of_mem_erase hj)]
        rw [products]
        simp [sign, he]
      · have ht : ¬ SamePattern x y (update u i true) (update v i true) :=
          fun h => hf (change true false h)
        simp [R, hf, ht]
    · simp only [R, ite_eq_left hself]
      apply Finset.prod_ne_zero_iff.mpr
      intro j _
      unfold sign
      split <;> simp
    · intro u v hnz
      by_cases hmatches : SamePattern x y u v
      · exact allowed u v hmatches
      · exact (hnz (by simp [R, hmatches])).elim

end D5.S3.Quantum.Entanglement.Marginals.BinaryDeletionSupport
