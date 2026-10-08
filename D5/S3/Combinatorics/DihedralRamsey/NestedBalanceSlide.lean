/- GID: D5/S3/Combinatorics/DihedralRamsey/NestedBalanceSlide
   generality: G
   mirror-B: D5/B/S3/Combinatorics/DihedralRamsey/NestedBalanceSlide
   mirror-E: none(waiver:matching-hole-exchange)
   anchors: [mathlib/module/Mathlib.Algebra.BigOperators.Group.Finset.Basic]
   utility: none
   digest: Equal colour counts of two matchings differing at one vertex force its edge colour. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import D5.S3.Combinatorics.DihedralRamsey.NestedBalanceParity
import D5.S3.Combinatorics.DihedralRamsey.NestedMatching

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.DihedralRamsey.NestedBalanceSlide

open scoped BigOperators

/-- An involutive matching with a single exchanged endpoint has a forced edge colour. -/
theorem single_vertex_matching_exchange {α β : Type*} [Fintype α] [DecidableEq α]
    (C : β → β → ℕ) (hC : ∀ x y, C x y = C y x)
    (f : α → α) (hf : Function.Involutive f) (j : α) (hj : f j ≠ j)
    (ψ φ : α → β) (hmap : ∀ i, i ≠ j → ψ i = φ i)
    (hcount : (∑ i, C (ψ i) (ψ (f i))) = ∑ i, C (φ i) (φ (f i))) :
    C (ψ j) (ψ (f j)) = C (φ j) (φ (f j)) := by
  classical
  let S := (Finset.univ.erase j).erase (f j)
  have hrest : (∑ i ∈ S, C (ψ i) (ψ (f i))) =
      ∑ i ∈ S, C (φ i) (φ (f i)) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i ≠ j := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
    have hi'' : i ≠ f j := (Finset.mem_erase.mp hi).1
    have hfi : f i ≠ j := by
      intro h
      have := congrArg f h
      rw [hf] at this
      exact hi'' this
    rw [hmap i hi', hmap (f i) hfi]
  have split : ∀ g : α → ℕ,
      (∑ i, g i) = g j + g (f j) + ∑ i ∈ S, g i := by
    intro g
    have h₁ := Finset.sum_erase_add Finset.univ g (Finset.mem_univ j)
    have hmem : f j ∈ Finset.univ.erase j := Finset.mem_erase.mpr ⟨hj, by simp⟩
    have h₂ := Finset.sum_erase_add (Finset.univ.erase j) g hmem
    dsimp [S]
    omega
  rw [split (fun i => C (ψ i) (ψ (f i))),
    split (fun i => C (φ i) (φ (f i))), hf j, hC (ψ (f j)) (ψ j),
    hC (φ (f j)) (φ j), hrest] at hcount
  omega

/-- Sliding the hole across one endpoint preserves its colour at every opposite rank. -/
theorem adjacent_hole_exchange {m r : ℕ} (hm : 0 < m)
    (C : Fin (2 * m + 1) → Fin (2 * m + 1) → ℕ)
    (hC : ∀ x y, C x y = C y x)
    (balanced : ∀ (h : Fin (2 * m + 1)) (c : Fin (2 * m)), c.val % 2 = 1 →
      (∑ i : Fin (2 * m), C (h.succAbove i) (h.succAbove (c - i))) = 2 * r)
    (i j : Fin (2 * m)) (hij : (i.val + j.val) % 2 = 1) :
    C (j.succ.succAbove i) j.castSucc = C (j.succ.succAbove i) j.succ := by
  letI : NeZero (2 * m) := ⟨by omega⟩
  let c := i + j
  have hc : c.val % 2 = 1 := by
    simp only [c, Fin.val_add]
    rw [Nat.mod_mod_of_dvd _ (show 2 ∣ 2 * m from dvd_mul_right 2 m)]
    exact hij
  have hne : i ≠ j := by
    intro h
    subst i
    omega
  have hmap : ∀ x : Fin (2 * m), x ≠ j →
      j.succ.succAbove x = j.castSucc.succAbove x := by
    intro x hx
    by_cases hlt : x < j
    · rw [Fin.succAbove_of_castSucc_lt, Fin.succAbove_of_castSucc_lt]
      · exact Fin.castSucc_lt_castSucc_iff.mpr hlt
      · exact Fin.castSucc_lt_succ_iff.mpr (le_of_lt hlt)
    · have hgt : j < x := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hx)
      rw [Fin.succAbove_of_le_castSucc, Fin.succAbove_of_le_castSucc]
      · exact Fin.castSucc_le_castSucc_iff.mpr (le_of_lt hgt)
      · exact Fin.succ_le_castSucc_iff.mpr hgt
  have hf : Function.Involutive (fun x : Fin (2 * m) => c - x) := by
    intro x
    simp only [sub_eq_add_neg, neg_add_rev, neg_neg]
    simp only [add_assoc, add_left_comm, add_comm, add_neg_cancel, zero_add, add_zero]
  have hfj : c - j = i := by simp [c]
  have hcount : (∑ x : Fin (2 * m),
      C (j.succ.succAbove x) (j.succ.succAbove (c - x))) =
      ∑ x : Fin (2 * m),
        C (j.castSucc.succAbove x) (j.castSucc.succAbove (c - x)) := by
    rw [balanced j.succ c hc, balanced j.castSucc c hc]
  have h := single_vertex_matching_exchange C hC (fun x => c - x) hf j
    (by rw [hfj]; exact hne) j.succ.succAbove j.castSucc.succAbove hmap hcount
  have hpj : j.succ.succAbove j = j.castSucc :=
    Fin.succAbove_of_castSucc_lt _ _ (Fin.castSucc_lt_succ_iff.mpr le_rfl)
  have hφj : j.castSucc.succAbove j = j.succ :=
    Fin.succAbove_of_le_castSucc _ _ le_rfl
  rw [hfj, hpj, hφj, ← hmap i hne] at h
  exact (hC _ _).trans (h.trans (hC _ _))

/-- The exchange across the end of the linear order relates the first and last vertices. -/
theorem wrap_hole_exchange {m r : ℕ} (hm : 0 < m)
    (C : Fin (2 * m + 1) → Fin (2 * m + 1) → ℕ)
    (hC : ∀ x y, C x y = C y x)
    (balanced : ∀ (h : Fin (2 * m + 1)) (c : Fin (2 * m)), c.val % 2 = 1 →
      (∑ i : Fin (2 * m), C (h.succAbove i) (h.succAbove (c - i))) = 2 * r)
    (i : Fin (2 * m)) (hi : i.val % 2 = 1) :
    C (0 : Fin (2 * m + 1)) i.castSucc = C (Fin.last (2 * m)) i.castSucc := by
  letI : NeZero (2 * m) := ⟨by omega⟩
  let one : Fin (2 * m) := ⟨1, by omega⟩
  let φ : Fin (2 * m) → Fin (2 * m + 1) :=
    fun x => (0 : Fin (2 * m + 1)).succAbove (x - one)
  have hmap : ∀ x : Fin (2 * m), x ≠ 0 → x.castSucc = φ x := by
    intro x hx
    have hx' : 1 ≤ x.val := by
      have hne : x.val ≠ 0 := by
        intro h
        exact hx (Fin.ext h)
      omega
    apply Fin.ext
    dsimp [φ]
    rw [Fin.sub_val_of_le]
    · dsimp [one]
      omega
    · exact Fin.le_iff_val_le_val.mpr hx'
  have hφ : φ 0 = Fin.last (2 * m) := by
    apply Fin.ext
    dsimp [φ]
    rw [Fin.sub_def]
    dsimp [one]
    rw [Nat.mod_eq_of_lt (show 2 * m - 1 < 2 * m by omega)]
    omega
  let c := i - one - one
  have hc : c.val % 2 = 1 := by
    have he : c + one + one = i := by dsimp [c]; simp
    have hev := congrArg Fin.val he
    simp only [Fin.val_add, Nat.mod_add_mod] at hev
    have ho : one.val = 1 := rfl
    rw [ho] at hev
    have hp := congrArg (fun x : ℕ => x % 2) hev
    rw [Nat.mod_mod_of_dvd _ (show 2 ∣ 2 * m from dvd_mul_right 2 m)] at hp
    omega
  have hcount : (∑ x : Fin (2 * m), C x.castSucc (i - x).castSucc) =
      ∑ x : Fin (2 * m), C (φ x) (φ (i - x)) := by
    have hleft := balanced (Fin.last (2 * m)) i hi
    simp only [Fin.succAbove_last] at hleft
    rw [hleft]
    have bij : Function.Bijective (fun x : Fin (2 * m) => x + one) :=
      ⟨fun _ _ h => add_right_cancel h, fun x => ⟨x - one, sub_add_cancel x one⟩⟩
    have he := bij.sum_comp
      (fun x : Fin (2 * m) => C (φ x) (φ (i - x)))
    rw [← he]
    have hright := balanced (0 : Fin (2 * m + 1)) c hc
    rw [← hright]
    apply Finset.sum_congr rfl
    intro x _
    dsimp [φ, c]
    congr 2 <;> simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  have hf : Function.Involutive (fun x : Fin (2 * m) => i - x) := by
    intro x
    simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  have hin : i ≠ 0 := by
    intro h
    have hh := congrArg Fin.val h
    simp only [Fin.val_zero] at hh
    omega
  have h := single_vertex_matching_exchange C hC (fun x => i - x) hf 0
    (by simpa using hin) Fin.castSucc φ hmap hcount
  simpa only [sub_zero, Fin.castSucc_zero, hφ, ← hmap i hin] using h

end D5.S3.Combinatorics.DihedralRamsey.NestedBalanceSlide
