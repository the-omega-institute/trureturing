/- GID: D5/S3/ConceptDynamics/Coding/PrimitiveLifts/RootMultiplicityMonoid
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/PrimitiveLifts/RootMultiplicityMonoid
   mirror-E: none(waiver:symbolic-structural-theorems)
   anchors: []
   utility: none
   digest: Mixed binary and ternary root blocks have exactly one missing scaled multiplicity. -/

import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Actual finite sums of positive divisor lengths with quotient gcd in {1,2,3}. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Coding.PrimitiveLifts.RootMultiplicityMonoid

private theorem quotient_dvd_small_multiple (a b m q d : ℕ)
    (hq : q ∣ 2 ^ (a + 1) * 3 ^ (b + 1) * m) (hg : Nat.gcd q 36 = d)
    (hd : 6 ∣ 36 / d) : q ∣ d * m := by
  have hdpos : 0 < Nat.gcd q 36 := Nat.gcd_pos_of_pos_right q (by decide)
  have hc : Nat.Coprime (q / d) 6 := by
    have h := Nat.coprime_div_gcd_div_gcd hdpos
    rw [hg] at h
    exact h.of_dvd_right hd
  have hcK : Nat.Coprime (q / d) (2 ^ (a + 1) * 3 ^ (b + 1)) :=
    ((hc.of_dvd_right (by decide : 2 ∣ 6)).pow_right (a + 1)).mul_right
      ((hc.of_dvd_right (by decide : 3 ∣ 6)).pow_right (b + 1))
  have hdq : d ∣ q := hg ▸ Nat.gcd_dvd_left q 36
  have hcm : q / d ∣ m :=
    hcK.dvd_of_dvd_mul_left ((Nat.div_dvd_of_dvd hdq).trans hq)
  have heq : d * (q / d) = q := Nat.mul_div_cancel' hdq
  rw [← heq]
  exact Nat.mul_dvd_mul_left d hcm

private theorem cancel_quotient (k ell t v : ℕ) (hk : 0 < k)
    (hell : ell ∣ k) (hfactor : k = t * v) (hq : k / ell ∣ v) : t ∣ ell := by
  have he : ell * (k / ell) = k := Nat.mul_div_cancel' hell
  have hqpos : 0 < k / ell := Nat.div_pos (Nat.le_of_dvd hk hell)
    (Nat.pos_of_dvd_of_pos hell hk)
  apply Nat.dvd_of_mul_dvd_mul_right hqpos
  calc
    t * (k / ell) ∣ t * v := Nat.mul_dvd_mul_left t hq
    _ = k := hfactor.symm
    _ = ell * (k / ell) := he.symm

private theorem allowed_divisor_reduction (a b m ell : ℕ) (hm : Nat.Coprime m 6)
    (hell : ell ∣ 2 ^ (a + 1) * 3 ^ (b + 1) * m)
    (hg : Nat.gcd ((2 ^ (a + 1) * 3 ^ (b + 1) * m) / ell) 36 = 1 ∨
      Nat.gcd ((2 ^ (a + 1) * 3 ^ (b + 1) * m) / ell) 36 = 2 ∨
      Nat.gcd ((2 ^ (a + 1) * 3 ^ (b + 1) * m) / ell) 36 = 3) :
    2 * (2 ^ a * 3 ^ b) ∣ ell ∨ 3 * (2 ^ a * 3 ^ b) ∣ ell := by
  have hmpos : 0 < m := Nat.pos_of_ne_zero (by
    intro h
    norm_num [h] at hm)
  have hk : 0 < 2 ^ (a + 1) * 3 ^ (b + 1) * m := by positivity
  have hq := Nat.div_dvd_of_dvd hell
  rcases hg with hg | hg | hg
  · have h := quotient_dvd_small_multiple a b m _ 1 hq hg (by decide)
    have ht : 6 * (2 ^ a * 3 ^ b) ∣ ell := cancel_quotient _ _ _ _ hk hell
      (by simp only [pow_succ]; ring) h
    exact Or.inl ((show 2 * (2 ^ a * 3 ^ b) ∣ 6 * (2 ^ a * 3 ^ b) from
      ⟨3, by ring⟩).trans ht)
  · exact Or.inr (cancel_quotient _ _ _ _ hk hell
      (by simp only [pow_succ]; ring)
      (quotient_dvd_small_multiple a b m _ 2 hq hg (by decide)))
  · exact Or.inl (cancel_quotient _ _ _ _ hk hell
      (by simp only [pow_succ]; ring)
      (quotient_dvd_small_multiple a b m _ 3 hq hg (by decide)))

private theorem generators_allowed (a b m : ℕ) (hm : Nat.Coprime m 6) :
    ∀ ell ∈ [2 * (2 ^ a * 3 ^ b), 3 * (2 ^ a * 3 ^ b)],
      0 < ell ∧ ell ∣ 2 ^ (a + 1) * 3 ^ (b + 1) * m ∧
        (Nat.gcd ((2 ^ (a + 1) * 3 ^ (b + 1) * m) / ell) 36 = 1 ∨
          Nat.gcd ((2 ^ (a + 1) * 3 ^ (b + 1) * m) / ell) 36 = 2 ∨
          Nat.gcd ((2 ^ (a + 1) * 3 ^ (b + 1) * m) / ell) 36 = 3) := by
  have hm36 : Nat.Coprime m 36 := by
    simpa using hm.pow_right 2
  have htwo : 0 < 2 * (2 ^ a * 3 ^ b) := by positivity
  have hthree : 0 < 3 * (2 ^ a * 3 ^ b) := by positivity
  have hKtwo : 2 ^ (a + 1) * 3 ^ (b + 1) * m = (2 * (2 ^ a * 3 ^ b)) * (3 * m) := by
    simp only [pow_succ]; ring
  have hKthree : 2 ^ (a + 1) * 3 ^ (b + 1) * m = (3 * (2 ^ a * 3 ^ b)) * (2 * m) := by
    simp only [pow_succ]; ring
  intro ell hell
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hell
  rcases hell with rfl | rfl
  · refine ⟨htwo, ⟨3 * m, hKtwo⟩, Or.inr (Or.inr ?_)⟩
    rw [hKtwo, Nat.mul_div_cancel_left _ htwo]
    rw [Nat.mul_comm 3 m]
    exact Nat.gcd_mul_of_coprime_of_dvd hm36 (by decide)
  · refine ⟨hthree, ⟨2 * m, hKthree⟩, Or.inr (Or.inl ?_)⟩
    rw [hKthree, Nat.mul_div_cancel_left _ hthree]
    rw [Nat.mul_comm 2 m]
    exact Nat.gcd_mul_of_coprime_of_dvd hm36 (by decide)

/-- Among multiples of `r`, exactly `r` is absent from the actual allowed-length sum monoid.
Zero is represented by the empty list; the two generating lengths are `2 * r` and `3 * r`. -/
theorem allowed_sum_iff (a b m n : ℕ) (hm : Nat.Coprime m 6) :
    let k := 2 ^ (a + 1) * 3 ^ (b + 1) * m
    let r := 2 ^ a * 3 ^ b
    (∃ L : List ℕ, L.sum = n ∧ ∀ ell ∈ L,
      0 < ell ∧ ell ∣ k ∧
        (Nat.gcd (k / ell) 36 = 1 ∨ Nat.gcd (k / ell) 36 = 2 ∨
          Nat.gcd (k / ell) 36 = 3)) ↔ (r ∣ n ∧ n ≠ r) := by
  dsimp only
  let r := 2 ^ a * 3 ^ b
  have hr : 0 < r := by dsimp [r]; positivity
  constructor
  · rintro ⟨L, hsum, hL⟩
    have hred : ∀ ell ∈ L, 2 * r ∣ ell ∨ 3 * r ∣ ell := by
      intro ell hell
      exact allowed_divisor_reduction a b m ell hm (hL ell hell).2.1 (hL ell hell).2.2
    constructor
    · rw [← hsum]
      apply List.dvd_sum
      intro ell hell
      rcases hred ell hell with h | h
      · exact (show r ∣ 2 * r from ⟨2, by ring⟩).trans h
      · exact (show r ∣ 3 * r from ⟨3, by ring⟩).trans h
    · intro hn
      cases L with
      | nil => simp only [List.sum_nil] at hsum; omega
      | cons ell L =>
        have hepos := (hL ell (by simp)).1
        have he : r < ell := by
          rcases hred ell (by simp) with h | h
          · have := Nat.le_of_dvd hepos h; omega
          · have := Nat.le_of_dvd hepos h; omega
        simp only [List.sum_cons] at hsum
        omega
  · rintro ⟨⟨s, hs⟩, hn⟩
    have hsone : s ≠ 1 := by
      intro h
      apply hn
      simpa only [h, mul_one] using hs
    by_cases hs0 : s = 0
    · exact ⟨[], by simp [hs, hs0], by simp⟩
    have hs2 : 2 ≤ s := by omega
    obtain ⟨A, B, hAB⟩ := Nat.exists_add_mul_eq_of_gcd_dvd_of_mul_pred_le 2 3 s
      (by norm_num) (by simpa using hs2)
    refine ⟨List.replicate A (2 * r) ++ List.replicate B (3 * r), ?_, ?_⟩
    · simp only [List.sum_append, List.sum_replicate_nat]
      calc
        A * (2 * r) + B * (3 * r) = r * (A * 2 + B * 3) := by ring
        _ = n := by rw [hAB]; exact hs.symm
    · intro ell hell
      have hmem : ell ∈ [2 * r, 3 * r] := by
        rcases List.mem_append.mp hell with h | h
        · simp [List.eq_of_mem_replicate h]
        · simp [List.eq_of_mem_replicate h]
      exact generators_allowed a b m hm ell hmem

end D5.S3.ConceptDynamics.Coding.PrimitiveLifts.RootMultiplicityMonoid
