/- GID: D5/S1/Recurrence/Residue/OEISA242926AntidiagonalLcm
   generality: I
   mirror-B: D5/B/S1/Recurrence/Residue/OEISA242926AntidiagonalLcm
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: [mathlib/module/Mathlib.Algebra.GCDMonoid.Finset]
   utility: none
   digest: Antidiagonal denominators of Curtz's arrays B and U have lcm lcm(1..floor((s+1)/2)). -/

import D5.S1.Recurrence.Residue.OEISA189733Reflection
import D5.S1.Recurrence.Residue.OEISA242926UnsignedLucasRow
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat

/-! The antidiagonal denominator lcm of the signed and unsigned zero-diagonal arrays. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Recurrence.Residue.OEISA242926AntidiagonalLcm

open Finset
open D5.S1.Recurrence.Residue.OEISA189733DenominatorConjecture
open D5.S1.Recurrence.Residue.OEISA189733Reflection
open D5.S1.Recurrence.Residue.OEISA242926UnsignedLucasRow

/-- Upper entries `V w m d = V(m, m + d)` of a zero-diagonal array with arbitrary
first-superdiagonal seeds `w m = V(m, m + 1)` and the recurrence
`V(m, n) = V(m, n - 1) + V(m + 1, n - 1)`. -/
def V (w : ℕ → ℚ) : ℕ → ℕ → ℚ
  | _, 0 => 0
  | m, 1 => w m
  | m, k + 2 => V w m (k + 1) + V w (m + 1) k

/-- `x` is an integer. -/
private def IsZ (x : ℚ) : Prop := ∃ z : ℤ, x = z

private theorem IsZ.add {x y : ℚ} (hx : IsZ x) (hy : IsZ y) : IsZ (x + y) := by
  obtain ⟨a, rfl⟩ := hx; obtain ⟨b, rfl⟩ := hy; exact ⟨a + b, by push_cast; ring⟩

private theorem IsZ.sub {x y : ℚ} (hx : IsZ x) (hy : IsZ y) : IsZ (x - y) := by
  obtain ⟨a, rfl⟩ := hx; obtain ⟨b, rfl⟩ := hy; exact ⟨a - b, by push_cast; ring⟩

private theorem IsZ.nat_mul {x : ℚ} (c : ℕ) (hx : IsZ x) : IsZ (c * x) := by
  obtain ⟨a, rfl⟩ := hx; exact ⟨c * a, by push_cast; ring⟩

private theorem IsZ.sum {ι : Type*} (s : Finset ι) (f : ι → ℚ) (h : ∀ i ∈ s, IsZ (f i)) :
    IsZ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a s ha ih =>
    rw [sum_insert ha]
    exact (h a (mem_insert_self a s)).add (ih fun i hi => h i (mem_insert_of_mem hi))

private theorem den_dvd_iff (q : ℚ) (N : ℕ) : q.den ∣ N ↔ IsZ (N * q) := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c * q.num, ?_⟩
    rw [hc]; push_cast
    rw [mul_comm (q.den : ℚ) c, mul_assoc, mul_comm (q.den : ℚ), Rat.mul_den_eq_num]
  · rintro ⟨z, hz⟩
    have h1 : (N : ℚ) * q.num = z * q.den := by
      rw [← Rat.mul_den_eq_num, ← mul_assoc, hz]
    have h2 : (q.den : ℤ) ∣ (N : ℤ) * q.num := ⟨z, by exact_mod_cast (h1.trans (mul_comm _ _))⟩
    have h3 : q.den ∣ N * q.num.natAbs := by
      have := Int.natAbs_dvd_natAbs.mpr h2
      simpa [Int.natAbs_mul] using this
    exact (Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.symm q.reduced) h3)

private theorem pascal_step (w : ℕ → ℚ) (m e : ℕ) :
    ∑ j ∈ range (e + 1 + 1), ((e + 1 - j).choose j : ℚ) * w (m + j) +
      ∑ j ∈ range (e + 1), ((e - j).choose j : ℚ) * w (m + 1 + j) =
    ∑ j ∈ range (e + 2 + 1), ((e + 2 - j).choose j : ℚ) * w (m + j) := by
  let f : ℕ → ℚ := fun j => ((e + 2 - j).choose j : ℚ) * w (m + j)
  let g : ℕ → ℚ := fun j => ((e + 1 - j).choose j : ℚ) * w (m + j)
  let k : ℕ → ℚ := fun j => ((e - j).choose j : ℚ) * w (m + 1 + j)
  have hL : ∑ j ∈ range (e + 2 + 1), f j = (∑ i ∈ range (e + 1), f (i + 1)) + f (e + 2) + f 0 := by
    rw [sum_range_succ', sum_range_succ]
  have hR : ∑ j ∈ range (e + 1 + 1), g j = (∑ i ∈ range (e + 1), g (i + 1)) + g 0 := by
    rw [sum_range_succ']
  have hlast : f (e + 2) = 0 := by
    simp only [f, show e + 2 - (e + 2) = 0 by omega,
      Nat.choose_eq_zero_of_lt (show 0 < e + 2 by omega)]
    simp
  have h0 : f 0 = g 0 := by simp [f, g]
  have hmid : ∀ i ∈ range (e + 1), f (i + 1) = g (i + 1) + k i := by
    intro i hi
    have hi' : i ≤ e := Nat.lt_succ_iff.mp (mem_range.mp hi)
    simp only [f, g, k]
    rw [show e + 2 - (i + 1) = (e - i) + 1 by omega, show e + 1 - (i + 1) = e - i by omega,
      Nat.choose_succ_succ', show m + 1 + i = m + (i + 1) by ring]
    push_cast
    ring
  show ∑ j ∈ range (e + 1 + 1), g j + ∑ j ∈ range (e + 1), k j = ∑ j ∈ range (e + 2 + 1), f j
  rw [hL, hR, hlast, h0, sum_congr rfl hmid, sum_add_distrib]
  ring

private theorem V_formula (w : ℕ → ℚ) (e : ℕ) : ∀ m, V w m (e + 1) =
    ∑ j ∈ range (e + 1), ((e - j).choose j : ℚ) * w (m + j) := by
  induction e using Nat.strong_induction_on with
  | _ e ih =>
    intro m
    rcases e with _ | _ | e
    · simp [V]
    · simp [V, sum_range_succ]
    · rw [show e + 1 + 1 + 1 = (e + 1) + 2 by ring, V, ih (e + 1) (by omega) m,
        ih e (by omega) (m + 1), pascal_step]

/-- An integer clears the strict upper antidiagonal `s` iff it clears the first `⌊(s+1)/2⌋`
seeds. -/
private theorem clear_iff (w : ℕ → ℚ) (s N : ℕ) :
    (∀ m, m < s - m → IsZ (N * V w m (s - 2 * m))) ↔
      ∀ k, k < (s + 1) / 2 → IsZ (N * w k) := by
  have hrepr : ∀ m, m < s - m → V w m (s - 2 * m) =
      ∑ j ∈ range (s - 2 * m), ((s - 2 * m - 1 - j).choose j : ℚ) * w (m + j) := by
    intro m hm
    obtain ⟨e, he⟩ : ∃ e, s - 2 * m = e + 1 := ⟨s - 2 * m - 1, by omega⟩
    rw [he, V_formula, show e + 1 - 1 = e by omega]
  -- a term with a nonzero coefficient has seed index below the bound
  have hidx : ∀ m j, m < s - m → j < s - 2 * m → (s - 2 * m - 1 - j).choose j ≠ 0 →
      m + j < (s + 1) / 2 := by
    intro m j hm hj hc
    have : j ≤ s - 2 * m - 1 - j := by
      by_contra h
      exact hc (Nat.choose_eq_zero_of_lt (by omega))
    omega
  constructor
  · intro h
    have key : ∀ t k, (s + 1) / 2 - k = t → k < (s + 1) / 2 → IsZ (N * w k) := by
      intro t
      induction t using Nat.strong_induction_on with
      | _ t ih =>
        intro k ht hk
        have hm : k < s - k := by omega
        have he := h k hm
        rw [hrepr k hm, show s - 2 * k = (s - 2 * k - 1) + 1 by omega, sum_range_succ',
          mul_add] at he
        simp only [Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, one_mul,
          Nat.add_zero] at he
        have hrest : IsZ (N * ∑ j ∈ range (s - 2 * k - 1),
            ((s - 2 * k - 1 - (j + 1)).choose (j + 1) : ℚ) * w (k + (j + 1))) := by
          rw [mul_sum]
          apply IsZ.sum
          intro j hj
          by_cases hc : (s - 2 * k - 1 - (j + 1)).choose (j + 1) = 0
          · exact ⟨0, by simp [hc]⟩
          · have hlt := hidx k (j + 1) hm (by have := mem_range.mp hj; omega) hc
            have := ih ((s + 1) / 2 - (k + (j + 1))) (by omega) (k + (j + 1)) rfl hlt
            rw [show (N : ℚ) * (((s - 2 * k - 1 - (j + 1)).choose (j + 1) : ℚ) *
              w (k + (j + 1))) = ((s - 2 * k - 1 - (j + 1)).choose (j + 1) : ℕ) *
              (N * w (k + (j + 1))) by ring]
            exact this.nat_mul _
        have := he.sub hrest
        simpa using this
    exact fun k hk => key _ k rfl hk
  · intro h m hm
    rw [hrepr m hm, mul_sum]
    apply IsZ.sum
    intro j hj
    by_cases hc : (s - 2 * m - 1 - j).choose j = 0
    · exact ⟨0, by simp [hc]⟩
    · have := h (m + j) (hidx m j hm (mem_range.mp hj) hc)
      rw [show (N : ℚ) * (((s - 2 * m - 1 - j).choose j : ℚ) * w (m + j)) =
        ((s - 2 * m - 1 - j).choose j : ℕ) * (N * w (m + j)) by ring]
      exact this.nat_mul _

private theorem seed_iff (σ : ℚ) (hσ : σ = 1 ∨ σ = -1) (k N : ℕ) :
    IsZ (N * (σ / (k + 1))) ↔ (k + 1) ∣ N := by
  constructor
  · rintro ⟨z, hz⟩
    have hk : (k : ℚ) + 1 ≠ 0 := by positivity
    have h1 : (N : ℚ) = σ * z * (k + 1) := by
      rcases hσ with rfl | rfl
      · field_simp at hz; linarith
      · field_simp at hz; linarith
    have h2 : ((k + 1 : ℕ) : ℤ) ∣ (N : ℤ) := by
      rcases hσ with rfl | rfl
      · exact ⟨z, by exact_mod_cast (by rw [h1]; ring : (N : ℚ) = (k + 1) * z)⟩
      · exact ⟨-z, by exact_mod_cast (by rw [h1]; ring : (N : ℚ) = (k + 1) * -z)⟩
    exact Int.natCast_dvd_natCast.mp h2
  · rintro ⟨c, rfl⟩
    have hk : (k : ℚ) + 1 ≠ 0 := by positivity
    rcases hσ with rfl | rfl
    · refine ⟨c, ?_⟩
      push_cast
      field_simp
    · refine ⟨-c, ?_⟩
      push_cast
      field_simp

private theorem triangle_eq_V (d : ℕ) :
    ∀ m, triangle m d = V (fun k => (-1) ^ k / (k + 1)) m d := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro m
    rcases d with _ | _ | d
    · simp [triangle, V]
    · simp [triangle, V]
    · rw [triangle, V, ih (d + 1) (by omega), ih d (by omega)]

private theorem Ut_eq_V (d : ℕ) : ∀ m, Ut m d = V (fun k => 1 / (k + 1)) m d := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro m
    rcases d with _ | _ | d
    · simp [Ut, V]
    · simp [Ut, V]
    · rw [Ut, V, ih (d + 1) (by omega), ih d (by omega)]

/-- The lcm of the reduced denominators on the strict upper antidiagonal `m + n = s`. -/
def antiLcm (A : ℕ → ℕ → ℚ) (s : ℕ) : ℕ :=
  ((range s).filter (fun m => m < s - m)).lcm (fun m => (A m (s - m)).den)

/-- A139550: `lcm(1, …, ⌊r / 2⌋)`. -/
def A139550 (r : ℕ) : ℕ := (Icc 1 (r / 2)).lcm id

private theorem antiLcm_eq (A : ℕ → ℕ → ℚ) (w : ℕ → ℚ) (s : ℕ)
    (hA : ∀ m, m < s - m → A m (s - m) = V w m (s - 2 * m))
    (hw : ∀ k N : ℕ, IsZ (N * w k) ↔ (k + 1) ∣ N) :
    antiLcm A s = (Icc 1 ((s + 1) / 2)).lcm id := by
  have H : ∀ N, antiLcm A s ∣ N ↔ (Icc 1 ((s + 1) / 2)).lcm id ∣ N := by
    intro N
    rw [antiLcm, Finset.lcm_dvd_iff, Finset.lcm_dvd_iff]
    have e1 : (∀ m ∈ (range s).filter (fun m => m < s - m), (A m (s - m)).den ∣ N) ↔
        ∀ m, m < s - m → IsZ (N * V w m (s - 2 * m)) := by
      constructor
      · intro h m hm
        rw [← hA m hm, ← den_dvd_iff]
        exact h m (mem_filter.mpr ⟨mem_range.mpr (by omega), hm⟩)
      · intro h m hm
        have hm' := (mem_filter.mp hm).2
        rw [den_dvd_iff, hA m hm']
        exact h m hm'
    rw [e1, clear_iff]
    constructor
    · intro h i hi
      obtain ⟨h1, h2⟩ := mem_Icc.mp hi
      have := (hw (i - 1) N).mp (h (i - 1) (by omega))
      rwa [show i - 1 + 1 = i by omega] at this
    · intro h k hk
      exact (hw k N).mpr (h (k + 1) (mem_Icc.mpr ⟨by omega, by omega⟩))
  exact Nat.dvd_antisymm ((H _).2 dvd_rfl) ((H _).1 dvd_rfl)

/-- Corollary 11: for both zero-diagonal arrays `B` (signed seed) and `U` (unsigned seed), the
lcm of the reduced denominators on the strict upper antidiagonal `m + n = s` is
`lcm(1, …, ⌊(s + 1) / 2⌋) = A139550(s + 1)`, with the empty lcm equal to one. -/
theorem result (s : ℕ) :
    antiLcm B s = (Icc 1 ((s + 1) / 2)).lcm id ∧
    antiLcm U s = (Icc 1 ((s + 1) / 2)).lcm id ∧
    (Icc 1 ((s + 1) / 2)).lcm id = A139550 (s + 1) := by
  refine ⟨antiLcm_eq B (fun k => (-1) ^ k / (k + 1)) s (fun m hm => ?_)
      (fun k N => seed_iff _ (neg_one_pow_eq_or ℚ k) k N),
    antiLcm_eq U (fun k => 1 / (k + 1)) s (fun m hm => ?_)
      (fun k N => seed_iff 1 (Or.inl rfl) k N), rfl⟩
  · rw [show s - m = m + (s - 2 * m) by omega, OEISA189733Reflection.result.1, triangle_eq_V]
  · rw [show s - m = m + (s - 2 * m) by omega, OEISA242926UnsignedLucasRow.result.1, Ut_eq_V]

end D5.S1.Recurrence.Residue.OEISA242926AntidiagonalLcm
