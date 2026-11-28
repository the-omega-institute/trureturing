import OmegaBuild.Commands
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Indicator
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Transfer of a scalar triangle profile along a predecessor suffix -/

compile_only_with_mathlib

open scoped BigOperators

namespace HilbertWeightedTransfer

private theorem capShift_mem {d z : ℝ} (hd : 0 ≤ d) (hz : -1 ≤ z) :
    -1 ≤ min 1 (z + d) ∧ min 1 (z + d) ≤ 1 :=
  ⟨le_min (by norm_num) (by linarith), min_le_left _ _⟩

private theorem capShift_dist_sq (d y z : ℝ) :
    (min 1 (y + d) - min 1 (z + d)) ^ 2 ≤ (y - z) ^ 2 := by
  by_cases hy : y + d ≤ 1 <;> by_cases hz : z + d ≤ 1
  · rw [min_eq_right hy, min_eq_right hz]
    ring_nf; rfl
  · rw [min_eq_right hy, min_eq_left (le_of_not_ge hz)]
    nlinarith [mul_nonneg (show 0 ≤ z + d - 1 by linarith)
      (show 0 ≤ 1 + z - 2 * y - d by linarith)]
  · rw [min_eq_left (le_of_not_ge hy), min_eq_right hz]
    nlinarith [mul_nonneg (show 0 ≤ y + d - 1 by linarith)
      (show 0 ≤ 1 + y - 2 * z - d by linarith)]
  · rw [min_eq_left (le_of_not_ge hy), min_eq_left (le_of_not_ge hz)]
    simpa using sq_nonneg (y - z)

private theorem capShift_mean_sq {a e l z : ℝ}
    (ha : 1 / 2 ≤ a) (he : 0 ≤ e) (hl : l ≤ 2 * a) (hz : z ≤ 1 - e / 2) :
    (min 1 (z + a * e) - l) ^ 2 ≤
      (z + a * e - l) ^ 2 + 2 * (2 * a - 1) * (a - 1 / 2) * e := by
  by_cases h : z + a * e ≤ 1
  · rw [min_eq_right h]
    exact le_add_of_nonneg_right (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by linarith)) he)
  · rw [min_eq_left (le_of_not_ge h)]
    let s := z + a * e - 1
    have hs : 0 ≤ s := by dsimp [s]; linarith
    have hs' : s ≤ (a - 1 / 2) * e := by dsimp [s]; nlinarith
    have h1 := mul_nonneg hs (show 0 ≤ 2 * a - l by linarith)
    have h2 := mul_nonneg (show 0 ≤ 2 * a - 1 by linarith) (sub_nonneg.mpr hs')
    have hsdef : z + a * e - l = 1 - l + s := by dsimp [s]; ring
    rw [hsdef]
    nlinarith [sq_nonneg s]

private theorem capShift_le {d y : ℝ} (hd : 0 ≤ d) (hy : y ≤ 1) :
    0 ≤ min 1 (y + d) - y ∧ min 1 (y + d) - y ≤ d :=
  ⟨sub_nonneg.mpr (le_min hy (by linarith)),
    sub_le_iff_le_add.mpr (by simpa [add_comm] using (min_le_right (1 : ℝ) (y + d)))⟩

/-- A new pair row is paid for by the mean shift, the suffix fluctuation,
the companion deficits, and a scalar bound for the suffix mass. -/
theorem suffix_transfer {ι : Type*} (S : Finset ι) (p y d' : ι → ℝ)
    (hp : ∀ k ∈ S, 0 ≤ p k) (hd' : ∀ k ∈ S, 0 ≤ d' k)
    (F B : ℝ → ℝ) (a r lam ν₀ ν₁ w L : ℝ)
    (ha : 1 / 2 ≤ a) (hr : 0 < r)
    (hlam : 0 ≤ lam) (hν₀ : 0 ≤ ν₀) (hν₁ : 0 ≤ ν₁) (hw : 0 ≤ w) (hL : 0 ≤ L)
    (hbudget : lam * w + (2 * ν₀ * (2 * a - 1) * (a - 1 / 2) + a * lam * L) / r ≤ w)
    (hLip : ∀ u v : ℝ, -1 ≤ u → u ≤ v → v ≤ 1 → F v ≤ F u + L * (v - u))
    (d t z : ℝ) (hd : 0 ≤ d) (ht₀ : -1 ≤ t) (ht₁ : t ≤ 1)
    (hz₀ : -1 ≤ z) (hz₁ : z ≤ 1 - d / (2 * r))
    (hy : ∀ k ∈ S, -1 ≤ y k ∧ y k ≤ 1)
    (hF : ∀ k ∈ S, F (y k) ≤ d' k + w * d)
    (hθ : (∑ k ∈ S, p k) ≤ 1)
    (hB : ∀ z' y' : ℝ, -1 ≤ z' → z' ≤ 1 → -1 ≤ y' → y' ≤ 1 →
      F t ≤ B (∑ k ∈ S, p k) + ν₀ * (z' - a * (1 + t)) ^ 2 +
        (∑ k ∈ S, p k) * (ν₁ * (y' - z') ^ 2 + lam * F y')) :
    F t - w * d ≤ B (∑ k ∈ S, p k) +
      ν₀ * (z + a * (d / r) - a * (1 + t)) ^ 2 +
        ∑ k ∈ S, p k * (ν₁ * (y k - z) ^ 2 + lam * d' k) := by
  let θ := ∑ k ∈ S, p k
  let l := a * (1 + t)
  let e := d / r
  let C := B θ + ν₀ * (z + a * e - l) ^ 2
  let z' := min 1 (z + a * e)
  have he : 0 ≤ e := div_nonneg hd hr.le
  have ha' : 0 ≤ a := by linarith
  have hδ := mul_nonneg ha' he
  have hθ₀ : 0 ≤ θ := Finset.sum_nonneg hp
  have hθ₁ : θ ≤ 1 := hθ
  have hl : l ≤ 2 * a := by dsimp [l]; nlinarith
  have hzd : z ≤ 1 - e / 2 := by
    simpa only [e, div_div, mul_comm r] using hz₁
  have hzm := capShift_mem hδ hz₀
  have hmean := mul_le_mul_of_nonneg_left (capShift_mean_sq ha he hl hzd) hν₀
  have hcharge : ν₀ * (2 * (2 * a - 1) * (a - 1 / 2) * e) +
      (lam * w * d + lam * L * (a * e)) ≤ w * d := by
    have h := mul_le_mul_of_nonneg_right hbudget hd
    have hprod : e * r = d := div_mul_cancel₀ d hr.ne'
    calc
      _ = (lam * w + (2 * ν₀ * (2 * a - 1) * (a - 1 / 2) + a * lam * L) / r) * d := by
        dsimp [e]
        ring
      _ ≤ _ := h
  change F t - w * d ≤ C + ∑ k ∈ S, p k * (ν₁ * (y k - z) ^ 2 + lam * d' k)
  rcases eq_or_lt_of_le hθ₀ with hzero | hpos
  · have htrial := hB z' z' hzm.1 hzm.2 hzm.1 hzm.2
    have htrial' : F t ≤ B θ + ν₀ * (z' - l) ^ 2 := by
      change F t ≤ B θ + ν₀ * (z' - l) ^ 2 + θ * _ at htrial
      simpa only [← hzero, zero_mul, add_zero] using htrial
    have hs : 0 ≤ ∑ k ∈ S, p k * (ν₁ * (y k - z) ^ 2 + lam * d' k) :=
      Finset.sum_nonneg fun k hk => mul_nonneg (hp k hk)
        (add_nonneg (mul_nonneg hν₁ (sq_nonneg _)) (mul_nonneg hlam (hd' k hk)))
    dsimp [C, z'] at *
    nlinarith [mul_nonneg (mul_nonneg hlam hw) hd, mul_nonneg (mul_nonneg hlam hL) hδ]
  · have htrial (k : ι) (hk : k ∈ S) :
        F t - w * d - C ≤ θ * (ν₁ * (y k - z) ^ 2 + lam * d' k) := by
      let y' := min 1 (y k + a * e)
      have hym := capShift_mem hδ (hy k hk).1
      have hf := hB z' y' hzm.1 hzm.2 hym.1 hym.2
      change F t ≤ B θ + ν₀ * (z' - l) ^ 2 +
        θ * (ν₁ * (y' - z') ^ 2 + lam * F y') at hf
      have hm := capShift_le hδ (hy k hk).2
      have hDy := mul_le_mul_of_nonneg_left (capShift_dist_sq (a * e) (y k) z) hν₁
      have hFy : F y' ≤ d' k + w * d + L * (a * e) :=
        (hLip (y k) y' (hy k hk).1 (by linarith [hm.1]) hym.2).trans (by
          linarith [hF k hk, mul_le_mul_of_nonneg_left hm.2 hL])
      have hlamFy := mul_le_mul_of_nonneg_left hFy hlam
      have hbound := mul_le_mul_of_nonneg_left (add_le_add hDy hlamFy) hθ₀
      have hc := mul_le_of_le_one_left
        (add_nonneg (mul_nonneg (mul_nonneg hlam hw) hd) (mul_nonneg (mul_nonneg hlam hL) hδ)) hθ₁
      dsimp [C, z', y'] at *
      nlinarith
    have hs : ∑ k ∈ S, p k * (F t - w * d - C) ≤
        ∑ k ∈ S, p k * (θ * (ν₁ * (y k - z) ^ 2 + lam * d' k)) :=
      Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_left (htrial k hk) (hp k hk)
    simp_rw [show ∀ k, p k * (θ * (ν₁ * (y k - z) ^ 2 + lam * d' k)) =
      θ * (p k * (ν₁ * (y k - z) ^ 2 + lam * d' k)) by intro; ring,
      ← Finset.mul_sum, ← Finset.sum_mul] at hs
    change θ * (F t - w * d - C) ≤ _ at hs
    linarith [le_of_mul_le_mul_left hs hpos]

end HilbertWeightedTransfer
