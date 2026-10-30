/- GID: D5/S3/Combinatorics/Circle/ThreeNegativeCommonCut
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/ThreeNegativeCommonCut
   mirror-E: none(waiver:no-escape-mirror-specified)
   anchors: [mathlib/module/Mathlib.Data.Int.ModEq, mathlib/module/Mathlib.Combinatorics.Colex]
   utility: none
   digest: One physical W mask constructs both native three-negative orders at the same zero cut. -/
import D5.S3.Combinatorics.Circle.RunFirstEarTransport
import D5.S3.Combinatorics.Circle.DyadicPrefix

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace D5.S3.Combinatorics.Circle.ThreeNegativeCommonCut
open SourceWidth PeriodicShortening
open scoped BigOperators

private theorem pow_lower (n : ℕ) (hn : 2 ≤ n) : (4 : ℤ) ≤ 2 ^ n := by
  have := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) hn
  norm_num at this
  exact this

private theorem pow_half (n : ℕ) (hn : 0 < n) :
    (2 : ℤ) ^ n = 2 * 2 ^ (n - 1) := by
  conv_lhs => rw [show n = (n - 1) + 1 by omega, pow_succ]
  ring

/-- A congruent ladder has precisely one final negative occurrence. -/
private theorem ladder_value (C p cap : ℤ) (len i : ℕ)
    (hC : 0 ≤ C) (hp : 0 < p) (hcap : 0 ≤ cap ∧ cap ≤ C)
    (hend : (2 : ℤ) ^ len * p = C + 1 + cap) (hi : i ≤ len) :
    centered (2 * C + 1) (2 ^ i * p) =
      if i < len then 2 ^ i * p else -C + cap := by
  have hN : 0 < 2 * C + 1 := by omega
  have ho : (2 * C + 1) % 2 = 1 := by omega
  have hh : (2 * C + 1) / 2 = C := by omega
  by_cases hil : i < len
  · rw [if_pos hil]
    have hhpow := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2)
      (show i + 1 ≤ len by omega)
    rw [pow_succ] at hhpow
    have hx := mul_le_mul_of_nonneg_right hhpow (le_of_lt hp)
    apply centered_unique hN ho (centered_bounds hN ho _) ?_ (centered_mod _ _)
    rw [hh]
    have hx0 : 0 ≤ (2 : ℤ) ^ i * p := by positivity
    constructor <;> nlinarith
  · have hei : i = len := by omega
    rw [if_neg hil, hei, hend]
    apply centered_unique hN ho (centered_bounds hN ho _) ?_ ?_
    · rw [hh]; constructor <;> omega
    · rw [centered_mod]
      have he : C + 1 + cap = (-C + cap) + (2 * C + 1) := by ring
      rw [he, Int.add_emod_right]

private theorem positive_strip {α : Type*} (f : α → ℤ) (l : List α) (C h : ℤ)
    (hpos : ∀ x ∈ l, 0 ≤ f x) (hh : 0 ≤ h) (hend : h + (l.map f).sum ≤ C) :
    InStrip f C h l := by
  apply inStrip_reflect
  apply inStrip_nonpos
  · intro x hx; exact neg_nonpos.mpr (hpos x hx)
  · omega
  · rw [sum_neg_map]; omega

/-- The native floor estimate includes the W-charge left behind at the seam. -/
private theorem mask_bound (t u m : ℤ) (hu : 4 ≤ u) (hm : m = 4 ∨ 8 ≤ m)
    (htu : t = m * u) :
    let H := t * u + t + 1
    let f := (t + 1) * (t - u) / H
    let h := (t + 1) * (t - u) - H * f
    0 ≤ f ∧ f ≤ m - 2 ∧ f < t / 2 ∧ 0 ≤ h ∧
      2 * h + 1 + (t + 1) * f ≤ t * (t + 1) / 2 := by
  dsimp only
  let H := t * u + t + 1
  let f := (t + 1) * (t - u) / H
  let h := (t + 1) * (t - u) - H * f
  change 0 ≤ f ∧ f ≤ m - 2 ∧ f < t / 2 ∧ 0 ≤ h ∧
    2 * h + 1 + (t + 1) * f ≤ t * (t + 1) / 2
  have hm4 : 4 ≤ m := by rcases hm with rfl | hm <;> omega
  have ht : 4 * u ≤ t := by nlinarith
  have ht0 : 0 ≤ t := by omega
  have hH : 0 < H := by dsimp [H]; positivity
  have hf0 : 0 ≤ f := Int.ediv_nonneg (mul_nonneg (by omega) (by omega)) (le_of_lt hH)
  have hr0 := Int.emod_nonneg ((t + 1) * (t - u)) (ne_of_gt hH)
  have hr1 := Int.emod_lt_of_pos ((t + 1) * (t - u)) hH
  have hre := Int.emod_add_mul_ediv ((t + 1) * (t - u)) H
  have hh0 : 0 ≤ h := by dsimp [h, f]; omega
  have hh1 : h ≤ H - 1 := by dsimp [h, f]; omega
  have hprod : (t + 1) * (t - u) < H * (m - 1) := by
    have hx : (t + 1) * (t - u) = (t + 1) * u * (m - 1) := by rw [htu]; ring
    rw [hx]
    have hgap : u * (t + 1) < H := by dsimp [H]; nlinarith
    nlinarith [mul_pos (by omega : 0 < m - 1) (by omega : 0 < H - u * (t + 1))]
  have hfm : f ≤ m - 2 := by
    have hmul : H * f ≤ (t + 1) * (t - u) := by dsimp [h] at hh0; omega
    by_contra hf
    have := mul_le_mul_of_nonneg_left (show m - 1 ≤ f by omega) (le_of_lt hH)
    omega
  have hfit : f < t / 2 := by
    have ht2 := Int.emod_add_mul_ediv t 2
    have htmod := Int.emod_lt_of_pos t (by norm_num : (0 : ℤ) < 2)
    nlinarith
  refine ⟨hf0, hfm, hfit, hh0, ?_⟩
  have hg := Int.emod_add_mul_ediv (t * (t + 1)) 2
  have hg0 := Int.emod_nonneg (t * (t + 1)) (by norm_num : (2 : ℤ) ≠ 0)
  have hg1 := Int.emod_lt_of_pos (t * (t + 1)) (by norm_num : (0 : ℤ) < 2)
  rcases hm with hm | hm
  · have ht4 : t = 4 * u := by rw [htu, hm]
    have htwo : 2 * H ≤ (t + 1) * (t - u) := by dsimp [H]; rw [ht4]; nlinarith
    have hf2 : 2 ≤ f := (Int.le_ediv_iff_mul_le hH).mpr (by nlinarith)
    have hfe : f = 2 := by omega
    dsimp [h, H]
    rw [hfe, ht4]
    rw [ht4] at hg hg0 hg1
    nlinarith
  · have ht8 : 8 * u ≤ t := by nlinarith
    have hq : 2 * h + 1 + (t + 1) * f ≤ 2 * t * u + (t + 1) * m - 1 := by
      have hf := mul_le_mul_of_nonneg_left hfm (show 0 ≤ t + 1 by omega)
      dsimp [H] at hh1
      nlinarith
    have hmterm : 4 * ((t + 1) * m) ≤ t * (t + 1) := by
      have hu4 := mul_nonneg (show 0 ≤ u - 4 by omega) (show 0 ≤ m * (t + 1) by positivity)
      nlinarith [show m * u = t by omega]
    have htuterm : 8 * t * u ≤ t * (t + 1) := by
      nlinarith [mul_nonneg ht0 (show 0 ≤ t + 1 - 8 * u by omega)]
    omega

end D5.S3.Combinatorics.Circle.ThreeNegativeCommonCut
