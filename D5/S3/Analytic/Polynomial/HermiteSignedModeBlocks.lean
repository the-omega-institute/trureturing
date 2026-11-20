/- GID: D5/S3/Analytic/Polynomial/HermiteSignedModeBlocks
   generality: G
   mirror-B: D5/B/S3/Analytic/Polynomial/HermiteSignedModeBlocks
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Sqrt]
   utility: none
   digest: Block structure of the signed Hermite mode differences and its square-root growth. -/

import D5.S3.Analytic.Polynomial.HermiteSignedModeThreshold
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! The differences of the signed Hermite mode form blocks `(1,1,1,-3)` and `(1,1,1,1,-3)`.

admission_basis: escape-witness. proof_shape: content for le_mode_iff_start, diff_neg_three_iff,
offset_step, five_iff, alpha_bounds, ratio_limit and result. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.Polynomial.HermiteSignedModeBlocks

open Finset
open D5.S3.Analytic.Polynomial.HermiteSignedMode

/-- `G(j) = j² + 5j + 7`. -/
def G (j : ℕ) : ℕ := j ^ 2 + 5 * j + 7

private theorem exists_offset (r : ℕ) : ∃ j, 8 * r ≤ G j := ⟨8 * r, by unfold G; nlinarith⟩

/-- `j_r = min {j : j² + 5j + 7 ≥ 8r}`. -/
noncomputable def blockOffset (r : ℕ) : ℕ := Nat.find (exists_offset r)

/-- `n_r = 4r + j_r`, the first degree with mode index `r` (`n_0 = 0`). -/
noncomputable def blockStart (r : ℕ) : ℕ := 4 * r + blockOffset r

private theorem G_mono {i j : ℕ} (h : i ≤ j) : G i ≤ G j := by
  unfold G; have := Nat.pow_le_pow_left h 2; omega

private theorem offset_le_iff (r j : ℕ) : blockOffset r ≤ j ↔ 8 * r ≤ G j := by
  constructor
  · intro h; exact (Nat.find_spec (exists_offset r)).trans (G_mono h)
  · intro h; exact Nat.find_min' _ h

private theorem mode_le (n : ℕ) : 4 * mode n ≤ n := (mode_rises n).1

private theorem le_mode_iff (n r : ℕ) : r ≤ mode n ↔ 4 * r ≤ n ∧ 8 * r ≤ G (n - 4 * r) := by
  have hth := (D5.S3.Analytic.Polynomial.HermiteSignedModeThreshold.result.2.1 n).2
  have hm := mode_le n
  constructor
  · intro h
    refine ⟨by omega, ?_⟩
    have := (hth (n - 4 * r) (by omega)).1 (by simp only [a]; omega)
    unfold G
    obtain ⟨j, hj⟩ : ∃ j, n - 4 * r = j := ⟨_, rfl⟩
    rw [hj] at this ⊢
    have : n = j + 4 * r := by omega
    subst this
    nlinarith
  · rintro ⟨h4, hG⟩
    obtain ⟨j, hj⟩ : ∃ j, n - 4 * r = j := ⟨_, rfl⟩
    rw [hj] at hG
    have hn : n = j + 4 * r := by omega
    have hF : 2 * n ≤ j ^ 2 + 7 * j + 7 := by unfold G at hG; subst hn; nlinarith
    have := (hth j (by omega)).2 hF
    simp only [a] at this
    omega

private theorem le_mode_iff_start (n r : ℕ) : r ≤ mode n ↔ blockStart r ≤ n := by
  rw [le_mode_iff, blockStart]
  constructor
  · rintro ⟨h4, hG⟩
    have := (offset_le_iff r _).2 hG
    omega
  · intro h
    exact ⟨by omega, (offset_le_iff r _).1 (by omega)⟩

private theorem mode_step (n : ℕ) : mode n ≤ mode (n + 1) ∧ mode (n + 1) ≤ mode n + 1 := by
  have h := result.2 n
  have h1 := mode_le n
  have h2 := mode_le (n + 1)
  simp only [a] at h
  push_cast [h1, h2] at h
  omega

private theorem diff_neg_three_iff (n : ℕ) :
    (a (n + 1) : ℤ) - a n = -3 ↔ ∃ r, 1 ≤ r ∧ blockStart r = n + 1 := by
  have hs := mode_step n
  have h1 := mode_le n
  have h2 := mode_le (n + 1)
  have hd : (a (n + 1) : ℤ) - a n = 1 - 4 * ((mode (n + 1) : ℤ) - mode n) := by
    simp only [a]; push_cast [h1, h2]; ring
  rw [hd]
  constructor
  · intro h
    have he : mode (n + 1) = mode n + 1 := by omega
    refine ⟨mode (n + 1), by omega, ?_⟩
    have hle := (le_mode_iff_start (n + 1) (mode (n + 1))).1 le_rfl
    have hgt : ¬ blockStart (mode (n + 1)) ≤ n := fun h => by
      have := (le_mode_iff_start n _).2 h; omega
    omega
  · rintro ⟨r, hr, hb⟩
    have hle := (le_mode_iff_start (n + 1) r).2 (le_of_eq hb)
    have hgt : ¬ r ≤ mode n := fun h => by
      have := (le_mode_iff_start n r).1 h; omega
    omega

private theorem offset_one : blockOffset 1 = 1 := by
  apply le_antisymm
  · exact (offset_le_iff 1 1).2 (by decide)
  · by_contra h
    push Not at h
    have := (offset_le_iff 1 0).1 (by omega)
    simp [G] at this

private theorem offset_pos (r : ℕ) (hr : 1 ≤ r) : 1 ≤ blockOffset r := by
  by_contra h
  push Not at h
  have := (offset_le_iff r 0).1 (by omega)
  simp [G] at this
  omega

private theorem offset_step (r : ℕ) (hr : 1 ≤ r) :
    blockOffset r ≤ blockOffset (r + 1) ∧ blockOffset (r + 1) ≤ blockOffset r + 1 := by
  have hj := (offset_le_iff r (blockOffset r)).1 le_rfl
  have hj1 := (offset_le_iff (r + 1) (blockOffset (r + 1))).1 le_rfl
  have hp := offset_pos r hr
  constructor
  · exact (offset_le_iff r _).2 (by omega)
  · apply (offset_le_iff (r + 1) _).2
    unfold G at hj ⊢
    nlinarith

private theorem start_step (r : ℕ) (hr : 1 ≤ r) :
    blockStart (r + 1) = blockStart r + 4 ∨ blockStart (r + 1) = blockStart r + 5 := by
  have := offset_step r hr
  unfold blockStart
  omega

/-- `R_j = ⌊(j² + 5j + 7)/8⌋`. -/
def R (j : ℕ) : ℕ := G j / 8

private theorem offset_R (j : ℕ) (hj : 1 ≤ j) : blockOffset (R j) = j := by
  apply le_antisymm
  · exact (offset_le_iff _ _).2 (by unfold R; omega)
  · by_contra h
    push Not at h
    have h1 := (offset_le_iff (R j) (j - 1)).1 (by omega)
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp [R, G] at h1
    · have h2 : G i + 8 ≤ G (i + 1) := by simp only [G]; nlinarith
      simp only [Nat.add_sub_cancel] at h1
      unfold R at h1
      have : 8 * (G (i + 1) / 8) ≤ G (i + 1) := Nat.mul_div_le _ _
      omega

private theorem R_pos (j : ℕ) (hj : 1 ≤ j) : 1 ≤ R j := by
  unfold R G; have : 13 ≤ j ^ 2 + 5 * j + 7 := by nlinarith
  omega

private theorem five_iff (r : ℕ) (hr : 1 ≤ r) :
    blockStart (r + 1) = blockStart r + 5 ↔ ∃ j, 1 ≤ j ∧ r = R j := by
  have hs := offset_step r hr
  unfold blockStart
  constructor
  · intro h
    have he : blockOffset (r + 1) = blockOffset r + 1 := by omega
    refine ⟨blockOffset r, offset_pos r hr, ?_⟩
    have hj := (offset_le_iff r (blockOffset r)).1 le_rfl
    have hnot : ¬ 8 * (r + 1) ≤ G (blockOffset r) := fun h => by
      have := (offset_le_iff (r + 1) _).2 h; omega
    unfold R; omega
  · rintro ⟨j, hj, rfl⟩
    rw [offset_R j hj]
    have hnot : ¬ 8 * (R j + 1) ≤ G j := by unfold R; omega
    have hne : blockOffset (R j + 1) ≠ j := fun h => by
      have := (offset_le_iff (R j + 1) j).1 (le_of_eq h); exact hnot this
    have := offset_step (R j) (R_pos j hj)
    rw [offset_R j hj] at this
    omega

private theorem start_R (j : ℕ) (hj : 1 ≤ j) : blockStart (R j) = 4 * R j + j := by
  unfold blockStart; rw [offset_R j hj]

/-- `α_n = (√(8n + 21) - 7)/2`. -/
noncomputable def alpha (n : ℕ) : ℝ := (√(8 * n + 21) - 7) / 2

private theorem alpha_bounds (n : ℕ) : alpha n ≤ a n ∧ (a n : ℝ) < alpha n + 4 := by
  have hth := (D5.S3.Analytic.Polynomial.HermiteSignedModeThreshold.result.2.1 n)
  have hF : 2 * n ≤ a n ^ 2 + 7 * a n + 7 := (hth.2 (a n) hth.1).1 le_rfl
  have han : a n ≤ n := Nat.sub_le _ _
  set s := √(8 * (n : ℝ) + 21) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hsq : s ^ 2 = 8 * n + 21 := Real.sq_sqrt (by positivity)
  unfold alpha
  rw [← hs]
  constructor
  · have hFr : (2 * n : ℝ) ≤ a n ^ 2 + 7 * a n + 7 := by exact_mod_cast hF
    have : s ≤ 2 * a n + 7 := by
      by_contra h; push Not at h; nlinarith
    linarith
  · have : 2 * (a n : ℝ) - 1 < s := by
      rcases Nat.lt_or_ge (a n) 4 with h4 | h4
      · have hr : (a n : ℝ) ≤ 3 := by exact_mod_cast (show a n ≤ 3 by omega)
        have hnr : (a n : ℝ) ≤ n := by exact_mod_cast han
        have h0 : (0 : ℝ) ≤ a n := by positivity
        by_contra h; push Not at h; nlinarith
      · have hnot : ¬ 2 * n ≤ (a n - 4) ^ 2 + 7 * (a n - 4) + 7 := fun h => by
          have := (hth.2 (a n - 4) (by omega)).2 h; omega
        push Not at hnot
        obtain ⟨i, hi⟩ : ∃ i, a n = i + 4 := ⟨a n - 4, by omega⟩
        rw [hi, Nat.add_sub_cancel] at hnot
        have hr : ((i : ℝ) ^ 2 + 7 * i + 7) < 2 * n := by exact_mod_cast hnot
        have hai : (a n : ℝ) = i + 4 := by exact_mod_cast hi
        by_contra h; push Not at h; nlinarith
    linarith

private theorem R_mono {i j : ℕ} (h : i ≤ j) : R i ≤ R j := Nat.div_le_div_right (G_mono h)

private theorem bs1 : blockStart 1 = 5 := by unfold blockStart; rw [offset_one]
private theorem bs0 : blockStart 0 = 0 := by simp [blockStart, blockOffset, G]

private theorem start_step' (r : ℕ) :
    blockStart (r + 1) = blockStart r + 4 ∨ blockStart (r + 1) = blockStart r + 5 := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · right; show blockStart 1 = blockStart 0 + 5; rw [bs1, bs0]
  · exact start_step r hr

private theorem five_iff' (r : ℕ) : blockStart (r + 1) = blockStart r + 5 ↔ ∃ j, r = R j := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · show blockStart 1 = blockStart 0 + 5 ↔ _
    rw [bs1, bs0]; exact ⟨fun _ => ⟨0, by simp [R, G]⟩, fun _ => rfl⟩
  · rw [five_iff r hr]
    constructor
    · rintro ⟨j, -, h⟩; exact ⟨j, h⟩
    · rintro ⟨j, h⟩
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · simp [R, G] at h; omega
      · exact ⟨j, hj, h⟩

private theorem start_R' (j : ℕ) : blockStart (R j) = 4 * R j + j := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [R, G, bs0]
  · exact start_R j hj

private theorem count_nat (j : ℕ) :
    8 * R j + 8 + 2 * j ≤ 8 * R (j + 1) + 6 ∧ 8 * R (j + 1) ≤ 8 * R j + 8 + 2 * j + 2 := by
  obtain ⟨q, s, hs, rfl⟩ : ∃ q s, s < 8 ∧ j = 8 * q + s :=
    ⟨j / 8, j % 8, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod j 8).symm⟩
  have key : ∀ t, G (8 * q + t) = 8 * (8 * q ^ 2 + 2 * q * t + 5 * q) + G t := by
    intro t; unfold G; ring
  have k1 := key s
  have k2 := key (s + 1)
  rw [show 8 * q + s + 1 = 8 * q + (s + 1) by ring]
  unfold R
  rw [k1, k2]
  have hu : 8 * q ^ 2 + 2 * q * (s + 1) + 5 * q = (8 * q ^ 2 + 2 * q * s + 5 * q) + 2 * q := by ring
  rw [hu]
  generalize 8 * q ^ 2 + 2 * q * s + 5 * q = u
  have : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [G] <;> omega

private theorem count_exact (j : ℕ) :
    -3 / 4 ≤ ((R (j + 1) : ℝ) - R j - 1) - j / 4 ∧ ((R (j + 1) : ℝ) - R j - 1) - j / 4 ≤ 1 / 4 := by
  obtain ⟨h1, h2⟩ := count_nat j
  have e1 : (8 * R j + 8 + 2 * j : ℝ) ≤ 8 * R (j + 1) + 6 := by exact_mod_cast h1
  have e2 : (8 * R (j + 1) : ℝ) ≤ 8 * R j + 8 + 2 * j + 2 := by exact_mod_cast h2
  constructor <;> linarith

private theorem sqrt_strict (n : ℕ) : -(7 / 2 : ℝ) < (a n : ℝ) - √(2 * n) ∧ (a n : ℝ) - √(2 * n) < 3 := by
  obtain ⟨hl, hu⟩ := alpha_bounds n
  unfold alpha at hl hu
  set s := √(8 * (n : ℝ) + 21)
  set t := √(2 * (n : ℝ))
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have hsq : s ^ 2 = 8 * n + 21 := Real.sq_sqrt (by positivity)
  have htq : t ^ 2 = 2 * n := Real.sq_sqrt (by positivity)
  have hlow : 2 * t < s := by
    by_contra h; push Not at h; nlinarith
  have hup : s ≤ 2 * t + 5 := by
    by_contra h; push Not at h; nlinarith
  constructor <;> linarith

private theorem ratio_limit :
    Filter.Tendsto (fun n : ℕ => (a n : ℝ) / √(2 * n)) Filter.atTop (nhds 1) := by
  have ht : Filter.Tendsto (fun n : ℕ => √(2 * (n : ℝ))) Filter.atTop Filter.atTop :=
    Real.tendsto_sqrt_atTop.comp
      (Filter.Tendsto.const_mul_atTop (by norm_num) tendsto_natCast_atTop_atTop)
  have hz : Filter.Tendsto (fun n : ℕ => (7 / 2 : ℝ) / √(2 * n)) Filter.atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop ht
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Filter.Eventually.of_forall fun n => norm_nonneg _) ?_ hz
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hpos : 0 < √(2 * (n : ℝ)) := Real.sqrt_pos.2 (by positivity)
  rw [Real.norm_eq_abs, show (a n : ℝ) / √(2 * n) - 1 = ((a n : ℝ) - √(2 * n)) / √(2 * n) by
    field_simp, abs_div, abs_of_pos hpos]
  have hb := sqrt_strict n
  exact div_le_div_of_nonneg_right (abs_le.2 ⟨by linarith [hb.1], by linarith [hb.2]⟩) hpos.le

private theorem four_between (j r : ℕ) (h1 : R j < r) (h2 : r < R (j + 1)) :
    blockStart (r + 1) = blockStart r + 4 := by
  rcases start_step' r with h | h
  · exact h
  · obtain ⟨i, rfl⟩ := (five_iff' r).1 h
    rcases Nat.lt_or_ge j i with hji | hji
    · have := R_mono (show j + 1 ≤ i by omega); omega
    · have := R_mono hji; omega

private theorem diff_neg_three_iff' (n : ℕ) :
    (a (n + 1) : ℤ) - a n = -3 ↔ ∃ r, blockStart r = n + 1 := by
  rw [diff_neg_three_iff]
  constructor
  · rintro ⟨r, -, h⟩; exact ⟨r, h⟩
  · rintro ⟨r, h⟩
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · rw [bs0] at h; omega
    · exact ⟨r, hr, h⟩

/-- Corollary 2 of Ma and Zhang on OEIS A381423, with `q(n) = mode n = (n - a n)/4`: `q(n) ≥ r`
exactly when `n ≥ n_r`; `a(n+1) - a(n) = -3` exactly when `n + 1` is a block start `n_r`; the block
starts satisfy `n_0 = 0`, `n_1 = 5` and `n_{r+1} - n_r ∈ {4, 5}`, with gap five exactly at
`r = R_j = ⌊(j² + 5j + 7)/8⌋` (the first block is `R_0 = 0`), `n_{R_j} = 4R_j + j`, and gap four
strictly between consecutive `R_j`; `R_{j+1} - R_j - 1 - j/4 ∈ [-3/4, 1/4]`; finally
`α_n ≤ a(n) < α_n + 4`, `-7/2 < a(n) - √(2n) < 3` and `a(n)/√(2n) → 1`. -/
theorem result :
    (∀ n r : ℕ, r ≤ mode n ↔ blockStart r ≤ n) ∧
    (∀ n : ℕ, (a (n + 1) : ℤ) - a n = -3 ↔ ∃ r, blockStart r = n + 1) ∧
    blockStart 0 = 0 ∧ blockStart 1 = 5 ∧
    (∀ r : ℕ, blockStart (r + 1) = blockStart r + 4 ∨ blockStart (r + 1) = blockStart r + 5) ∧
    (∀ r : ℕ, blockStart (r + 1) = blockStart r + 5 ↔ ∃ j, r = R j) ∧
    (∀ j : ℕ, blockStart (R j) = 4 * R j + j) ∧
    (∀ j r : ℕ, R j < r → r < R (j + 1) → blockStart (r + 1) = blockStart r + 4) ∧
    (∀ j : ℕ, -3 / 4 ≤ ((R (j + 1) : ℝ) - R j - 1) - j / 4 ∧
      ((R (j + 1) : ℝ) - R j - 1) - j / 4 ≤ 1 / 4) ∧
    (∀ n : ℕ, alpha n ≤ a n ∧ (a n : ℝ) < alpha n + 4) ∧
    (∀ n : ℕ, -(7 / 2 : ℝ) < (a n : ℝ) - √(2 * n) ∧ (a n : ℝ) - √(2 * n) < 3) ∧
    Filter.Tendsto (fun n : ℕ => (a n : ℝ) / √(2 * n)) Filter.atTop (nhds 1) :=
  ⟨le_mode_iff_start, diff_neg_three_iff', bs0, bs1, start_step', five_iff', start_R', four_between,
    count_exact, alpha_bounds, sqrt_strict, ratio_limit⟩

end D5.S3.Analytic.Polynomial.HermiteSignedModeBlocks
