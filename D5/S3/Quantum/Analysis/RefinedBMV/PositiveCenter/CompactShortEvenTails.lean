/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/CompactShortEvenTails
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Geometric bounds for the hyperbolic tails in the midpoint expansion of the joint term. -/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Hyperbolic remainders and conditional even moments for the short-gap bound. -/

namespace RefinedBMV.PositiveCenter

private theorem factorial_stride_lower (start n : ℕ) :
    start.factorial * ((start + 1) * (start + 2)) ^ n ≤ (start + 2 * n).factorial := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hstep : (start + 1) * (start + 2) ≤
        (start + 2 * n + 1) * (start + 2 * n + 2) :=
      Nat.mul_le_mul (by omega) (by omega)
    calc
      _ = (start.factorial * ((start + 1) * (start + 2)) ^ n) *
          ((start + 1) * (start + 2)) := by rw [pow_succ, mul_assoc]
      _ ≤ (start + 2 * n).factorial * ((start + 2 * n + 1) * (start + 2 * n + 2)) :=
        Nat.mul_le_mul ih hstep
      _ = _ := by
        rw [show start + 2 * (n + 1) = (start + 2 * n + 1) + 1 by omega,
          Nat.factorial_succ (start + 2 * n + 1), Nat.factorial_succ (start + 2 * n)]
        ring

private theorem stride_tail_bound (start : ℕ) {x radius : ℝ} (hx : 0 ≤ x) (hxr : x ≤ radius)
    (hr : radius ^ 2 / (↑((start + 1) * (start + 2) : ℕ) : ℝ) < 1)
    (htail : Summable (fun n : ℕ ↦ x ^ (start + 2 * n) / ((start + 2 * n).factorial : ℝ))) :
    (∑' n : ℕ, x ^ (start + 2 * n) / ((start + 2 * n).factorial : ℝ)) ≤
      x ^ start / (start.factorial : ℝ) / (1 - radius ^ 2 / ↑((start + 1) * (start + 2) : ℕ)) := by
  let step : ℝ := ↑((start + 1) * (start + 2) : ℕ)
  let ratio := radius ^ 2 / step
  let leading := x ^ start / (start.factorial : ℝ)
  have hstep : 0 < step := by dsimp [step]; positivity
  have hratio : 0 ≤ ratio := div_nonneg (sq_nonneg _) hstep.le
  have hgeo := (hasSum_geometric_of_lt_one hratio hr).mul_left leading
  change _ ≤ leading / (1 - ratio)
  rw [div_eq_mul_inv leading (1 - ratio), ← hgeo.tsum_eq]
  apply htail.tsum_le_tsum _ hgeo.summable
  intro n
  have hfac : (start.factorial : ℝ) * step ^ n ≤ ((start + 2 * n).factorial : ℝ) := by
    dsimp only [step]
    exact_mod_cast factorial_stride_lower start n
  have hrad := hx.trans hxr
  have hpow : (x ^ 2) ^ n ≤ (radius ^ 2) ^ n := by gcongr
  calc
    _ ≤ x ^ (start + 2 * n) / ((start.factorial : ℝ) * step ^ n) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hfac
    _ = leading * ((x ^ 2) ^ n / step ^ n) := by
      rw [pow_add, pow_mul]
      dsimp [leading]
      ring
    _ ≤ leading * ratio ^ n := by
      dsimp [ratio]
      rw [div_pow]
      gcongr

/-- The Taylor remainder above degree four is nonnegative and bounded by a geometric series. -/
theorem short_cosh_fourth_tail {x radius : ℝ} (hx : 0 ≤ x) (hxr : x ≤ radius)
    (hr : radius ^ 2 / 56 < 1) :
    let error := Real.cosh x - (1 + x ^ 2 / 2 + x ^ 4 / 24)
    0 ≤ error ∧ error ≤ x ^ 6 / 720 / (1 - radius ^ 2 / 56) := by
  let f (n : ℕ) := x ^ (2 * n) / ((2 * n).factorial : ℝ)
  have hf : HasSum f (Real.cosh x) := Real.hasSum_cosh x
  have hshift (n : ℕ) : f (n + 3) = x ^ (6 + 2 * n) / ((6 + 2 * n).factorial : ℝ) := by
    unfold f
    rw [show 2 * (n + 3) = 6 + 2 * n by omega]
  have hsum := (summable_nat_add_iff 3).2 hf.summable
  simp_rw [hshift] at hsum
  have hprefix : (∑ n ∈ Finset.range 3, f n) = 1 + x ^ 2 / 2 + x ^ 4 / 24 := by
    norm_num [f, Finset.sum_range_succ, Nat.factorial]
  have heq := hf.summable.sum_add_tsum_nat_add 3
  simp_rw [hprefix, hshift, hf.tsum_eq] at heq
  change 0 ≤ Real.cosh x - (1 + x ^ 2 / 2 + x ^ 4 / 24) ∧ _
  rw [← heq, add_sub_cancel_left]
  exact ⟨tsum_nonneg (fun _ ↦ by positivity), by
    simpa [Nat.factorial] using stride_tail_bound 6 hx hxr (by simpa using hr) hsum⟩

/-- The Taylor remainder above degree three is nonnegative and bounded by a geometric series. -/
theorem short_sinh_third_tail {x radius : ℝ} (hx : 0 ≤ x) (hxr : x ≤ radius)
    (hr : radius ^ 2 / 42 < 1) :
    let error := Real.sinh x - (x + x ^ 3 / 6)
    0 ≤ error ∧ error ≤ x ^ 5 / 120 / (1 - radius ^ 2 / 42) := by
  let f (n : ℕ) := x ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ)
  have hf : HasSum f (Real.sinh x) := Real.hasSum_sinh x
  have hshift (n : ℕ) : f (n + 2) = x ^ (5 + 2 * n) / ((5 + 2 * n).factorial : ℝ) := by
    unfold f
    rw [show 2 * (n + 2) + 1 = 5 + 2 * n by omega]
  have hsum := (summable_nat_add_iff 2).2 hf.summable
  simp_rw [hshift] at hsum
  have hprefix : (∑ n ∈ Finset.range 2, f n) = x + x ^ 3 / 6 := by
    norm_num [f, Finset.sum_range_succ, Nat.factorial]
  have heq := hf.summable.sum_add_tsum_nat_add 2
  simp_rw [hprefix, hshift, hf.tsum_eq] at heq
  change 0 ≤ Real.sinh x - (x + x ^ 3 / 6) ∧ _
  rw [← heq, add_sub_cancel_left]
  exact ⟨tsum_nonneg (fun _ ↦ by positivity), by
    simpa [Nat.factorial] using stride_tail_bound 5 hx hxr (by simpa using hr) hsum⟩

/-- The quadratic weight of a reflected pair is bounded by its value at the lower endpoint. -/
theorem short_midpoint_weight_le {X Y a b : ℝ}
    (hlo : -2 ≤ X + Y) (hhi : X + Y ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    X * Y - (a + b) * (X + Y) / 2 + a * b ≤ (1 + a) * (1 + b) := by
  have hsum : (X + Y) ^ 2 ≤ 4 := by
    nlinarith only [mul_nonneg (show 0 ≤ X + Y + 2 by linarith)
      (show 0 ≤ 2 - (X + Y) by linarith)]
  have hprod : X * Y ≤ 1 := by nlinarith only [hsum, sq_nonneg (X - Y)]
  have hlinear : (a + b) * (-(X + Y) / 2) ≤ (a + b) * 1 :=
    mul_le_mul_of_nonneg_left (by linarith) (add_nonneg ha hb)
  linarith only [hprod, hlinear,
    show (1 + a) * (1 + b) = 1 + (a + b) + a * b by ring,
    show (a + b) * (-(X + Y) / 2) = -(a + b) * (X + Y) / 2 by ring]

/-- Bound the error of the paired joint term, keeping the sign of its odd coefficient. -/
theorem short_midpoint_remainder_le {x radius H cap c w : ℝ}
    (hx : 0 ≤ x) (hxr : x ≤ radius) (hr : radius ^ 2 / 42 < 1)
    (hw : 0 ≤ w) (hH : H ≤ cap) (hcap : 0 ≤ cap) :
    H * (Real.cosh x - (1 + x ^ 2 / 2 + x ^ 4 / 24)) +
      c * w * (Real.sinh x - (x + x ^ 3 / 6)) ≤
    cap * (x ^ 6 / 720 / (1 - radius ^ 2 / 56)) +
      max 0 c * w * (x ^ 5 / 120 / (1 - radius ^ 2 / 42)) := by
  have hr' : radius ^ 2 / 56 < 1 := by nlinarith only [hr, sq_nonneg radius]
  obtain ⟨hce, hcu⟩ := short_cosh_fourth_tail hx hxr hr'
  obtain ⟨hse, hsu⟩ := short_sinh_third_tail hx hxr hr
  refine add_le_add
    ((mul_le_mul_of_nonneg_right hH hce).trans (mul_le_mul_of_nonneg_left hcu hcap)) ?_
  have hc := le_max_right (0 : ℝ) c
  have hc₀ := le_max_left (0 : ℝ) c
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc hw) hse).trans
    (mul_le_mul_of_nonneg_left hsu (mul_nonneg hc₀ hw))

private theorem short_midpoint_pair {X Y a b r : ℝ} :
    ((X - a) * (Y - b) * Real.exp (r * (Y - X)) +
      (Y - a) * (X - b) * Real.exp (-(r * (Y - X)))) / 2 =
    (X * Y - (a + b) * (X + Y) / 2 + a * b) * Real.cosh (r * (Y - X)) +
      (b - a) / 2 * (Y - X) * Real.sinh (r * (Y - X)) := by
  rw [Real.cosh_eq, Real.sinh_eq]
  ring

/-- The fourth-order upper bound for one reflected pair in the tilted joint sum. -/
noncomputable def shortPairMajorant (r radius a b X Y : ℝ) : ℝ :=
  let w := |Y - X|
  let t := r * w
  let H := X * Y - (a + b) * (X + Y) / 2 + a * b
  H * (1 + t ^ 2 / 2 + t ^ 4 / 24) +
    (b - a) / 2 * w * (t + t ^ 3 / 6) +
    (1 + a) * (1 + b) * (t ^ 6 / 720 / (1 - radius ^ 2 / 56)) +
    max 0 ((b - a) / 2) * w * (t ^ 5 / 120 / (1 - radius ^ 2 / 42))

theorem shortPairMajorant_expanded (r radius a b X Y : ℝ) :
    let w := Y - X
    let H := X * Y - (a + b) * (X + Y) / 2 + a * b
    let c := (b - a) / 2
    let tail := (1 + a) * (1 + b) * (r ^ 6 / 720 / (1 - radius ^ 2 / 56)) +
      max 0 c * (r ^ 5 / 120 / (1 - radius ^ 2 / 42))
    shortPairMajorant r radius a b X Y =
      H + (r ^ 2 / 2) * (H * w ^ 2) + (r ^ 4 / 24) * (H * w ^ 4) +
        c * r * w ^ 2 + c * (r ^ 3 / 6) * w ^ 4 + tail * w ^ 6 := by
  intro w H c tail
  have h2 : |w| ^ 2 = w ^ 2 := sq_abs w
  have h4 : |w| ^ 4 = w ^ 4 := (even_two_mul 2).pow_abs w
  have h6 : |w| ^ 6 = w ^ 6 := (even_two_mul 3).pow_abs w
  rw [← h2, ← h4, ← h6]
  dsimp only [shortPairMajorant, H, c, w, tail]
  ring

theorem short_midpoint_pair_le_fourth {r radius a b X Y : ℝ}
    (hr : 0 ≤ r) (ht : r * |Y - X| ≤ radius) (hR : radius ^ 2 / 42 < 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hlo : -2 ≤ X + Y) (hhi : X + Y ≤ 1) :
    (X * Y - (a + b) * (X + Y) / 2 + a*b) * Real.cosh (r * (Y - X)) +
      (b - a) / 2 * (Y - X) * Real.sinh (r * (Y - X)) ≤
    shortPairMajorant r radius a b X Y := by
  let w := Y - X
  let H := X * Y - (a + b) * (X + Y) / 2 + a * b
  let c := (b - a) / 2
  have hc : Real.cosh (r * w) = Real.cosh (r * |w|) := by
    calc
      _ = Real.cosh |r * w| := (Real.cosh_abs _).symm
      _ = _ := by rw [abs_mul, abs_of_nonneg hr]
  have hs : w * Real.sinh (r * w) = |w| * Real.sinh (r * |w|) := by
    rcases le_or_gt 0 w with hw | hw
    · rw [abs_of_nonneg hw]
    · rw [abs_of_neg hw, mul_neg, Real.sinh_neg, neg_mul_neg]
  have hrem := short_midpoint_remainder_le (x := r * |w|) (H := H)
    (cap := (1 + a) * (1 + b)) (c := c) (w := |w|)
    (mul_nonneg hr (abs_nonneg _)) ht hR (abs_nonneg _)
    (short_midpoint_weight_le hlo hhi ha hb) (by positivity)
  change H * Real.cosh (r * w) + c * w * Real.sinh (r * w) ≤ _
  rw [hc, mul_assoc c, hs]
  dsimp only [shortPairMajorant]
  dsimp only [H, c, w] at hrem ⊢
  nlinarith only [hrem]

/-- The even moments of the step-two symmetric grid used in the conditional joint term. -/
def shortGridEvenSum (n j : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, ((n : ℝ) - 1 - 2 * i) ^ (2 * j)

private theorem shortGridEvenSum_step (n j : ℕ) :
    shortGridEvenSum (n + 2) j =
      shortGridEvenSum n j + 2 * ((n : ℝ) + 1) ^ (2 * j) := by
  unfold shortGridEvenSum
  rw [Finset.sum_range_succ (n := n + 1), Finset.sum_range_succ' (n := n)]
  have hmiddle (i : ℕ) :
      (↑(n + 2) : ℝ) - 1 - 2 * (↑(i + 1) : ℝ) = (n : ℝ) - 1 - 2 * i := by
    push_cast
    ring
  have hleft : (↑(n + 2) : ℝ) - 1 - 2 * 0 = (n : ℝ) + 1 := by
    push_cast
    ring
  simp only [Nat.cast_succ, Nat.cast_zero] at hmiddle hleft ⊢
  simp only [hmiddle, hleft]
  ring_nf
  rw [show (-1 : ℝ) - n = -(1 + (n : ℝ)) by ring,
    show j * 2 = 2 * j by omega, (even_two_mul j).neg_pow]
  ring

private theorem shortGridEvenSum_eq_of_step {j : ℕ} {F : ℕ → ℝ}
    (h₀ : shortGridEvenSum 0 j = F 0) (h₁ : shortGridEvenSum 1 j = F 1)
    (step : ∀ n : ℕ, F (n + 2) = F n + 2 * ((n : ℝ) + 1) ^ (2 * j))
    (n : ℕ) : shortGridEvenSum n j = F n :=
  Nat.twoStepInduction h₀ h₁
    (fun k ih _ ↦ by rw [shortGridEvenSum_step, ih, step]) n

theorem shortGridEvenSum_two (n : ℕ) :
    shortGridEvenSum n 1 = n * ((n : ℝ) ^ 2 - 1) / 3 := by
  apply shortGridEvenSum_eq_of_step
  · norm_num [shortGridEvenSum]
  · norm_num [shortGridEvenSum, Finset.sum_range_succ]
  · intro k
    push_cast
    ring

theorem shortGridEvenSum_four (n : ℕ) :
    shortGridEvenSum n 2 = n * ((n : ℝ) ^ 2 - 1) * (3 * (n : ℝ) ^ 2 - 7) / 15 := by
  apply shortGridEvenSum_eq_of_step
  · norm_num [shortGridEvenSum]
  · norm_num [shortGridEvenSum, Finset.sum_range_succ]
  · intro k
    push_cast
    ring

theorem shortGridEvenSum_six (n : ℕ) :
    shortGridEvenSum n 3 = n * ((n : ℝ) ^ 2 - 1) *
      (3 * (n : ℝ) ^ 4 - 18 * (n : ℝ) ^ 2 + 31) / 21 := by
  apply shortGridEvenSum_eq_of_step
  · norm_num [shortGridEvenSum]
  · norm_num [shortGridEvenSum, Finset.sum_range_succ]
  · intro k
    push_cast
    ring

end RefinedBMV.PositiveCenter
