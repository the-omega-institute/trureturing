/- GID: D5/S3/Fourier/ThetaVerticalPositive
   generality: G
   mirror-B: D5/B/S3/Fourier/ThetaVerticalPositive
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Hexagonal stationarity and a quantitative lower bound for the vertical square sum. -/

import D5.S3.Fourier.PlanarThetaFoundation
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Real.Pi.Bounds

/-! # Hexagonal stationarity and the vertical square contribution -/

set_option autoImplicit false

open scoped BigOperators

namespace D5.S3.Fourier.PlanarTheta
noncomputable section

/-- The negative part of the height differential expression. -/
def verticalNegative (t y : ℝ) : ℝ :=
  (2 * Real.pi * t / y) * ∑' p : ℤ × ℤ, (p.2 : ℝ) ^ 2 *
    Real.exp (-Real.pi * t * Q (1 / 2) y p)

/-- Convergence of the weighted height series. -/
theorem weighted_gaussian_summable {t y : ℝ} (ht : 0 < t) (hy : 0 < y) :
    Summable (fun p : ℤ × ℤ => (p.2 : ℝ) ^ 2 *
      Real.exp (-Real.pi * t * Q (1 / 2) y p)) := by
  let c := Real.pi * t / 2
  have hc : 0 < c := by dsimp [c]; positivity
  have hbase := (summable (t / 2) (1 / 2) (by positivity) hy).mul_left (1 / (c * y))
  apply hbase.of_nonneg_of_le (fun p => by positivity)
  intro p
  have hq : y * (p.2 : ℝ) ^ 2 ≤ Q (1 / 2) y p := by
    dsimp [Q]
    exact le_add_of_nonneg_left (by positivity)
  have hu := (Real.mul_exp_neg_le_exp_neg_one (c * Q (1 / 2) y p)).trans
    (Real.exp_le_one_iff.mpr (by norm_num : (-1 : ℝ) ≤ 0))
  have hmul := mul_le_mul_of_nonneg_left hq
    (show 0 ≤ c * Real.exp (-(c * Q (1 / 2) y p)) by positivity)
  have hn : (p.2 : ℝ) ^ 2 * Real.exp (-c * Q (1 / 2) y p) ≤ 1 / (c * y) := by
    apply (le_div_iff₀ (mul_pos hc hy)).mpr
    rw [show -c * Q (1 / 2) y p = -(c * Q (1 / 2) y p) by ring]
    nlinarith only [hu, hmul]
  have h := mul_le_mul_of_nonneg_right hn (Real.exp_pos (-c * Q (1 / 2) y p)).le
  have he : Real.exp (-Real.pi * t * Q (1 / 2) y p) =
      Real.exp (-c * Q (1 / 2) y p) * Real.exp (-c * Q (1 / 2) y p) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [c]
    ring
  have hehalf : Real.exp (-Real.pi * (t / 2) * Q (1 / 2) y p) =
      Real.exp (-c * Q (1 / 2) y p) := by
    congr 1
    dsimp [c]
    ring
  rw [he, hehalf]
  convert h using 1 <;> ring

private def heightTerm (t x y : ℝ) (v : ℤ × ℤ) : ℝ :=
  (-Real.pi * t *
    ((v.2 : ℝ) ^ 2 - ((v.1 : ℝ) + v.2 * x) ^ 2 / y ^ 2)) *
      Real.exp (-Real.pi * t * Q x y v)

private lemma heightQuadratic_bound (x : ℝ) {y : ℝ} (hy : 0 < y) (v : ℤ × ℤ) :
    |(v.2 : ℝ) ^ 2 - ((v.1 : ℝ) + v.2 * x) ^ 2 / y ^ 2| ≤
    Q x y v / y := by
  have hU : 0 ≤ ((v.1 : ℝ) + v.2 * x) ^ 2 / y := by positivity
  have hV : 0 ≤ y * (v.2 : ℝ) ^ 2 := by positivity
  have he : (v.2 : ℝ) ^ 2 - ((v.1 : ℝ) + v.2 * x) ^ 2 / y ^ 2 =
      (y * (v.2 : ℝ) ^ 2 - ((v.1 : ℝ) + v.2 * x) ^ 2 / y) / y := by
    field_simp [hy.ne']
    <;> ring
  rw [he, abs_div, abs_of_pos hy]
  apply div_le_div_of_nonneg_right _ hy.le
  change |y * (v.2 : ℝ) ^ 2 - ((v.1 : ℝ) + v.2 * x) ^ 2 / y| ≤
    ((v.1 : ℝ) + v.2 * x) ^ 2 / y + y * (v.2 : ℝ) ^ 2
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private lemma heightTerm_summable (t x : ℝ) {y : ℝ} (ht : 0 < t) (hy : 0 < y) :
    Summable (heightTerm t x y) := by
  have hb (v : ℤ × ℤ) :
      ‖heightTerm t x y v‖ ≤ (2 / y) * Real.exp (-Real.pi * (t / 2) * Q x y v) := by
    have hA := heightQuadratic_bound x hy v
    have hE : (Real.pi * t / 2) * Q x y v ≤
        Real.exp ((Real.pi * t / 2) * Q x y v) := by
      linarith [Real.add_one_le_exp ((Real.pi * t / 2) * Q x y v)]
    change |(-Real.pi * t *
      ((v.2 : ℝ) ^ 2 - ((v.1 : ℝ) + v.2 * x) ^ 2 / y ^ 2)) *
        Real.exp (-Real.pi * t * Q x y v)| ≤ _
    rw [abs_mul, abs_mul, abs_mul, abs_neg,
      abs_of_pos Real.pi_pos, abs_of_pos ht, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ (Real.pi * t * (Q x y v / y)) *
          Real.exp (-Real.pi * t * Q x y v) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hA (by positivity)) (Real.exp_pos _).le
      _ = (2 / y) * (((Real.pi * t / 2) * Q x y v) *
          Real.exp (-Real.pi * t * Q x y v)) := by ring
      _ ≤ (2 / y) * (Real.exp ((Real.pi * t / 2) * Q x y v) *
          Real.exp (-Real.pi * t * Q x y v)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hE (Real.exp_pos _).le) (by positivity)
      _ = _ := by rw [← Real.exp_add]; congr 1; congr 1; ring
  exact ((summable (t / 2) x (by positivity) hy).mul_left (2 / y)).of_norm_bounded hb

def hexTurn : (ℤ × ℤ) ≃ (ℤ × ℤ) where
  toFun v := (v.2, -v.1 - v.2)
  invFun v := (-v.1 - v.2, v.1)
  left_inv v := by apply Prod.ext <;> dsimp <;> ring
  right_inv v := by apply Prod.ext <;> dsimp <;> ring

private lemma hex_height_pos : 0 < Real.sqrt 3 / 2 := by positivity

private lemma hex_height_square : (Real.sqrt 3 / 2) ^ 2 = (3 : ℝ) / 4 := by
  rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num

lemma hex_q_turn (v : ℤ × ℤ) :
    Q (1 / 2) (Real.sqrt 3 / 2) (hexTurn v) =
      Q (1 / 2) (Real.sqrt 3 / 2) v := by
  have hc0 := hex_height_pos.ne'
  have hscale (w : ℤ × ℤ) : Q (1 / 2) (Real.sqrt 3 / 2) w * (Real.sqrt 3 / 2) =
      (w.1 : ℝ) ^ 2 + (w.1 : ℝ) * w.2 + (w.2 : ℝ) ^ 2 := by
    dsimp [Q]
    rw [add_mul, div_mul_cancel₀ _ hc0]
    calc
      _ = ((w.1 : ℝ) + w.2 * (1 / 2)) ^ 2 +
          (Real.sqrt 3 / 2) ^ 2 * (w.2 : ℝ) ^ 2 := by ring
      _ = _ := by rw [hex_height_square]; ring
  apply (mul_left_inj' hc0).mp
  rw [hscale, hscale]
  dsimp [hexTurn]
  push_cast
  ring

private lemma heightTerm_hex_orbit (t : ℝ) (v : ℤ × ℤ) :
    heightTerm t (1 / 2) (Real.sqrt 3 / 2) v +
      heightTerm t (1 / 2) (Real.sqrt 3 / 2) (hexTurn v) +
      heightTerm t (1 / 2) (Real.sqrt 3 / 2) (hexTurn (hexTurn v)) = 0 := by
  simp only [heightTerm, hex_q_turn, hex_height_square]
  dsimp [hexTurn]
  push_cast
  ring

/-- The threefold integer rotation of the hexagonal form annihilates its height derivative. -/
theorem hexagonal_height_stationary {t : ℝ} (ht : 0 < t) :
    deriv (fun y => F t (1 / 2) y) (Real.sqrt 3 / 2) = 0 := by
  let f := heightTerm t (1 / 2) (Real.sqrt 3 / 2)
  have hs : Summable f := heightTerm_summable t (1 / 2) ht hex_height_pos
  have hs1 : Summable (fun v => f (hexTurn v)) := hexTurn.summable_iff.mpr hs
  have hs2 : Summable (fun v => f (hexTurn (hexTurn v))) :=
    hexTurn.summable_iff.mpr hs1
  have hsum : (∑' v, f v) + (∑' v, f (hexTurn v)) +
      (∑' v, f (hexTurn (hexTurn v))) = 0 := by
    rw [← hs.tsum_add hs1, ← (hs.add hs1).tsum_add hs2]
    simp only [f, heightTerm_hex_orbit, tsum_zero]
  have hsTurn : (∑' v, f (hexTurn (hexTurn v))) = ∑' v, f (hexTurn v) :=
    hexTurn.tsum_eq (fun v => f (hexTurn v))
  have hsOnce : (∑' v, f (hexTurn v)) = ∑' v, f v := hexTurn.tsum_eq f
  rw [hsTurn] at hsum
  simp only [hsOnce] at hsum
  have hz : (∑' v, f v) = 0 := by linarith
  rw [(hasDerivAt_height t (1 / 2) ht hex_height_pos).deriv]
  exact hz

/-- The nonnegative square contribution to the vertical differential expression. -/
def verticalPositive (t y : ℝ) : ℝ :=
  (Real.pi * t) ^ 2 * ∑' v : ℤ × ℤ,
    ((v.2 : ℝ) ^ 2 - ((v.1 : ℝ) + v.2 * (1 / 2)) ^ 2 / y ^ 2) ^ 2 *
      Real.exp (-Real.pi * t * Q (1 / 2) y v)

/-- The positive Gaussian scale of the four shortest directions. -/
def verticalScale (t y : ℝ) : ℝ :=
  2 * Real.pi * t * Real.exp (-Real.pi * t * (y + 1 / (4 * y)))

private lemma vertical_square_summable {t y : ℝ} (ht : 0 < t) (hy : 0 < y) :
    Summable (fun v : ℤ × ℤ =>
      ((v.2 : ℝ) ^ 2 - ((v.1 : ℝ) + v.2 * (1 / 2)) ^ 2 / y ^ 2) ^ 2 *
        Real.exp (-Real.pi * t * Q (1 / 2) y v)) := by
  let p := Real.pi * t
  have hp : 0 < p := mul_pos Real.pi_pos ht
  have hmajor (v : ℤ × ℤ) :
      ((v.2 : ℝ) ^ 2 - ((v.1 : ℝ) + v.2 * (1 / 2)) ^ 2 / y ^ 2) ^ 2 *
        Real.exp (-Real.pi * t * Q (1 / 2) y v) ≤
      (8 / (p ^ 2 * y ^ 2)) * Real.exp (-Real.pi * (t / 2) * Q (1 / 2) y v) := by
    let q := Q (1 / 2) y v
    have hq : 0 ≤ q := by dsimp [q, Q]; positivity
    have hA := heightQuadratic_bound (1 / 2) hy v
    have hsq :
        ((v.2 : ℝ) ^ 2 - ((v.1 : ℝ) + v.2 * (1 / 2)) ^ 2 / y ^ 2) ^ 2 ≤
          q ^ 2 / y ^ 2 := by
      have h := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ q / y)).mpr hA
      simpa only [sq_abs, div_pow] using h
    have hE : (p * q) ^ 2 ≤ 8 * Real.exp (p * q / 2) := by
      have h := Real.sum_le_exp_of_nonneg (by positivity : 0 ≤ p * q / 2) 3
      norm_num [Finset.sum_range_succ] at h
      nlinarith [mul_nonneg hp.le hq]
    rw [show -Real.pi * t * Q (1 / 2) y v = -p * q by dsimp [p, q]; ring,
      show -Real.pi * (t / 2) * Q (1 / 2) y v = -p * q / 2 by dsimp [p, q]; ring]
    calc
      _ ≤ (q ^ 2 / y ^ 2) * Real.exp (-p * q) :=
        mul_le_mul_of_nonneg_right hsq (Real.exp_pos _).le
      _ = (1 / (p ^ 2 * y ^ 2)) * ((p * q) ^ 2 * Real.exp (-p * q)) := by
        field_simp [hp.ne', hy.ne']
        <;> ring
      _ ≤ (1 / (p ^ 2 * y ^ 2)) *
          ((8 * Real.exp (p * q / 2)) * Real.exp (-p * q)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hE (Real.exp_pos _).le) (by positivity)
      _ = (8 / (p ^ 2 * y ^ 2)) * Real.exp (-p * q / 2) := by
        rw [show 8 * Real.exp (p * q / 2) * Real.exp (-p * q) =
          8 * Real.exp (-p * q / 2) by
            rw [mul_assoc, ← Real.exp_add]; congr 1; congr 1; ring]
        ring
  exact ((summable (t / 2) (1 / 2) (by positivity) hy).mul_left
    (8 / (p ^ 2 * y ^ 2))).of_nonneg_of_le (fun _ => by positivity) hmajor

private def leadingVertical (p y : ℝ) : ℝ :=
  p / y ^ 4 * Real.exp (p * (y - 3 / (4 * y)))

private lemma leadingVertical_hasDeriv (p : ℝ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (leadingVertical p)
      (p * Real.exp (p * (y - 3 / (4 * y))) / y ^ 6 *
        (p * (y ^ 2 + 3 / 4) - 4 * y)) y := by
  have hq := (hasDerivAt_const y p).div ((hasDerivAt_id y).pow 4)
    (pow_ne_zero 4 hy.ne')
  have he := ((hasDerivAt_id y).sub ((hasDerivAt_const y 3).div
    ((hasDerivAt_id y).const_mul 4) (by positivity : (4 : ℝ) * y ≠ 0))).const_mul p
  convert hq.mul he.exp using 1
  · rfl
  · dsimp
    field_simp [hy.ne']
    <;> ring


private lemma leadingVertical_at_hex (p : ℝ) :
    leadingVertical p (Real.sqrt 3 / 2) = 16 * p / 9 := by
  have hc := hex_height_square
  have hc0 := hex_height_pos.ne'
  have he : Real.sqrt 3 / 2 - 3 / (4 * (Real.sqrt 3 / 2)) = 0 := by
    field_simp [hc0]
    nlinarith [hc]
  have hc4 : (Real.sqrt 3 / 2) ^ 4 = (9 : ℝ) / 16 := by
    rw [show (Real.sqrt 3 / 2) ^ 4 = ((Real.sqrt 3 / 2) ^ 2) ^ 2 by ring, hc]
    norm_num
  rw [leadingVertical, he, mul_zero, Real.exp_zero, mul_one, hc4]
  ring


private lemma vertical_four_terms {t y : ℝ} (ht : 0 < t) (hy : 0 < y) :
    verticalScale t y * (leadingVertical (Real.pi * t) y +
      Real.pi * t * (1 - 1 / (4 * y ^ 2)) ^ 2) ≤ verticalPositive t y := by
  let p := Real.pi * t
  let f (v : ℤ × ℤ) :=
    ((v.2 : ℝ) ^ 2 - ((v.1 : ℝ) + v.2 * (1 / 2)) ^ 2 / y ^ 2) ^ 2 *
      Real.exp (-Real.pi * t * Q (1 / 2) y v)
  have hs : Summable f := vertical_square_summable ht hy
  have hf0 : f (1, 0) = (1 / y ^ 4) * Real.exp (-p / y) := by
    dsimp [f, Q, p]
    norm_num only [Int.cast_zero, Int.cast_one, zero_pow (by decide : (2 : ℕ) ≠ 0),
      one_pow, zero_mul, mul_zero, zero_add, add_zero, zero_sub, neg_sq]
    congr 1
    · field_simp [hy.ne']
      <;> ring
    · congr 1
      ring
  have hfn0 : f (-1, 0) = f (1, 0) := by
    simp [f, Q]
  have hf1 : f (0, 1) = (1 - 1 / (4 * y ^ 2)) ^ 2 *
      Real.exp (-p * (y + 1 / (4 * y))) := by
    dsimp [f, Q, p]
    norm_num only [Int.cast_zero, Int.cast_one, zero_pow (by decide : (2 : ℕ) ≠ 0),
      one_pow, zero_mul, mul_zero, zero_add, add_zero]
    congr 1
    · congr 1
      field_simp [hy.ne']
      <;> ring
    · congr 1
      ring
  have hfn1 : f (0, -1) = f (0, 1) := by
    simp [f, Q]
  have hpart := hs.sum_le_tsum ({(1, 0), (-1, 0), (0, 1), (0, -1)} :
    Finset (ℤ × ℤ)) (fun _ _ => by dsimp [f]; positivity)
  have hmul := mul_le_mul_of_nonneg_left hpart (sq_nonneg p)
  change p ^ 2 * _ ≤ verticalPositive t y at hmul
  have hfinite : p ^ 2 * (∑ v ∈
      ({(1, 0), (-1, 0), (0, 1), (0, -1)} : Finset (ℤ × ℤ)), f v) =
      2 * p ^ 2 / y ^ 4 * Real.exp (-p / y) +
        2 * p ^ 2 * (1 - 1 / (4 * y ^ 2)) ^ 2 *
          Real.exp (-p * (y + 1 / (4 * y))) := by
    norm_num [hfn0, hfn1, hf0, hf1] <;> ring
  rw [hfinite] at hmul
  have hexp : Real.exp (-p * (y + 1 / (4 * y))) *
      Real.exp (p * (y - 3 / (4 * y))) = Real.exp (-p / y) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hfirst : 2 * p * Real.exp (-p * (y + 1 / (4 * y))) *
      (p / y ^ 4 * Real.exp (p * (y - 3 / (4 * y)))) =
      2 * p ^ 2 / y ^ 4 * Real.exp (-p / y) := by
    calc
      _ = 2 * p ^ 2 / y ^ 4 *
          (Real.exp (-p * (y + 1 / (4 * y))) *
            Real.exp (p * (y - 3 / (4 * y)))) := by ring
      _ = _ := by rw [hexp]
  have hscale : verticalScale t y = 2 * p *
      Real.exp (-p * (y + 1 / (4 * y))) := by
    unfold verticalScale
    rw [show -Real.pi * t * (y + 1 / (4 * y)) =
      -p * (y + 1 / (4 * y)) by dsimp [p]; ring]
    dsimp [p]
    ring
  calc
    _ = 2 * p ^ 2 / y ^ 4 * Real.exp (-p / y) +
        2 * p ^ 2 * (1 - 1 / (4 * y ^ 2)) ^ 2 *
          Real.exp (-p * (y + 1 / (4 * y))) := by
      rw [hscale]
      unfold leadingVertical
      change (2 * p * Real.exp (-p * (y + 1 / (4 * y)))) *
        (p / y ^ 4 * Real.exp (p * (y - 3 / (4 * y))) +
          p * (1 - 1 / (4 * y ^ 2)) ^ 2) = _
      rw [mul_add, hfirst]
      ring
    _ ≤ _ := hmul

/-- Four explicitly retained terms give a uniform lower bound for the square contribution. -/
theorem verticalPositive_lower {t y : ℝ} (ht : 4 / Real.sqrt 3 ≤ Real.pi * t)
    (hy : Real.sqrt 3 / 2 ≤ y) :
    verticalScale t y * (20 * Real.pi * t / 9) ≤ verticalPositive t y := by
  have hs : 0 < Real.sqrt 3 := by positivity
  have hs2 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have ht0 : 0 < t := by
    have hp : 0 < Real.pi * t := lt_of_lt_of_le (by positivity) ht
    exact (mul_pos_iff_of_pos_left Real.pi_pos).mp hp
  have hy0 : 0 < y := (by positivity : 0 < Real.sqrt 3 / 2).trans_le hy
  have hmul : 4 ≤ Real.pi * t * Real.sqrt 3 := (div_le_iff₀ hs).mp ht
  have hleadmono : MonotoneOn (leadingVertical (Real.pi * t)) (Set.Ici (Real.sqrt 3 / 2)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici _)
    · intro z hz
      exact (leadingVertical_hasDeriv (Real.pi * t)
        ((by positivity : 0 < Real.sqrt 3 / 2).trans_le hz)).continuousAt.continuousWithinAt
    · intro z hz
      rw [interior_Ici] at hz
      exact (leadingVertical_hasDeriv (Real.pi * t)
        ((by positivity : 0 < Real.sqrt 3 / 2).trans hz)).differentiableAt.differentiableWithinAt
    · intro z hz
      rw [interior_Ici] at hz
      have hz0 : 0 < z := (by positivity : 0 < Real.sqrt 3 / 2).trans hz
      rw [(leadingVertical_hasDeriv (Real.pi * t) hz0).deriv]
      have hp : 0 < Real.pi * t := mul_pos Real.pi_pos ht0
      have hpoly : 0 ≤ Real.pi * t * (z ^ 2 + 3 / 4) - 4 * z := by
        have hm := mul_le_mul_of_nonneg_right hmul (by positivity : 0 ≤ z ^ 2 + 3 / 4)
        have hsq := sq_nonneg (z - Real.sqrt 3 / 2)
        have hh : 0 ≤ Real.sqrt 3 * (Real.pi * t * (z ^ 2 + 3 / 4) - 4 * z) := by
          nlinarith
        exact (mul_nonneg_iff_of_pos_left hs).mp hh
      exact mul_nonneg
        (div_nonneg (mul_nonneg hp.le (Real.exp_pos _).le) (pow_nonneg hz0.le 6)) hpoly
  have hlead : 16 * (Real.pi * t) / 9 ≤ leadingVertical (Real.pi * t) y := by
    rw [← leadingVertical_at_hex (Real.pi * t)]
    exact hleadmono (a := Real.sqrt 3 / 2) (b := y) (by simp) hy hy
  have hy2 : (3 : ℝ) / 4 ≤ y ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hy) (show 0 ≤ y + Real.sqrt 3 / 2 by positivity)]
  have hfrac : 1 / (4 * y ^ 2) ≤ (1 : ℝ) / 3 := by
    apply (div_le_iff₀ (by positivity : 0 < 4 * y ^ 2)).mpr
    nlinarith
  have hsq : (4 : ℝ) / 9 ≤ (1 - 1 / (4 * y ^ 2)) ^ 2 := by
    nlinarith [sq_nonneg (1 - 1 / (4 * y ^ 2) - 2 / 3)]
  have hp2 := mul_le_mul_of_nonneg_left hsq (mul_pos Real.pi_pos ht0).le
  have hcombined : 20 * Real.pi * t / 9 ≤ leadingVertical (Real.pi * t) y +
      Real.pi * t * (1 - 1 / (4 * y ^ 2)) ^ 2 := by linarith
  exact (mul_le_mul_of_nonneg_left hcombined
    (by dsimp [verticalScale]; positivity)).trans (vertical_four_terms ht0 hy0)

/-- Cancellation of the first-derivative terms leaves precisely the positive and negative sums. -/
theorem vertical_differential_identity {t y : ℝ} (ht : 0 < t) (hy : 0 < y) :
    deriv (fun b => deriv (fun z => F t (1 / 2) z) b) y +
      (2 / y) * deriv (fun z => F t (1 / 2) z) y =
        verticalPositive t y - verticalNegative t y := by
  let p := Real.pi * t
  let U (v : ℤ × ℤ) :=
    ((v.2 : ℝ) ^ 2 - ((v.1 : ℝ) + v.2 * (1 / 2)) ^ 2 / y ^ 2) ^ 2 *
      Real.exp (-Real.pi * t * Q (1 / 2) y v)
  let N (v : ℤ × ℤ) := (v.2 : ℝ) ^ 2 *
    Real.exp (-Real.pi * t * Q (1 / 2) y v)
  let V := heightTerm t (1 / 2) y
  let W (v : ℤ × ℤ) := p ^ 2 * U v - (2 * p / y) * N v - (2 / y) * V v
  have hU : Summable U := vertical_square_summable ht hy
  have hN : Summable N := weighted_gaussian_summable ht hy
  have hV : Summable V := heightTerm_summable t (1 / 2) ht hy
  have hterm (v : ℤ × ℤ) :
      ((Real.pi * t) ^ 2 *
        ((v.2 : ℝ) ^ 2 - ((v.1 : ℝ) + v.2 * (1 / 2)) ^ 2 / y ^ 2) ^ 2 -
        Real.pi * t * (2 * ((v.1 : ℝ) + v.2 * (1 / 2)) ^ 2 / y ^ 3)) *
          Real.exp (-Real.pi * t * Q (1 / 2) y v) = W v := by
    dsimp [W, U, N, V, p, heightTerm]
    field_simp [hy.ne']
    <;> ring
  have hsum : (∑' v : ℤ × ℤ, W v) = p ^ 2 * (∑' v, U v) -
      (2 * p / y) * (∑' v, N v) - (2 / y) * (∑' v, V v) := by
    dsimp [W]
    rw [((hU.mul_left (p ^ 2)).sub (hN.mul_left (2 * p / y))).tsum_sub
      (hV.mul_left (2 / y)), (hU.mul_left (p ^ 2)).tsum_sub (hN.mul_left (2 * p / y)),
      tsum_mul_left, tsum_mul_left, tsum_mul_left]
  rw [(hasDerivAt_height_deriv t (1 / 2) ht hy).deriv,
    (hasDerivAt_height t (1 / 2) ht hy).deriv]
  simp_rw [hterm]
  rw [hsum]
  unfold verticalPositive verticalNegative
  change p ^ 2 * (∑' v, U v) - (2 * p / y) * (∑' v, N v) -
    (2 / y) * (∑' v, V v) + (2 / y) *
      (∑' v, heightTerm t (1 / 2) y v) =
        p ^ 2 * (∑' v, U v) - (2 * Real.pi * t / y) * (∑' v, N v)
  have hcoeff : 2 * Real.pi * t / y = 2 * p / y := by dsimp [p]; ring
  rw [hcoeff]
  change p ^ 2 * (∑' v, U v) - (2 * p / y) * (∑' v, N v) -
    (2 / y) * (∑' v, V v) + (2 / y) * (∑' v, V v) = _
  ring

end
end D5.S3.Fourier.PlanarTheta
