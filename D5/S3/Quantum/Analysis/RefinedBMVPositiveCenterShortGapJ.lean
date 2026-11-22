/- GID: D5/S3/Quantum/Analysis/RefinedBMVPositiveCenterShortGapJ
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Derivative bounds for the positive-center short-gap marginal. -/

import D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterMarginalTaylor
import D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterMomentPolynomial

/-! The continued square root of the logarithmic short-gap marginal. -/

open Filter MeasureTheory Set
open scoped Topology

noncomputable section

namespace RefinedBMV.PositiveCenter

open DimThree (gaps mem_gaps_iff_total word_counts_all)
open SmallCorner

private abbrev Gap := ℕ × ℕ × ℕ
private abbrev gapCount (p : ℕ) : ℝ := (gaps p).length
private abbrev spacing (p : ℕ) : ℝ := 3 / (p : ℝ)
private abbrev scale (p : ℕ) : ℝ := (3 + spacing p) * (3 + 2 * spacing p) / 2
private abbrev varianceHalf (p : ℕ) : ℝ := compositionMarginalVariance p / 2
private abbrev centered (p : ℕ) (g : Gap) : ℝ := 3 * (g.2.2 : ℝ) / p - 1
private abbrev exponent (p : ℕ) (g : Gap) : ℝ := 3 * (g.2.2 : ℝ) / p

private theorem gapCount_pos (p : ℕ) : 0 < gapCount p := by
  exact_mod_cast (word_counts_all p).2.1

private theorem varianceHalf_pos (p : ℕ) : 0 < varianceHalf p :=
  half_pos (compositionMarginalVariance_pos p)

private theorem scale_pos (p : ℕ) : 0 < scale p := by
  have h : 0 ≤ spacing p := by positivity
  exact div_pos (mul_pos (by linarith) (by linarith)) (by norm_num)

private theorem variance_eq {p : ℕ} (hp : 0 < p) :
    compositionMarginalVariance p = (1 + spacing p) / 2 := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  unfold compositionMarginalVariance
  rw [(centered_marginal_sums hp).2]
  field_simp [(gapCount_pos p).ne', hpR]

private abbrev M (p : ℕ) := integralMarginalDerivative p (varianceHalf p)

private theorem hasDerivAt_M (p k : ℕ) (t : ℝ) :
    HasDerivAt (M p k) (M p (k + 1) t) t := by
  simpa [affineMarginalJet] using (continuedMarginalJet_isAt p k 0 1 0 t).2.1

private theorem M_zero (p k : ℕ) :
    M p k 0 = ((gaps p).map fun g ↦ centered p g ^ (k + 2)).sum /
      (gapCount p * varianceHalf p * (((k : ℝ) + 1) * ((k : ℝ) + 2))) := by
  have heq (g : Gap) :
      (centered p g ^ 2 * ∫ s in (0 : ℝ)..1,
        (1 - s) * (centered p g * s) ^ k * Real.exp (0 * (centered p g * s))) =
      centered p g ^ (k + 2) * (1 / (((k : ℝ) + 1) * ((k : ℝ) + 2))) := by
    have h (b s : ℝ) : (1 - s) * (b * s) ^ k = b ^ k * ((1 - s) * s ^ k) := by
      rw [mul_pow]
      ring
    simp_rw [zero_mul, Real.exp_zero, mul_one, h, intervalIntegral.integral_const_mul,
      unit_weight_moment]
    rw [← mul_assoc, ← pow_add, Nat.add_comm 2 k]
  unfold M integralMarginalDerivative
  change ((gaps p).map fun g ↦ centered p g ^ 2 * ∫ s in (0 : ℝ)..1,
    (1 - s) * (centered p g * s) ^ k * Real.exp (0 * (centered p g * s))).sum / _ = _
  simp_rw [heq, List.sum_map_mul_right, mul_one_div, div_div]
  rw [mul_comm (((k : ℝ) + 1) * ((k : ℝ) + 2))]

private theorem M_mass_zero (p : ℕ) : M p 0 0 = 1 := by
  rw [M_zero]
  have h : ((gaps p).map fun g ↦ centered p g ^ 2).sum =
      gapCount p * compositionMarginalVariance p := by
    unfold compositionMarginalVariance
    field_simp [(gapCount_pos p).ne']
  rw [h]
  norm_num
  field_simp [(gapCount_pos p).ne', (compositionMarginalVariance_pos p).ne']

private theorem M_first_zero_pos {p : ℕ} (hp : 0 < p) : 0 < M p 1 0 := by
  rw [M_zero, show (1 : ℕ) + 2 = 3 by rfl, centered_marginal_cubic_sum hp]
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  have hN := gapCount_pos p
  have hV := varianceHalf_pos p
  positivity

private theorem M_pos {p : ℕ} (hp : 0 < p) (t : ℝ) : 0 < M p 0 t := by
  by_cases ht : t = 0
  · simp [ht, M_mass_zero]
  · unfold M
    rw [← iteratedDeriv_G_eq_integral hp (varianceHalf_pos p).ne' ht 0, iteratedDeriv_zero]
    exact G_pos hp (varianceHalf_pos p) ht

private theorem M_quadratic_nonneg (p : ℕ) (t q : ℝ) :
    0 ≤ M p 2 t - (2 * q) * M p 1 t + q ^ 2 * M p 0 t := by
  let f (g : Gap) (k : ℕ) (s : ℝ) :=
    (1 - s) * (centered p g * s) ^ k * Real.exp (t * (centered p g * s))
  let a (k : ℕ) (g : Gap) := centered p g ^ 2 * ∫ s in (0 : ℝ)..1, f g k s
  have hi (g : Gap) (k : ℕ) : IntervalIntegrable (f g k) volume 0 1 :=
    (by unfold f; fun_prop : Continuous (f g k)).intervalIntegrable 0 1
  have hterm (g : Gap) : 0 ≤ a 2 g - (2 * q) * a 1 g + q ^ 2 * a 0 g := by
    have hInt : 0 ≤ ∫ s in (0 : ℝ)..1,
        (1 - s) * (centered p g * s - q) ^ 2 * Real.exp (t * (centered p g * s)) :=
      intervalIntegral.integral_nonneg zero_le_one fun s hs ↦
        mul_nonneg (mul_nonneg (sub_nonneg.mpr hs.2) (sq_nonneg _)) (Real.exp_pos _).le
    have heq (s : ℝ) :
        (1 - s) * (centered p g * s - q) ^ 2 * Real.exp (t * (centered p g * s)) =
          f g 2 s - (2 * q) * f g 1 s + q ^ 2 * f g 0 s := by
      unfold f
      ring
    simp_rw [heq] at hInt
    rw [intervalIntegral.integral_add ((hi g 2).sub ((hi g 1).const_mul _))
      ((hi g 0).const_mul _), intervalIntegral.integral_sub (hi g 2) ((hi g 1).const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hInt
    exact (show 0 ≤ centered p g ^ 2 *
        ((∫ s in (0 : ℝ)..1, f g 2 s) - (2 * q) * (∫ s in (0 : ℝ)..1, f g 1 s) +
          q ^ 2 * (∫ s in (0 : ℝ)..1, f g 0 s)) from mul_nonneg (sq_nonneg _) hInt) |>.trans_eq
      (by unfold a; ring)
  have hsum (l : List Gap) :
      0 ≤ (l.map (a 2)).sum - (2 * q) * (l.map (a 1)).sum + q ^ 2 * (l.map (a 0)).sum := by
    induction l with
    | nil => simp
    | cons g l ih =>
      simp only [List.map_cons, List.sum_cons]
      linarith only [hterm g, ih]
  let N := gapCount p * varianceHalf p
  change 0 ≤ (List.map (a 2) (gaps p)).sum / N - (2 * q) *
    ((List.map (a 1) (gaps p)).sum / N) + q ^ 2 * ((List.map (a 0) (gaps p)).sum / N)
  convert (div_nonneg (hsum (gaps p))
    (mul_pos (gapCount_pos p) (varianceHalf_pos p)).le : 0 ≤ _ / N) using 1
  ring

private theorem M_logConvex {p : ℕ} (hp : 0 < p) (t : ℝ) :
    M p 1 t ^ 2 ≤ M p 0 t * M p 2 t := by
  have h := M_quadratic_nonneg p t (M p 1 t / M p 0 t)
  have h0 := M_pos hp t
  have hh := mul_nonneg h0.le h
  field_simp [h0.ne'] at hh
  nlinarith only [hh]

private theorem M_first_nonneg {p : ℕ} (hp : 0 < p) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ M p 1 t := by
  have hderiv (x : ℝ) : HasDerivAt (fun y ↦ M p 1 y / M p 0 y)
      ((M p 2 x * M p 0 x - M p 1 x ^ 2) / M p 0 x ^ 2) x := by
    convert (hasDerivAt_M p 1 x).div (hasDerivAt_M p 0 x) (M_pos hp x).ne' using 1
    ring
  have hmono := monotone_of_deriv_nonneg (fun x ↦ (hderiv x).differentiableAt)
    (fun x ↦ by
      rw [(hderiv x).deriv]
      exact div_nonneg (sub_nonneg.mpr (by simpa [mul_comm] using M_logConvex hp x)) (sq_nonneg _))
  have h := hmono ht
  change M p 1 0 / M p 0 0 ≤ M p 1 t / M p 0 t at h
  rw [M_mass_zero, div_one] at h
  have hn := (M_first_zero_pos hp).le.trans h
  rwa [le_div_iff₀ (M_pos hp t), zero_mul] at hn

private abbrev weight (p : ℕ) (t : ℝ) : ℝ := scale p * varianceHalf p * Real.exp t
private abbrev U (p : ℕ) (t : ℝ) : ℝ := weight p t * M p 0 t
private abbrev U₁ (p : ℕ) (t : ℝ) : ℝ := weight p t * (M p 0 t + M p 1 t)
private abbrev U₂ (p : ℕ) (t : ℝ) : ℝ := weight p t * (M p 0 t + 2 * M p 1 t + M p 2 t)

private theorem shortGapWeight_pos (p : ℕ) (t : ℝ) : 0 < weight p t :=
  mul_pos (mul_pos (scale_pos p) (varianceHalf_pos p)) (Real.exp_pos t)

private theorem U_pos {p : ℕ} (hp : 0 < p) (t : ℝ) : 0 < U p t :=
  mul_pos (shortGapWeight_pos p t) (M_pos hp t)

private theorem hasDerivAt_U (p : ℕ) (t : ℝ) : HasDerivAt (U p) (U₁ p t) t :=
  (((Real.hasDerivAt_exp t).const_mul (scale p * varianceHalf p)).mul
    (hasDerivAt_M p 0 t)).congr_deriv (by dsimp; ring)

private theorem hasDerivAt_U₁ (p : ℕ) (t : ℝ) : HasDerivAt (U₁ p) (U₂ p t) t :=
  (((Real.hasDerivAt_exp t).const_mul (scale p * varianceHalf p)).mul
    ((hasDerivAt_M p 0 t).add (hasDerivAt_M p 1 t))).congr_deriv (by dsimp; ring)

private theorem U_logConvex {p : ℕ} (hp : 0 < p) (t : ℝ) :
    U₁ p t ^ 2 ≤ U p t * U₂ p t := by
  have h := mul_nonneg (sq_nonneg (weight p t)) (sub_nonneg.mpr (M_logConvex hp t))
  apply sub_nonneg.mp
  convert h using 1
  unfold U U₁ U₂
  ring

private theorem U_le_U₁ {p : ℕ} (hp : 0 < p) {t : ℝ} (ht : 0 ≤ t) :
    U p t ≤ U₁ p t := by
  have h := mul_nonneg (shortGapWeight_pos p t).le (M_first_nonneg hp ht)
  unfold U U₁
  linarith only [mul_add (weight p t) (M p 0 t) (M p 1 t), h]

/-- The smooth continuation of the short-gap marginal square root from positive gaps. -/
def shortGapJ (p : ℕ) (t : ℝ) : ℝ := t * Real.sqrt (U p t)

private theorem t_sq_mul_U {p : ℕ} (hp : 0 < p) {t : ℝ} (ht : t ≠ 0) :
    t ^ 2 * U p t = scale p * Real.exp t * compositionMoment p 0 t := by
  unfold U
  rw [show M p 0 t = G p (varianceHalf p) t by
    simpa only [iteratedDeriv_zero] using
      (iteratedDeriv_G_eq_integral hp (varianceHalf_pos p).ne' ht 0).symm]
  unfold G
  field_simp [(compositionMarginalVariance_pos p).ne', ht]

/-- At positive gaps the continuation equals the square root of the actual marginal. -/
theorem shortGapJ_eq_sqrt {p : ℕ} (hp : 0 < p) {t : ℝ} (ht : 0 < t) :
    shortGapJ p t =
      Real.sqrt (((3 + 3 / (p : ℝ)) * (3 + 2 * (3 / (p : ℝ))) / 2) *
        Real.exp t * compositionMoment p 0 t) := by
  rw [← show scale p * Real.exp t * compositionMoment p 0 t = _ from rfl,
    ← t_sq_mul_U hp ht.ne', Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ht.le, shortGapJ]

private abbrev S (p : ℕ) (t : ℝ) := Real.sqrt (U p t)
private abbrev S₁ (p : ℕ) (t : ℝ) := U₁ p t / (2 * S p t)
private abbrev S₂ (p : ℕ) (t : ℝ) :=
  (2 * U p t * U₂ p t - U₁ p t ^ 2) / (4 * S p t ^ 3)

private theorem hasDerivAt_S {p : ℕ} (hp : 0 < p) (t : ℝ) :
    HasDerivAt (S p) (S₁ p t) t :=
  (hasDerivAt_U p t).sqrt (U_pos hp t).ne'

private theorem hasDerivAt_S₁ {p : ℕ} (hp : 0 < p) (t : ℝ) :
    HasDerivAt (S₁ p) (S₂ p t) t := by
  have hs := Real.sqrt_pos.2 (U_pos hp t)
  have hd := (hasDerivAt_U₁ p t).div ((hasDerivAt_S hp t).const_mul 2)
    (mul_ne_zero (by norm_num) hs.ne')
  refine hd.congr_deriv ?_
  change _ = (2 * U p t * U₂ p t - U₁ p t ^ 2) / (4 * S p t ^ 3)
  rw [← Real.sq_sqrt (U_pos hp t).le]
  change (U₂ p t * (2 * S p t) - U₁ p t * (2 * (U₁ p t / (2 * S p t)))) /
      (2 * S p t) ^ 2 = _
  field_simp [hs.ne']
  ring

private theorem hasDerivAt_J {p : ℕ} (hp : 0 < p) (t : ℝ) :
    HasDerivAt (shortGapJ p) (S p t + t * S₁ p t) t := by
  unfold shortGapJ
  simpa only [one_mul] using (hasDerivAt_id' t).fun_mul (hasDerivAt_S hp t)

private theorem hasDerivAt_deriv_J {p : ℕ} (hp : 0 < p) (t : ℝ) :
    HasDerivAt (deriv (shortGapJ p)) (2 * S₁ p t + t * S₂ p t) t := by
  have heq : deriv (shortGapJ p) = fun x ↦ S p x + x * S₁ p x :=
    funext fun x ↦ (hasDerivAt_J hp x).deriv
  rw [heq]
  exact ((hasDerivAt_S hp t).add ((hasDerivAt_id' t).mul (hasDerivAt_S₁ hp t))).congr_deriv
    (by ring)

/-- The marginal is strictly increasing on the nonnegative gap axis. -/
theorem shortGapJ_deriv_pos {p : ℕ} (hp : 0 < p) {t : ℝ} (ht : 0 ≤ t) :
    0 < deriv (shortGapJ p) t := by
  rw [(hasDerivAt_J hp t).deriv]
  have hs := Real.sqrt_pos.2 (U_pos hp t)
  exact add_pos_of_pos_of_nonneg hs
    (mul_nonneg ht (div_nonneg ((U_pos hp t).le.trans (U_le_U₁ hp ht)) (by positivity)))

/-- The curvature dominates one half of the slope on the nonnegative gap axis. -/
theorem shortGapJ_deriv_half_le_second {p : ℕ} (hp : 0 < p) {t : ℝ} (ht : 0 ≤ t) :
    deriv (shortGapJ p) t / 2 ≤ deriv (deriv (shortGapJ p)) t := by
  rw [(hasDerivAt_deriv_J hp t).deriv, (hasDerivAt_J hp t).deriv]
  have hs : 0 < S p t := Real.sqrt_pos.2 (U_pos hp t)
  have hs₂ : S p t ^ 2 = U p t := Real.sq_sqrt (U_pos hp t).le
  have h₁ : S p t / 2 ≤ S₁ p t := by
    rw [show S₁ p t = U₁ p t / (2 * S p t) from rfl, le_div_iff₀ (by positivity)]
    calc
      _ = S p t ^ 2 := by ring
      _ = U p t := hs₂
      _ ≤ _ := U_le_U₁ hp ht
  have h₂ : S₁ p t / 2 ≤ S₂ p t := by
    have hU := U_pos hp t
    have hU₁ := hU.le.trans (U_le_U₁ hp ht)
    have hlog := U_logConvex hp t
    have hmul := mul_le_mul_of_nonneg_left (U_le_U₁ hp ht) hU₁
    change U₁ p t / (2 * S p t) / 2 ≤
      (2 * U p t * U₂ p t - U₁ p t ^ 2) / (4 * S p t ^ 3)
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have hh : U₁ p t * U p t ≤ 2 * U p t * U₂ p t - U₁ p t ^ 2 := by
      nlinarith only [hlog, hmul]
    have hscaled := mul_le_mul_of_nonneg_right hh (show 0 ≤ 4 * S p t by positivity)
    rw [← hs₂] at hscaled ⊢
    nlinarith only [hscaled]
  have hm := mul_le_mul_of_nonneg_left h₂ ht
  have hn : 0 ≤ S₁ p t := (by positivity : 0 ≤ S p t / 2).trans h₁
  linarith only [h₁, hm, hn]

/-- The raw powers of the last scaled gap, whose support is the interval `[0,3]`. -/
def shortGapRawMoment (p n : ℕ) : ℝ :=
  ((gaps p).map fun g ↦ exponent p g ^ n).sum / gapCount p

/-- The last-coordinate marginal counts exactly `p+1-i` compositions
with last coordinate `i`. -/
theorem shortGapRawMoment_grid (p n : ℕ) :
    shortGapRawMoment p n =
      (∑ i ∈ Finset.range (p+1), ((p : ℝ)+1-i)*(spacing p*i)^n) / gapCount p := by
  let F : Gap → ℝ := fun g ↦ exponent p g ^ n
  have hCycle := ((DimThree.gaps_cycle_all p).map F).sum_eq
  simp only [List.map_map, Function.comp_def] at hCycle
  unfold shortGapRawMoment
  change ((gaps p).map F).sum / gapCount p = _
  rw [← hCycle]
  change ((gaps p).map (fun g ↦ (3 * (g.1 : ℝ) / p)^n)).sum / gapCount p = _
  congr 1
  have hflat (L : List ℕ) (f : ℕ → List ℝ) :
      (L.flatMap f).sum = (L.map fun i ↦ (f i).sum).sum := by
    induction L with
    | nil => simp
    | cons i L ih => simp [List.flatMap_cons, List.sum_append, ih]
  have hlist (f : ℕ → ℝ) (m : ℕ) :
      ((List.range m).map f).sum = ∑ i ∈ Finset.range m, f i := by
    induction m with
    | zero => simp
    | succ m ih => simp [List.range_succ, List.sum_append, Finset.sum_range_succ, ih]
  rw [gaps, List.map_flatMap, hflat, hlist]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hi' : i ≤ p+1 := (Finset.mem_range.mp hi).le
  simp only [List.map_map, Function.comp_def, List.map_const', List.length_range]
  rw [List.sum_replicate, nsmul_eq_mul, Nat.cast_sub hi', Nat.cast_add, Nat.cast_one]
  unfold spacing
  rw [mul_div_right_comm]

/-- Multiplying the marginal by the short-gap scale gives its weighted grid sum. -/
theorem shortGapScaledMoment_grid {p : ℕ} (hp : 0 < p) (n : ℕ) :
    let h : ℝ := 3 / (p : ℝ)
    (3 + h) * (3 + 2 * h) / 2 * (shortGapRawMoment p n - 1) =
      h * (∑ i ∈ Finset.range (p + 1), (3 + h - h * i) * (h * i) ^ n) -
        (3 + h) * (3 + 2 * h) / 2 := by
  let h := spacing p
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hgrid : h * (p : ℝ) = 3 := div_mul_cancel₀ 3 hpR
  have hscale : scale p = gapCount p * h ^ 2 := by
    change scale p = ((gaps p).length : ℝ) * h ^ 2
    rw [DimThree.gaps_length_eq_choose, Nat.cast_choose_two]
    dsimp [h]
    push_cast
    field_simp
    ring
  change scale p * (shortGapRawMoment p n - 1) = _
  rw [shortGapRawMoment_grid]
  calc
    _ = h ^ 2 * (∑ i ∈ Finset.range (p + 1), ((p : ℝ) + 1 - i) * (h * i) ^ n) -
          scale p := by
      rw [mul_sub, mul_one]
      congr 1
      rw [hscale]
      field_simp [(gapCount_pos p).ne']
      congr 1
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [show (i : ℝ) * 3 / p = h * i by dsimp [h]; ring]
    _ = _ := by
      have hsum : h * (∑ i ∈ Finset.range (p + 1), ((p : ℝ) + 1 - i) * (h * i) ^ n) =
          ∑ i ∈ Finset.range (p + 1), (3 + h - h * i) * (h * i) ^ n := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [← mul_assoc, mul_sub, mul_add, hgrid, mul_one]
      rw [pow_two, mul_assoc, hsum]

private theorem rawMoment_small {p : ℕ} (hp : 0 < p) :
    shortGapRawMoment p 0 = 1 ∧ shortGapRawMoment p 1 = 1 ∧
    shortGapRawMoment p 2 - 1 = compositionMarginalVariance p ∧
    shortGapRawMoment p 3 - 1 = compositionMarginalVariance p * (17 + spacing p) / 5 ∧
    shortGapRawMoment p 4 = (3 + spacing p) * (18 + 12 * spacing p - spacing p ^ 2) / 10 := by
  let N := gapCount p
  let h := spacing p
  let C (n : ℕ) := ((gaps p).map fun g ↦ centered p g ^ n).sum
  have hN : 0 < N := gapCount_pos p
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have h0 : C 0 = N := by simp [C, N]
  have h1 : C 1 = 0 := by simpa [C] using (centered_marginal_sums hp).1
  have h2 : C 2 = N * ((1 + h) / 2) := by
    dsimp [C, N, h]
    rw [(centered_marginal_sums hp).2]
    field_simp [hpR]
  have h3 : C 3 = N * ((1 + h) * (2 + h) / 10) := by
    dsimp [C, N, h]
    rw [centered_marginal_cubic_sum hp]
    field_simp [hpR]
  have h4 : C 4 = N * ((1 + h) * (6 + 6 * h - h ^ 2) / 10) := by
    have hcoeff : normalizedMomentCoeffs 0 4 = [1 / 10, 1 / 10, -1 / 60, 0, 0] := by
      have hn : certifiedMomentNumerators 0 4 = [1728, 1728, -288, 0, 0] := by decide
      rw [← certifiedMomentCoeffs_eq, certifiedMomentCoeffs, hn]
      norm_num [certifiedMomentDenominator, Nat.factorial]
    have hm := normalized_moment_eval_marginal hp 2
    change momentHorner h (normalizedMomentCoeffs 0 4) = C 4 / (N * varianceHalf p *
      (((4 : ℕ).factorial : ℝ))) at hm
    unfold varianceHalf at hm
    rw [hcoeff, variance_eq hp] at hm
    change _ = C 4 / (N * ((1 + h) / 2 / 2) * (((4 : ℕ).factorial : ℝ))) at hm
    norm_num [momentHorner, Nat.factorial] at hm
    have hpos : 0 < 1 + h := by positivity
    have heq : N * ((1 + h) / 2 / 2) * 24 ≠ 0 := by positivity
    have hm' := (eq_div_iff heq).mp hm
    linear_combination (norm := ring) -hm'
  have hexp (g : Gap) : exponent p g = centered p g + 1 := by ring
  have hsum (k : ℕ) (l : List Gap) :
      (l.map fun g ↦ exponent p g ^ k).sum =
        ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
          (l.map fun g ↦ centered p g ^ i).sum := by
    induction l with
    | nil => simp
    | cons g l ih =>
      simp only [List.map_cons, List.sum_cons, mul_add, Finset.sum_add_distrib, ih]
      congr 1
      rw [hexp, add_pow]
      apply Finset.sum_congr rfl
      intro i _
      simp [mul_comm]
  have hraw (k : ℕ) : shortGapRawMoment p k =
      (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * C i) / N :=
    congrArg (· / N) (hsum k (gaps p))
  simp only [hraw, variance_eq hp, show spacing p = h from rfl]
  norm_num [Finset.sum_range_succ, h0, h1, h2, h3, h4, Nat.choose, hN.ne']
  constructor
  · field_simp [hN.ne']
    ring
  constructor <;> field_simp [hN.ne'] <;> ring

private theorem exponent_mem {p : ℕ} (hp : 0 < p) {g : Gap} (hg : g ∈ gaps p) :
    exponent p g ∈ Icc (0 : ℝ) 3 := by
  have hsum := (mem_gaps_iff_total p g).mp hg
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  have hj : (g.2.2 : ℝ) ≤ p := by exact_mod_cast (show g.2.2 ≤ p by omega)
  exact ⟨by positivity, (div_le_iff₀ hpR).2 (by linarith)⟩

private theorem rawMoment_ge_four_le {p : ℕ} (hp : 0 < p) (n : ℕ) :
    shortGapRawMoment p (n + 4) ≤ shortGapRawMoment p 4 * (3 : ℝ) ^ n := by
  have hsum (l : List Gap) (hl : ∀ g ∈ l, exponent p g ∈ Icc (0 : ℝ) 3) :
      (l.map fun g ↦ exponent p g ^ (n + 4)).sum ≤
        (l.map fun g ↦ exponent p g ^ 4 * (3 : ℝ) ^ n).sum := by
    induction l with
    | nil => simp
    | cons g l ih =>
      have hg := hl g (by simp)
      simp only [List.map_cons, List.sum_cons]
      apply add_le_add _ (ih fun j hj ↦ hl j (List.mem_cons_of_mem _ hj))
      rw [add_comm n 4, pow_add]
      gcongr
      exact hg.2
  have h := hsum (gaps p) (fun _ hg ↦ exponent_mem hp hg)
  rw [List.sum_map_mul_right] at h
  simpa only [shortGapRawMoment, mul_div_right_comm] using
    div_le_div_of_nonneg_right h (gapCount_pos p).le

/-- The exact coefficientwise majorant for the square of the marginal slope. -/
theorem shortGapRawMoment_majorant {p : ℕ} (hp : 11 ≤ p) (n : ℕ) :
    (shortGapRawMoment p (n + 2) - 1) *
        (1 + 2 / (((n : ℝ) + 1) * ((n : ℝ) + 2))) ≤
      2 * compositionMarginalVariance p * (3 : ℝ) ^ n := by
  have hp₀ : 0 < p := by omega
  obtain ⟨_, _, h2, h3, h4⟩ := rawMoment_small hp₀
  let h := spacing p
  let v := compositionMarginalVariance p
  have hv : 0 < v := compositionMarginalVariance_pos p
  have hh₀ : 0 ≤ h := by positivity
  have hpR : (11 : ℝ) ≤ p := by exact_mod_cast hp
  have hh₁ : h ≤ 1 := (div_le_iff₀ (show 0 < (p : ℝ) by linarith)).2 (by linarith)
  have h4' : shortGapRawMoment p 4 ≤ 12 * v := by
    rw [h4, show spacing p = h from rfl, show v = (1 + h) / 2 from variance_eq hp₀]
    have hs := mul_nonneg hh₀ (sub_nonneg.mpr hh₁)
    nlinarith only [hs, mul_nonneg hh₀ (sq_nonneg h), hh₀, hh₁]
  match n with
  | 0 =>
    norm_num [h2]
    rw [mul_comm]
  | 1 =>
    norm_num [h3]
    have hb := mul_le_mul_of_nonneg_left hh₁ hv.le
    change (v * (17 + h) / 5) * (4 / 3) ≤ 2 * v * 3
    nlinarith only [hb, hv]
  | n + 2 =>
    have hn₀ : 0 ≤ (n : ℝ) := by positivity
    have hd : (12 : ℝ) ≤ ((n : ℝ) + 2 + 1) * ((n : ℝ) + 2 + 2) := by
      nlinarith only [hn₀, sq_nonneg (n : ℝ)]
    have hf : (2 : ℝ) / (((n : ℝ) + 2 + 1) * ((n : ℝ) + 2 + 2)) ≤ 2 / 12 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hd
    have hg : shortGapRawMoment p (n + 4) ≤ 12 * v * (3 : ℝ) ^ n :=
      (rawMoment_ge_four_le hp₀ n).trans (mul_le_mul_of_nonneg_right h4' (by positivity))
    simp only [Nat.cast_add, Nat.cast_ofNat]
    change (shortGapRawMoment p (n + 4) - 1) *
        (1 + 2 / (((n : ℝ) + 2 + 1) * ((n : ℝ) + 2 + 2))) ≤ 2 * v * (3 : ℝ) ^ (n + 2)
    calc
      _ ≤ (12 * v * (3 : ℝ) ^ n) * (1 + 2 / 12) :=
        mul_le_mul (by linarith only [hg]) (add_le_add_right hf 1) (by positivity) (by positivity)
      _ ≤ _ := by
        rw [pow_add]
        have hpw : 0 ≤ v * (3 : ℝ) ^ n := by positivity
        nlinarith only [hpw]

private def rawExp (p k : ℕ) (t : ℝ) : ℝ :=
  ((gaps p).map fun g ↦ exponent p g ^ k * Real.exp (t * exponent p g)).sum /
    gapCount p - Real.exp t

private theorem hasDerivAt_rawExp (p k : ℕ) (t : ℝ) :
    HasDerivAt (rawExp p k) (rawExp p (k + 1) t) t := by
  have h (l : List Gap) :
      HasDerivAt (fun x ↦ (l.map fun g ↦ exponent p g ^ k * Real.exp (x * exponent p g)).sum)
        ((l.map fun g ↦ exponent p g ^ (k + 1) * Real.exp (t * exponent p g)).sum) t := by
    induction l with
    | nil => simpa using hasDerivAt_const t (0 : ℝ)
    | cons g l ih =>
      have hg := (((hasDerivAt_id' t).mul_const (exponent p g)).exp).const_mul (exponent p g ^ k)
      have hg' : HasDerivAt (fun x ↦ exponent p g ^ k * Real.exp (x * exponent p g))
          (exponent p g ^ (k + 1) * Real.exp (t * exponent p g)) t :=
        hg.congr_deriv (by simp only [pow_succ]; ring)
      simpa only [List.map_cons, List.sum_cons, Pi.add_def] using hg'.add ih
  exact ((h (gaps p)).div_const _).sub (Real.hasDerivAt_exp t)

private theorem t_sq_mul_U_eq_rawExp {p : ℕ} (hp : 0 < p) (t : ℝ) :
    t ^ 2 * U p t = scale p * rawExp p 0 t := by
  by_cases ht : t = 0
  · simp [ht, rawExp, (gapCount_pos p).ne']
  rw [t_sq_mul_U hp ht]
  unfold rawExp compositionMoment
  simp only [mul_zero, zero_add, pow_zero, one_mul]
  rw [mul_assoc, mul_sub]
  congr 1
  rw [mul_one]
  congr 1
  rw [← mul_div_assoc, ← List.sum_map_mul_left]
  congr 2
  apply congrArg (fun f : Gap → ℝ ↦ List.map f (gaps p))
  funext g
  rw [← Real.exp_add]
  congr 1
  change t + centered p g * t = t * exponent p g
  ring

private theorem U_majorant_eq_rawExp {p : ℕ} (hp : 0 < p) (t : ℝ) :
    U p t + t * U₁ p t + t ^ 2 * U₂ p t / 4 =
      U p t / 2 + scale p * rawExp p 2 t / 4 := by
  have h₁ (x : ℝ) : 2 * x * U p x + x ^ 2 * U₁ p x = scale p * rawExp p 1 x := by
    have hd := ((hasDerivAt_pow 2 x).mul (hasDerivAt_U p x)).deriv
    have hd' := ((hasDerivAt_rawExp p 0 x).const_mul (scale p)).deriv
    change deriv (fun y ↦ y ^ 2 * U p y) x = _ at hd
    rw [funext (t_sq_mul_U_eq_rawExp hp), hd'] at hd
    simpa using hd.symm
  have hd := ((((hasDerivAt_id' t).const_mul 2).mul (hasDerivAt_U p t)).add
    ((hasDerivAt_pow 2 t).mul (hasDerivAt_U₁ p t))).deriv
  change deriv (fun x ↦ 2 * x * U p x + x ^ 2 * U₁ p x) t = _ at hd
  rw [funext h₁, ((hasDerivAt_rawExp p 1 t).const_mul (scale p)).deriv] at hd
  norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one, id_eq, mul_one] at hd
  linear_combination (norm := ring) -hd / 4

private theorem hasSum_realExp (x : ℝ) :
    HasSum (fun n : ℕ ↦ x ^ n / (n.factorial : ℝ)) (Real.exp x) := by
  rw [Real.exp_eq_exp_ℝ]
  exact NormedSpace.expSeries_div_hasSum_exp x

private theorem hasSum_rawExp (p k : ℕ) (t : ℝ) :
    HasSum (fun n : ℕ ↦ (shortGapRawMoment p (n + k) - 1) * (t ^ n / (n.factorial : ℝ)))
      (rawExp p k t) := by
  have h (l : List Gap) : HasSum
      (fun n : ℕ ↦ (l.map fun g ↦ exponent p g ^ (n + k)).sum * (t ^ n / (n.factorial : ℝ)))
      (l.map fun g ↦ exponent p g ^ k * Real.exp (t * exponent p g)).sum := by
    induction l with
    | nil => simp
    | cons g l ih =>
      have hg := (hasSum_realExp (t * exponent p g)).mul_left (exponent p g ^ k)
      refine (hg.add ih).congr_fun fun n ↦ ?_
      simp only [List.map_cons, List.sum_cons, mul_pow, pow_add]
      ring
  refine (((h (gaps p)).div_const (gapCount p)).sub (hasSum_realExp t)).congr_fun
    fun n ↦ ?_
  unfold shortGapRawMoment
  ring

private theorem hasSum_U {p : ℕ} (hp : 0 < p) {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℕ ↦ scale p * (shortGapRawMoment p (n + 2) - 1) *
      (t ^ n / ((n + 2).factorial : ℝ))) (U p t) := by
  obtain ⟨h0, h1, _, _, _⟩ := rawMoment_small hp
  have h := (hasSum_nat_add_iff' 2).2 (hasSum_rawExp p 0 t)
  simp only [add_zero, Finset.sum_range_succ, Finset.sum_range_zero,
    h0, h1, sub_self, zero_mul, sub_zero] at h
  have ht₂ : t ^ 2 ≠ 0 := pow_ne_zero _ ht.ne'
  have hh := (h.mul_left (scale p)).div_const (t ^ 2)
  rw [← t_sq_mul_U_eq_rawExp hp t, mul_comm (t ^ 2), mul_div_cancel_right₀ _ ht₂] at hh
  refine hh.congr_fun fun n ↦ ?_
  rw [pow_add]
  field_simp [ht.ne']

private theorem rawExp_one_eq_U {p : ℕ} (hp : 0 < p) (t : ℝ) :
    scale p * rawExp p 1 t = 2*t*U p t + t^2*U₁ p t := by
  have hd := ((hasDerivAt_pow 2 t).mul (hasDerivAt_U p t)).deriv
  have hd' := ((hasDerivAt_rawExp p 0 t).const_mul (scale p)).deriv
  change deriv (fun x ↦ x^2 * U p x) t = _ at hd
  rw [funext (t_sq_mul_U_eq_rawExp hp), hd'] at hd
  simpa using hd

private theorem rawExp_two_eq_U {p : ℕ} (hp : 0 < p) (t : ℝ) :
    scale p * rawExp p 2 t = 2*U p t + 4*t*U₁ p t + t^2*U₂ p t := by
  have hd := ((((hasDerivAt_id' t).const_mul 2).mul (hasDerivAt_U p t)).add
    ((hasDerivAt_pow 2 t).mul (hasDerivAt_U₁ p t))).deriv
  change deriv (fun x ↦ 2*x*U p x + x^2*U₁ p x) t = _ at hd
  rw [← funext (rawExp_one_eq_U hp), ((hasDerivAt_rawExp p 1 t).const_mul (scale p)).deriv] at hd
  norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one, id_eq, mul_one] at hd
  linear_combination hd

private theorem hasSum_U₁ {p : ℕ} (hp : 0 < p) {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℕ ↦ scale p * (shortGapRawMoment p (n + 3) - 1) *
      (t^n / ((n+2 : ℝ)*(n+3)*(n.factorial : ℝ)))) (U₁ p t) := by
  obtain ⟨_, h1, _, _, _⟩ := rawMoment_small hp
  have h := (hasSum_nat_add_iff' 1).2 (hasSum_rawExp p 1 t)
  simp only [Finset.sum_range_one, zero_add, h1, sub_self, zero_mul, sub_zero] at h
  have ht₀ := ht.ne'
  have H := ((((h.mul_left (scale p)).div_const t).sub
    ((hasSum_U hp ht).mul_left 2)).div_const t)
  rw [rawExp_one_eq_U hp t] at H
  have hvalue : ((2*t*U p t + t^2*U₁ p t)/t - 2*U p t)/t = U₁ p t := by
    field_simp [ht₀] <;> ring
  rw [hvalue] at H
  have Htail := (hasSum_nat_add_iff' 1).2 H
  simp only [Finset.sum_range_one, zero_add, Nat.factorial_zero, Nat.factorial_succ,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_zero, pow_zero, pow_one] at Htail
  convert Htail using 1
  · funext n
    have hn : (n.factorial : ℝ) ≠ 0 := by positivity
    simp only [Nat.add_assoc]
    norm_num only [Nat.cast_ofNat]
    simp only [pow_succ]
    field_simp [ht₀, hn] <;> ring
  · norm_num
    field_simp [ht₀] <;> ring

private theorem hasSum_U₂ {p : ℕ} (hp : 0 < p) {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℕ ↦ scale p * (shortGapRawMoment p (n+4) - 1) *
      (t^n / ((n+3 : ℝ)*(n+4)*(n.factorial : ℝ)))) (U₂ p t) := by
  let A (n : ℕ) : ℝ := scale p * (shortGapRawMoment p (n+2) - 1) *
    (t^n / ((n+2).factorial : ℝ))
  have ht₀ := ht.ne'
  have H₀ : HasSum A (U p t) := hasSum_U hp ht
  have H₁ : HasSum (fun n : ℕ ↦ (n : ℝ)*A n) (t*U₁ p t) := by
    apply (hasSum_nat_add_iff' 1).1
    simp only [Finset.sum_range_one, Nat.cast_zero, zero_mul, sub_zero]
    refine ((hasSum_U₁ hp ht).mul_left t).congr_fun fun n ↦ ?_
    have hn : (n.factorial : ℝ) ≠ 0 := by positivity
    unfold A
    simp only [Nat.add_assoc, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
      Nat.cast_one, Nat.cast_ofNat, pow_succ]
    field_simp [hn] <;> ring
  have H₂ := (((hasSum_rawExp p 2 t).mul_left (scale p)).sub
    (H₀.mul_left 2)).sub (H₁.mul_left 4)
  rw [rawExp_two_eq_U hp t] at H₂
  have hval : 2*U p t + 4*t*U₁ p t + t^2*U₂ p t - 2*U p t - 4*(t*U₁ p t) = t^2*U₂ p t := by
    ring
  rw [hval] at H₂
  let B (n : ℕ) : ℝ := scale p * ((shortGapRawMoment p (n+2) - 1) *
    (t^n / (n.factorial : ℝ))) - 2*A n - 4*((n : ℝ)*A n)
  change HasSum B (t^2*U₂ p t) at H₂
  have hzero : ∑ i ∈ Finset.range 2, B i = 0 := by
    norm_num [B, A, Finset.sum_range_succ, Nat.factorial]
    ring
  have Htail := (hasSum_nat_add_iff' 2).2 H₂
  rw [hzero, sub_zero] at Htail
  have Hdiv := Htail.div_const (t^2)
  rw [mul_comm (t^2), mul_div_cancel_right₀ _ (pow_ne_zero 2 ht₀)] at Hdiv
  refine Hdiv.congr_fun fun n ↦ ?_
  have hn : (n.factorial : ℝ) ≠ 0 := by positivity
  dsimp only [B, A]
  simp only [Nat.add_assoc, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one, Nat.cast_ofNat, pow_succ]
  field_simp [ht₀, hn] <;> ring

/-- The positive marginal under the root of the short-gap profile. -/
abbrev shortGapProfileU (p : ℕ) : ℝ → ℝ := U p

theorem shortGapProfileU_pos {p : ℕ} (hp : 0 < p) (t : ℝ) :
    0 < shortGapProfileU p t := U_pos hp t

theorem shortGapProfileU_contDiff (p : ℕ) : ContDiff ℝ 2 (shortGapProfileU p) := by
  have h₁ : deriv (U p) = U₁ p := funext fun t ↦ (hasDerivAt_U p t).deriv
  have h₂ : deriv (U₁ p) = U₂ p := funext fun t ↦ (hasDerivAt_U₁ p t).deriv
  have h₃ : Continuous (U₂ p) := by
    unfold U₂ M weight varianceHalf
    have h (k : ℕ) : Continuous (integralMarginalDerivative p (compositionMarginalVariance p / 2) k) :=
      continuous_iff_continuousAt.mpr fun t ↦ (hasDerivAt_M p k t).continuousAt
    fun_prop (disch := exact h _)
  change ContDiff ℝ (1+1) (U p)
  rw [contDiff_succ_iff_deriv, h₁, contDiff_one_iff_deriv, h₂]
  exact ⟨fun t ↦ (hasDerivAt_U p t).differentiableAt, by simp,
    fun t ↦ (hasDerivAt_U₁ p t).differentiableAt, h₃⟩

theorem shortGapProfileU_series {p : ℕ} (hp : 0 < p) {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℕ ↦ scale p * (shortGapRawMoment p (n+2) - 1) *
      (t^n / ((n+2).factorial : ℝ))) (shortGapProfileU p t) ∧
    HasSum (fun n : ℕ ↦ scale p * (shortGapRawMoment p (n+3) - 1) *
      (t^n / ((n+2 : ℝ)*(n+3)*(n.factorial : ℝ)))) (deriv (shortGapProfileU p) t) ∧
    HasSum (fun n : ℕ ↦ scale p * (shortGapRawMoment p (n+4) - 1) *
      (t^n / ((n+3 : ℝ)*(n+4)*(n.factorial : ℝ))))
      (deriv (deriv (shortGapProfileU p)) t) := by
  have h₁ : deriv (shortGapProfileU p) = U₁ p := funext fun s ↦ (hasDerivAt_U p s).deriv
  rw [h₁, (hasDerivAt_U₁ p t).deriv]
  exact ⟨hasSum_U hp ht, hasSum_U₁ hp ht, hasSum_U₂ hp ht⟩

/-- The coefficients of `U` and its derivatives, with argument `t`. -/
noncomputable def shortGapUCoeff (p k n : ℕ) : ℝ :=
  scale p * (shortGapRawMoment p (n+k+2)-1) /
    (((n+k : ℕ) : ℝ)+1) / (((n+k : ℕ) : ℝ)+2) / (n.factorial : ℝ)

private theorem shortGapUCoeff_bounds {p : ℕ} (hp : 11 ≤ p) (k n : ℕ) :
    |shortGapUCoeff p k n| ≤ 3^(k+1) * ((3 : ℝ)^n / (n.factorial : ℝ)) ∧
    |shortGapUCoeff p k n| ≤ (9 * (3 : ℝ) ^ k / ((n : ℝ) + k + 1) /
      ((n : ℝ) + k + 2)) * ((3 : ℝ) ^ n / (n.factorial : ℝ)) := by
  let h := spacing p
  let j := n+k
  have hp₀ : 0 < p := by omega
  have hh : 0 ≤ h := by positivity
  have hhmax : h ≤ 3/11 := by
    have hpR : (11 : ℝ) ≤ p := by exact_mod_cast hp
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hpR
  have hh₁ : h ≤ 1/3 := hhmax.trans (by norm_num)
  have hV : 2*compositionMarginalVariance p = 1+h := by
    rw [variance_eq hp₀]
    ring
  have hN := gapCount_pos p
  have hμ₀ : 0 ≤ shortGapRawMoment p (j+2) := by
    rw [shortGapRawMoment_grid]
    apply div_nonneg (Finset.sum_nonneg fun i hi ↦ ?_) hN.le
    have hi' : (i : ℝ) ≤ (p : ℝ)+1 := by
      exact_mod_cast (Finset.mem_range.mp hi).le
    exact mul_nonneg (sub_nonneg.mpr hi') (pow_nonneg (by positivity) _)
  have hμabs : |shortGapRawMoment p (j+2)-1| ≤ (1+h)*(3 : ℝ)^j := by
    have hM := shortGapRawMoment_majorant hp j
    rw [hV] at hM
    have hfac : 0 ≤ (2 : ℝ) / (((j : ℝ)+1)*((j : ℝ)+2)) := by positivity
    have hpow : (1 : ℝ) ≤ 3^j := one_le_pow₀ (by norm_num)
    have hbound : 1 ≤ (1+h)*(3 : ℝ)^j := by
      exact hpow.trans (le_mul_of_one_le_left (by positivity) (by linarith))
    apply abs_le.mpr
    constructor
    · linarith only [hμ₀, hbound]
    · by_cases hx : 0 ≤ shortGapRawMoment p (j+2)-1
      · nlinarith only [hM, mul_nonneg hx hfac]
      · linarith only [hx, hbound]
  have hC := (scale_pos p).le
  have hCmax : scale p*(1+h) ≤ 9 := by
    have hstep : (3+h)*(3+2*h)*(1+h) ≤ (10/3 : ℝ)*(11/3)*(4/3) := by
      gcongr <;> linarith
    change (3+h)*(3+2*h)/2*(1+h) ≤ 9
    nlinarith only [hstep]
  have hraw : scale p * |shortGapRawMoment p (j+2)-1| ≤ 9 * (3 : ℝ)^j := calc
    _ ≤ scale p * ((1+h)*(3 : ℝ)^j) := mul_le_mul_of_nonneg_left hμabs hC
    _ = (scale p * (1+h)) * (3 : ℝ)^j := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hCmax (by positivity)
  have hbudget : scale p*|shortGapRawMoment p (j+2)-1| ≤ 3*(3 : ℝ)^j*((j : ℝ)+1)*((j : ℝ)+2) := by
    by_cases hzero : j = 0
    · rw [hzero]
      obtain ⟨_, _, hm, _, _⟩ := rawMoment_small hp₀
      norm_num only [zero_add, Nat.cast_zero, pow_zero] 
      rw [hm, abs_of_nonneg (compositionMarginalVariance_pos p).le]
      linarith only [hCmax, show scale p*(1+h) = 2*(scale p*compositionMarginalVariance p) by
        rw [← hV]; ring]
    · have hjn : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hzero
      have hd : (3 : ℝ) ≤ ((j : ℝ)+1)*((j : ℝ)+2) := by
        nlinarith only [hjn, sq_nonneg (j : ℝ)]
      refine hraw.trans ?_
      rw [mul_assoc]
      convert mul_le_mul_of_nonneg_right hd (show 0 ≤ 3*(3 : ℝ)^j by positivity) using 1 <;> ring
  have habs : |shortGapUCoeff p k n| =
      scale p * |shortGapRawMoment p (j+2)-1| / ((j : ℝ)+1) /
        ((j : ℝ)+2) / (n.factorial : ℝ) := by
    change |scale p*(shortGapRawMoment p (j+2)-1)/((j : ℝ)+1)/((j : ℝ)+2)/(n.factorial : ℝ)| = _
    rw [abs_div, abs_div, abs_div, abs_mul, abs_of_nonneg hC,
    abs_of_nonneg (by positivity : 0 ≤ (j : ℝ)+1),
    abs_of_nonneg (by positivity : 0 ≤ (j : ℝ)+2), abs_of_nonneg (by positivity : 0 ≤ (n.factorial : ℝ))]
  rw [habs]
  constructor
  · rw [div_le_iff₀ (by positivity), div_le_iff₀ (by positivity), div_le_iff₀ (by positivity)]
    convert hbudget using 1
    dsimp [j]
    rw [pow_add (3 : ℝ) n k, pow_succ]
    field_simp [(show (n.factorial : ℝ) ≠ 0 by positivity)]
  · refine (div_le_div_of_nonneg_right (div_le_div_of_nonneg_right
      (div_le_div_of_nonneg_right hraw (by positivity)) (by positivity)) (by positivity)).trans_eq ?_
    dsimp only [j]
    rw [pow_add, Nat.cast_add]
    ring

theorem shortGapUCoeff_majorant {p : ℕ} (hp : 11 ≤ p) (k n : ℕ) :
    |shortGapUCoeff p k n| ≤ 3^(k+1) * ((3 : ℝ)^n / (n.factorial : ℝ)) :=
  (shortGapUCoeff_bounds hp k n).1

/-- The factorial denominator gives a sharper estimate for the late marginal coefficients. -/
theorem shortGapUCoeff_tail_majorant {p : ℕ} (hp : 11 ≤ p) (k : ℕ) {n : ℕ} (hn : 19 ≤ n) :
    |shortGapUCoeff p k n| ≤ (9 * (3 : ℝ)^k / (20 + k) / (21 + k)) *
      ((3 : ℝ)^n / (n.factorial : ℝ)) := by
  have hn' : (19 : ℝ) ≤ n := by exact_mod_cast hn
  refine (shortGapUCoeff_bounds hp k n).2.trans ?_
  have h20 : (20 : ℝ) + k ≤ (n : ℝ) + k + 1 := by linarith
  have h21 : (21 : ℝ) + k ≤ (n : ℝ) + k + 2 := by linarith
  gcongr

private theorem U_majorant_le {p : ℕ} (hp : 11 ≤ p) {t : ℝ} (ht : 0 < t) :
    U p t + t * U₁ p t + t ^ 2 * U₂ p t / 4 ≤ scale p * varianceHalf p * Real.exp (3 * t) := by
  have hp₀ : 0 < p := by omega
  rw [U_majorant_eq_rawExp hp₀]
  have hl := ((hasSum_U hp₀ ht).div_const 2).add
    (((hasSum_rawExp p 2 t).mul_left (scale p)).div_const 4)
  have hr := (hasSum_realExp (3 * t)).mul_left (scale p * varianceHalf p)
  rw [← hl.tsum_eq, ← hr.tsum_eq]
  apply Summable.tsum_le_tsum _ hl.summable hr.summable
  intro n
  have hfac : 0 < (n.factorial : ℝ) := by exact_mod_cast n.factorial_pos
  have hden : 0 < ((n : ℝ) + 1) * ((n : ℝ) + 2) := by positivity
  have h := mul_le_mul_of_nonneg_left (shortGapRawMoment_majorant hp n)
    (show 0 ≤ scale p * (t ^ n / (n.factorial : ℝ)) / 4 by
      exact div_nonneg (mul_nonneg (scale_pos p).le (by positivity)) (by norm_num))
  have hfactorial : (((n + 2).factorial : ℕ) : ℝ) =
      (n.factorial : ℝ) * (((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
    rw [show n + 2 = (n + 1) + 1 by omega, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring
  have hv : compositionMarginalVariance p = 2 * varianceHalf p := by unfold varianceHalf; ring
  change scale p * (shortGapRawMoment p (n + 2) - 1) *
      (t ^ n / ((n + 2).factorial : ℝ)) / 2 +
      scale p * ((shortGapRawMoment p (n + 2) - 1) * (t ^ n / (n.factorial : ℝ))) / 4 ≤
      scale p * varianceHalf p * ((3 * t) ^ n / (n.factorial : ℝ))
  rw [hfactorial, mul_pow]
  rw [hv] at h
  have heq : scale p * (shortGapRawMoment p (n + 2) - 1) *
      (t ^ n / ((n.factorial : ℝ) * (((n : ℝ) + 1) * ((n : ℝ) + 2)))) / 2 +
      scale p * ((shortGapRawMoment p (n + 2) - 1) * (t ^ n / (n.factorial : ℝ))) / 4 =
      (scale p * (t ^ n / (n.factorial : ℝ)) / 4) *
        ((shortGapRawMoment p (n + 2) - 1) *
          (1 + 2 / (((n : ℝ) + 1) * ((n : ℝ) + 2)))) := by
    field_simp [hden.ne', hfac.ne']
    ring
  rw [heq]
  exact h.trans_eq (by ring)

private theorem slope_square_le {p : ℕ} (hp : 0 < p) (t : ℝ) :
    deriv (shortGapJ p) t ^ 2 ≤ U p t + t * U₁ p t + t ^ 2 * U₂ p t / 4 := by
  rw [(hasDerivAt_J hp t).deriv]
  have hs : 0 < S p t := Real.sqrt_pos.2 (U_pos hp t)
  have hs₂ : S p t ^ 2 = U p t := Real.sq_sqrt (U_pos hp t).le
  calc
    _ = U p t + t * U₁ p t + t ^ 2 * U₁ p t ^ 2 / (4 * U p t) := by
      unfold S₁
      rw [← hs₂]
      field_simp [hs.ne']
      ring
    _ ≤ _ := by
      apply add_le_add_right
      rw [div_le_div_iff₀ (mul_pos (by norm_num) (U_pos hp t)) (by norm_num)]
      have hh := mul_le_mul_of_nonneg_left (U_logConvex hp t) (show 0 ≤ 4 * t ^ 2 by positivity)
      nlinarith only [hh]

/-- The upper bound attains equality at the origin of the smooth continuation. -/
theorem shortGapJ_deriv_zero {p : ℕ} (hp : 0 < p) :
    deriv (shortGapJ p) 0 =
      Real.sqrt ((3 + 3 / (p : ℝ)) * (3 + 2 * (3 / (p : ℝ))) * (1 + 3 / (p : ℝ)) / 8) := by
  rw [(hasDerivAt_J hp 0).deriv, zero_mul, add_zero]
  unfold S U weight
  rw [M_mass_zero, Real.exp_zero, mul_one, mul_one]
  unfold varianceHalf scale spacing
  rw [variance_eq hp]
  congr 1
  ring

/-- Sharp upper bound for the marginal slope on the entire nonnegative gap axis. -/
theorem shortGapJ_deriv_le {p : ℕ} (hp : 11 ≤ p) {t : ℝ} (ht : 0 ≤ t) :
    deriv (shortGapJ p) t ≤
      Real.sqrt ((3 + 3 / (p : ℝ)) * (3 + 2 * (3 / (p : ℝ))) * (1 + 3 / (p : ℝ)) / 8) *
        Real.exp (3 * t / 2) := by
  have hp₀ : 0 < p := by omega
  obtain rfl | ht' := ht.eq_or_lt
  · rw [shortGapJ_deriv_zero hp₀]
    simp
  have hconstant : scale p * varianceHalf p =
      (3 + 3 / (p : ℝ)) * (3 + 2 * (3 / (p : ℝ))) * (1 + 3 / (p : ℝ)) / 8 := by
    unfold varianceHalf scale spacing
    rw [variance_eq hp₀]
    ring
  have hc : 0 ≤ scale p * varianceHalf p :=
    (mul_pos (scale_pos p) (varianceHalf_pos p)).le
  rw [← hconstant]
  apply le_of_sq_le_sq _ (by positivity)
  rw [mul_pow, Real.sq_sqrt hc, ← Real.exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  rw [show (2 : ℝ) * (3 * t / 2) = 3 * t by ring]
  exact (slope_square_le hp₀ t).trans (U_majorant_le hp ht')

#print axioms shortGapJ_deriv_zero
#print axioms shortGapJ_deriv_le
#print axioms shortGapRawMoment_majorant
#print axioms shortGapJ_eq_sqrt
#print axioms shortGapJ_deriv_pos
#print axioms shortGapJ_deriv_half_le_second

end RefinedBMV.PositiveCenter
