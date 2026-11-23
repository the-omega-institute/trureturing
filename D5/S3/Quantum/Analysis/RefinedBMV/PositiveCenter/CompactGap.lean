/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/CompactGap
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact scaled kernel for the centered compact-gap Taylor calculation. -/

import D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterTailJet
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CollisionRadicand
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.ShortGapNormalization
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.ShortGapSign
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.ShortGapCorrection
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.ShortGapJ
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.ShortGapReplay

/-! # The centered Taylor formula for the positive-center kernel -/

open Filter
open scoped Topology

namespace RefinedBMV.PositiveCenter.CompactGap

private noncomputable def rate (p : ℕ) : ℝ := 3 / (p : ℝ)
private noncomputable def node (p : ℕ) (t : ℝ) : ℝ := Real.exp (-t / (p : ℝ))
private noncomputable def c (h : ℝ) : ℝ := (3+h)*(3+2*h)/2

private noncomputable def R (h t : ℝ) : ℝ :=
  Real.exp (-((3+2*h)*t)) - 1 + (3+2*h)*upperTailGap h t

private noncomputable def W (h t : ℝ) : ℝ :=
  R h t - c h * (upperTailGap h t)^2 * Real.exp (-t)

private noncomputable def X (h t : ℝ) : ℝ := 1 - upperTailLambda h t

/-- The expression evaluated by the centered Taylor replay, with the
lower coordinate and the gap independent. -/
noncomputable def G (h u d : ℝ) : ℝ :=
  let v := d+u
  let a := upperTailGap h
  Real.exp (2*d) *
    (a u * (1 - upperTailRepeatCorrection h d - Real.sqrt (X h d)*Real.sqrt (X h v) -
      c h*a v*a d*Real.exp (-(v+d))) + a d*Real.exp (-((3+h)*d))*R h u) /
    (a d*Real.sqrt (W h u)*Real.sqrt (W h v))

/-- The same expression with the removable division by the upper gap eliminated. -/
noncomputable def GAtUpperCollision (h u d : ℝ) : ℝ :=
  let v := d+u
  let a := upperTailGap h
  let q := (3+h)*(3+2*h)*(1+h)
  let j := collisionRepeatDefect h d
  let s := Real.sqrt (q * collisionRadicand h d) * Real.sqrt (X h v)
  Real.exp (2*d) *
    (a u * (d*(j-s)/expGapMean h d - c h*a v*Real.exp (-(v+d))) +
      Real.exp (-((3+h)*d))*R h u) /
    (Real.sqrt (W h u)*Real.sqrt (W h v))

theorem G_eq_GAtUpperCollision {h u d : ℝ} (hh : 0 < h) (hd : 0 < d) :
    G h u d = GAtUpperCollision h u d := by
  let q : ℝ := (3+h)*(3+2*h)*(1+h)
  have hx : X h d = d^4 * (q * collisionRadicand h d) := by
    unfold X
    rw [one_sub_upperTailLambda_eq_collisionRadicand hh]
    dsimp [q]
    ring
  have hroot : Real.sqrt (X h d) = d^2 * Real.sqrt (q*collisionRadicand h d) := by
    rw [hx, show d^4 = (d^2)^2 by ring, Real.sqrt_mul (sq_nonneg _),
      Real.sqrt_sq (sq_nonneg d)]
  have hmean := expGapMean_pos h d
  have hgap : 0 < upperTailGap h d := by
    rw [expGapMean_eq hh]
    exact mul_pos hd hmean
  have hquot :
      d^2 / upperTailGap h d = d / expGapMean h d := by
    rw [expGapMean_eq hh]
    field_simp [hmean.ne', hd.ne']
  unfold G GAtUpperCollision
  dsimp only
  rw [hroot, one_sub_upperTailRepeatCorrection_eq_collisionRepeatDefect hh]
  calc
    _ = Real.exp (2*d) *
          (upperTailGap h u * (d^2 / upperTailGap h d *
            (collisionRepeatDefect h d - Real.sqrt (q*collisionRadicand h d)*Real.sqrt (X h (d+u))) -
            c h*upperTailGap h (d+u)*Real.exp (-((d+u)+d))) +
            Real.exp (-((3+h)*d))*R h u) /
          (Real.sqrt (W h u)*Real.sqrt (W h (d+u))) := by
      rw [show upperTailGap h d * Real.sqrt (W h u) * Real.sqrt (W h (d+u)) =
        upperTailGap h d * (Real.sqrt (W h u)*Real.sqrt (W h (d+u))) by ring, div_mul_eq_div_div]
      congr 1
      field_simp [hgap.ne']
      <;> ring
    _ = _ := by rw [hquot, div_mul_eq_mul_div]

private theorem rate_pos {p : ℕ} (hp : 0 < p) : 0 < rate p := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  unfold rate
  positivity

private theorem node_cube (p : ℕ) (t : ℝ) :
    node p t ^ 3 = Real.exp (-(rate p*t)) := by
  rw [node, ← Real.exp_nat_mul]
  congr 1
  unfold rate
  push_cast
  ring

private theorem node_pow {p : ℕ} (hp : 0 < p) (t : ℝ) :
    node p t ^ p = Real.exp (-t) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  rw [node, ← Real.exp_nat_mul]
  congr 1
  field_simp

private theorem gap_factor (p : ℕ) (t : ℝ) :
    1 - node p t ^ 3 = rate p * upperTailGap (rate p) t := by
  by_cases hp : p = 0
  · simp [hp, node, rate, upperTailGap]
  · have hh := (rate_pos (Nat.pos_of_ne_zero hp)).ne'
    rw [node_cube, upperTailGap, mul_div_cancel₀ _ hh]

private theorem node_lt_one {p : ℕ} (hp : 0 < p) {t : ℝ} (ht : 0 < t) :
    node p t < 1 := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  exact Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (neg_neg_of_pos ht) hpR)

private theorem node_gap_pos {p : ℕ} (hp : 0 < p) {t : ℝ} (ht : 0 < t) :
    0 < 1 - node p t ^ 3 := by
  rw [node_cube]
  exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos (mul_pos (rate_pos hp) ht)))

private theorem gap_pos {p : ℕ} (hp : 0 < p) {t : ℝ} (ht : 0 < t) :
    0 < upperTailGap (rate p) t := by
  have hg := node_gap_pos hp ht
  rw [gap_factor] at hg
  exact (mul_pos_iff_of_pos_left (rate_pos hp)).mp hg

private theorem cast_scale {p : ℕ} (hp : 0 < p) :
    ((p+2 : ℕ) : ℝ) * rate p = 3 + 2*rate p ∧
      ((p+2).choose 2 : ℝ) * rate p ^ 2 = c (rate p) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  constructor
  · unfold rate
    push_cast
    field_simp
  · rw [Nat.cast_choose_two]
    unfold c rate
    push_cast
    field_simp
    ring

private theorem W_eq_defect {p : ℕ} (hp : 0 < p) (t : ℝ) :
    (1-node p t^3)^2 * DimThree.defect p (node p t) 1 1 = W (rate p) t := by
  let q := node p t ^ 3
  let h := rate p
  have hq : q = Real.exp (-(h*t)) := node_cube p t
  have hgap : 1-q = h*upperTailGap h t := gap_factor p t
  have hpow : q^(p+2) = Real.exp (-((3+2*h)*t)) := by
    change (node p t^3)^(p+2) = _
    rw [pow_add, ← pow_mul, Nat.mul_comm 3 p, pow_mul, node_pow hp,
      show (node p t^3)^2 = Real.exp (-(h*t))^2 by rw [← hq]]
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    push_cast
    ring
  obtain ⟨hk, hc⟩ := cast_scale hp
  change ((p+2 : ℕ) : ℝ)*h = 3+2*h at hk
  change ((p+2).choose 2 : ℝ)*h^2 = c h at hc
  have hclear : (1-q)^2 * DividedDifference.homogeneousThree p q 1 1 =
      Real.exp (-((3+2*h)*t)) - 1 + (3+2*h)*upperTailGap h t := by
    rw [DividedDifference.clear_repeat_last, hpow]
    simp only [one_pow, mul_one, one_mul]
    calc
      _ = Real.exp (-((3+2*h)*t)) - 1 + ((p+2 : ℕ) : ℝ)*(1-q) := by push_cast; ring
      _ = _ := by rw [hgap, ← mul_assoc, hk]
  rw [DividedDifference.defect_eq_homogeneous]
  simp only [one_pow, mul_one, mul_sub, node_pow hp]
  change (1-q)^2 * DividedDifference.homogeneousThree p q 1 1 -
    (1-q)^2 * (((p+2).choose 2 : ℝ)*Real.exp (-t)) = _
  rw [hclear, hgap]
  unfold W R
  linear_combination -(upperTailGap h t)^2*Real.exp (-t)*hc

private theorem W_pos {p : ℕ} (hp : 0 < p) {t : ℝ} (ht : 0 < t) :
    0 < W (rate p) t := by
  rw [← W_eq_defect hp]
  exact mul_pos (sq_pos_of_pos (node_gap_pos hp ht))
    (weight_pos hp (Real.exp_pos _).le (node_lt_one hp ht))

private theorem X_pos {p : ℕ} (hp : 0 < p) {t : ℝ} (ht : 0 < t) :
    0 < X (rate p) t := by
  have hx : (1-node p t^3)^2 * DimThree.defect p (node p t) (node p t) 1 =
      X (rate p) t := upperTail_repeated_defect hp t
  rw [← hx, UniformThreeSpectrum.defect_cycle_all]
  have ha : 0 < node p t := Real.exp_pos _
  have hlt := node_lt_one hp ht
  have hle := DimThree.defect_corner p (show (0 : ℝ) ≤ 1 by norm_num) ha.le ha.le
  have hne : Real.sqrt (DimThree.defect p 1 1 (node p t) *
      DimThree.defect p (node p t) (node p t) (node p t)) ≠
        DimThree.defect p 1 (node p t) (node p t) := by
    intro he
    exact ((DimThree.defect_corner_eq_iff p (by norm_num : (0 : ℝ) ≤ 1) ha.le ha.le).mp he).elim
      hp.ne' hlt.ne'
  exact mul_pos (sq_pos_of_pos (node_gap_pos hp ht))
    ((Real.sqrt_nonneg _).trans_lt (lt_of_le_of_ne hle hne))

private theorem coordinate {p : ℕ} (hp : 0 < p) (s t : ℝ) :
    logCoordinate p (node p s) (node p t) = s-t := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  rw [logCoordinate, node, node, ← Real.exp_sub, Real.log_exp]
  field_simp
  ring

private theorem lower_weight {p : ℕ} (hp : 0 < p) (u d : ℝ) :
    DimThree.defect p (node p (d+u)) (node p d) (node p d) =
      Real.exp (-(3*d))*DimThree.defect p (node p u) 1 1 := by
  have hd := upperTail_lower_weight hp u d
  have h0 : DimThree.defect p (node p u) 1 1 =
      ((p+2).choose 2 : ℝ)*Real.exp (-u)*compositionMoment p 0 (-u) := by
    simpa [node] using upperTail_lower_weight hp u 0
  change DimThree.defect p (node p (d+u)) (node p d) (node p d) = _ at hd
  rw [hd, h0, show -(3*d+u) = -(3*d) + -u by ring, Real.exp_add]
  ring

private theorem cross_eq {p : ℕ} (hp : 0 < p) {u : ℝ} (hu : 0 < u) (d : ℝ) :
    upperTailCrossCorrection (rate p) u d = upperTailRepeatCorrection (rate p) d -
      upperTailGap (rate p) d*Real.exp (-((3+rate p)*d))*R (rate p) u /
        upperTailGap (rate p) u := by
  have hg := (gap_pos hp hu).ne'
  have hd := gap_factor p d
  rw [node_cube] at hd
  have he : Real.exp (-(rate p*d)) = 1 - rate p*upperTailGap (rate p) d := by linarith
  unfold upperTailCrossCorrection upperTailRepeatCorrection R
  rw [he]
  field_simp
  ring

/-- The Taylor expression differs from the actual logarithmic kernel by
the exponential scaling alone, throughout the open ordered chamber. -/
theorem logKernel_eq_exp_mul_G {p : ℕ} (hp : 0 < p) {u d : ℝ}
    (hu : 0 < u) (hd : 0 < d) :
    logKernel p u (d+u) = Real.exp (-d/2) * G (3/(p : ℝ)) u d := by
  let h := rate p
  let v := d+u
  let a := node p v
  let x := node p d
  let b := node p u
  let α := 1-a^3
  let β := 1-x^3
  let γ := 1-b^3
  let Lo := DimThree.defect p a x x
  let Hi := DimThree.defect p a 1 1
  let Num := DimThree.defect p a x 1 -
    Real.sqrt (DimThree.defect p a a 1 * DimThree.defect p x x 1)
  have hv : 0 < v := by dsimp [v]; positivity
  have ha : 0 < a := Real.exp_pos _
  have hx : x < 1 := node_lt_one hp hd
  have hax : a < x := by
    have hpR : (0 : ℝ) < p := by exact_mod_cast hp
    apply Real.exp_lt_exp.mpr
    exact (div_lt_div_iff_of_pos_right hpR).mpr (by dsimp [v]; linarith)
  have hα : 0 < α := node_gap_pos hp hv
  have hβ : 0 < β := node_gap_pos hp hd
  have hγ : 0 < γ := node_gap_pos hp hu
  have hWu : 0 < W h u := W_pos hp hu
  have hWv : 0 < W h v := W_pos hp hv
  have hXv : 0 < X h v := X_pos hp hv
  have hA : α^2 * DimThree.defect p a a 1 = X h v := upperTail_repeated_defect hp v
  have hB : β^2 * DimThree.defect p x x 1 = X h d := upperTail_repeated_defect hp d
  have hroot : α*β * Real.sqrt (DimThree.defect p a a 1 * DimThree.defect p x x 1) =
      Real.sqrt (X h v)*Real.sqrt (X h d) := by
    rw [← Real.sqrt_sq (mul_pos hα hβ).le, ← Real.sqrt_mul (sq_nonneg _)]
    rw [show ((α*β)^2 : ℝ)* (DimThree.defect p a a 1 * DimThree.defect p x x 1) =
      (α^2 * DimThree.defect p a a 1)*(β^2 * DimThree.defect p x x 1) by ring,
      hA, hB, Real.sqrt_mul hXv.le]
  have hm : α*β * DimThree.defect p a x 1 = 1 - upperTailCrossCorrection h u d -
      c h*upperTailGap h v*upperTailGap h d*Real.exp (-(v+d)) := by
    have he : v+d = u+2*d := by dsimp [v]; ring
    rw [he]
    exact upperTail_distinct_defect hp hu
  have hnum : Num =
      (1 - upperTailCrossCorrection h u d -
        c h*upperTailGap h v*upperTailGap h d*Real.exp (-(v+d)) -
        Real.sqrt (X h v)*Real.sqrt (X h d))/(α*β) := by
    apply (eq_div_iff (mul_pos hα hβ).ne').mpr
    dsimp only [Num]
    rw [mul_comm, mul_sub, hm, hroot]
  have hLo : Lo = Real.exp (-(3*d)) * (W h u / γ^2) := by
    rw [show Lo = _ from lower_weight hp u d]
    congr 1
    exact (eq_div_iff (sq_pos_of_pos hγ).ne').mpr
      (by rw [mul_comm]; exact W_eq_defect hp u)
  have hHi : Hi = W h v / α^2 := (eq_div_iff (sq_pos_of_pos hα).ne').mpr
    (by rw [mul_comm]; exact W_eq_defect hp v)
  have hden : Real.sqrt (Lo*Hi) =
      Real.exp (-(3*d)/2)*Real.sqrt (W h u)*Real.sqrt (W h v)/(γ*α) := by
    rw [hLo, hHi]
    rw [show Real.exp (-(3*d)) * (W h u / γ^2) * (W h v / α^2) =
      (Real.exp (-(3*d)/2)^2*(W h u*W h v))/(γ*α)^2 by
        rw [pow_two (Real.exp _), ← Real.exp_add, show -(3*d)/2 + -(3*d)/2 = -(3*d) by ring]
        field_simp [hγ.ne', hα.ne']]
    rw [Real.sqrt_div (by positivity), Real.sqrt_mul (sq_nonneg _), Real.sqrt_mul hWu.le,
      Real.sqrt_sq (Real.exp_pos _).le, Real.sqrt_sq (mul_pos hγ hα).le]
    ring
  have hCu : logCoordinate p a x = u := by
    rw [show a = node p (d+u) from rfl, show x = node p d from rfl, coordinate hp]
    ring
  have hCv : logCoordinate p a 1 = v := by
    rw [show (1 : ℝ) = node p 0 by simp [node]]
    exact (coordinate hp v 0).trans (sub_zero _)
  have hk := upperKernel_div_weights_eq_logKernel hp ha hax (hax.trans hx)
  rw [min_eq_left hx.le, max_eq_right hx.le, hCu, hCv] at hk
  have hk' : Num/Real.sqrt (Lo*Hi) = logKernel p u v := by
    simpa only [ExtremeWalk.upperKernel, min_eq_left hx.le, max_eq_right hx.le, Num, Lo, Hi] using hk
  have hcross : upperTailCrossCorrection h u d = upperTailRepeatCorrection h d -
      upperTailGap h d*Real.exp (-((3+h)*d))*R h u / upperTailGap h u := cross_eq hp hu d
  have hscale : Real.exp (-d/2)*Real.exp (2*d) = (Real.exp (-(3*d)/2))⁻¹ := by
    rw [← Real.exp_add, ← Real.exp_neg]
    congr 1
    ring
  change logKernel p u v = Real.exp (-d/2) * G h u d
  rw [← hk', hnum, hden, hcross]
  unfold G
  dsimp only
  rw [← mul_div_assoc, ← mul_assoc, hscale,
    show γ = h*upperTailGap h u from gap_factor p u,
    show β = h*upperTailGap h d from gap_factor p d]
  have hh : h ≠ 0 := (rate_pos hp).ne'
  have hgu : upperTailGap h u ≠ 0 := (gap_pos hp hu).ne'
  have hgd : upperTailGap h d ≠ 0 := (gap_pos hp hd).ne'
  dsimp only [v]
  have hS : Real.sqrt (W h (d+u)) ≠ 0 := (Real.sqrt_pos.mpr hWv).ne'
  field_simp [hh, hgu, hgd, hα.ne', (Real.exp_pos (-(3*d)/2)).ne',
    (Real.sqrt_pos.mpr hWu).ne', hS]
  ring

/-- The repeated-root part of the short-gap comparison. -/
noncomputable def shortGapJ (h t : ℝ) : ℝ :=
  Real.exp (3*t/2) * Real.sqrt (X h t) / upperTailGap h t

private theorem X_eq_marginal {p : ℕ} (hp : 0 < p) (t : ℝ) :
    X (rate p) t = c (rate p) * (upperTailGap (rate p) t) ^ 2 *
      Real.exp (-(2*t)) * compositionMoment p 0 t := by
  let h := rate p
  have hm : DimThree.defect p (node p t) (node p t) 1 =
      ((p+2).choose 2 : ℝ) * Real.exp (-(2*t)) * compositionMoment p 0 t := by
    rw [UniformThreeSpectrum.defect_cycle_all]
    simpa only [node, add_neg_cancel, neg_zero, zero_div, Real.exp_zero, neg_neg,
      show -(3*t + -t) = -(2*t) by ring] using upperTail_lower_weight hp (-t) t
  have he : (1-node p t^3)^2 * DimThree.defect p (node p t) (node p t) 1 = X h t :=
    upperTail_repeated_defect hp t
  rw [gap_factor, hm] at he
  calc
    _ = (((p+2).choose 2 : ℝ)*h^2) * (upperTailGap h t)^2 *
        Real.exp (-(2*t)) * compositionMoment p 0 t := by rw [← he]; ring
    _ = _ := by rw [(cast_scale hp).2]

/-- The squared scalar correction is the positive marginal composition
defect times its exponential scale. -/
theorem shortGapJ_sq {p : ℕ} (hp : 0 < p) {t : ℝ} (ht : 0 < t) :
    shortGapJ (3/(p : ℝ)) t ^ 2 =
      c (3/(p : ℝ)) * Real.exp t * compositionMoment p 0 t := by
  let h := rate p
  have ha : upperTailGap h t ≠ 0 := (gap_pos hp ht).ne'
  change shortGapJ h t ^ 2 = c h * Real.exp t * compositionMoment p 0 t
  have hx : X h t = c h * (upperTailGap h t) ^ 2 *
      Real.exp (-(2 * t)) * compositionMoment p 0 t := X_eq_marginal hp t
  unfold shortGapJ
  rw [div_pow, mul_pow, Real.sq_sqrt (X_pos hp ht).le, ← Real.exp_nat_mul, hx]
  rw [show (2 : ℕ) * (3*t/2) = 3*t by push_cast; ring]
  calc
    _ = c h *
        (Real.exp (3*t)*Real.exp (-(2*t))) * compositionMoment p 0 t := by
      field_simp [ha] <;> ring
    _ = _ := by rw [← Real.exp_add, show 3*t + -(2*t) = t by ring]

private theorem compositionMoment_eq_integralMarginal {p : ℕ} (hp : 0 < p)
    {t : ℝ} (ht : t ≠ 0) :
    compositionMoment p 0 t = t ^ 2 * SmallCorner.integralMarginalDerivative p 1 0 t := by
  have H := SmallCorner.iteratedDeriv_G_eq_integral hp (by norm_num : (1 : ℝ) ≠ 0) ht 0
  simp only [iteratedDeriv_zero, SmallCorner.G, one_mul] at H
  rw [← H]
  exact (mul_div_cancel₀ _ (pow_ne_zero 2 ht)).symm

/-- At a physical degree, the repeated defect and the regularized radical
use the same centered marginal moment. -/
theorem upperCollision_eq_marginal {p : ℕ} (hp : 0 < p) (u : ℝ) {d : ℝ} (hd : 0 < d) :
    let h := 3 / (p : ℝ)
    let v := d + u
    let a := upperTailGap h
    let V := SmallCorner.integralMarginalDerivative p 1 0
    GAtUpperCollision h u d =
      (a u * (c h * a d * (1 + d ^ 2 * V d) -
        Real.exp d * d * Real.sqrt (c h * V d) * Real.sqrt (X h v) -
        c h * a v * Real.exp (-u)) + Real.exp (-((1 + h) * d)) * R h u) /
        (Real.sqrt (W h u) * Real.sqrt (W h v)) := by
  let h := rate p
  let v := d + u
  let a := upperTailGap h
  let V := SmallCorner.integralMarginalDerivative p 1 0
  have hgap : a d ≠ 0 := (gap_pos hp hd).ne'
  have hc : 0 < c h := by have := rate_pos hp; unfold c; positivity
  have hV : 0 ≤ V d := by
    have hm := compositionMoment_marginal_pos hp hd.ne'
    rw [compositionMoment_eq_integralMarginal hp hd.ne'] at hm
    exact (pos_of_mul_pos_right hm (sq_nonneg d)).le
  have hj : Real.exp (d / 2) * shortGapJ h d = Real.exp d * d * Real.sqrt (c h * V d) := by
    have hJ : 0 ≤ shortGapJ h d := by
      unfold shortGapJ
      exact div_nonneg (mul_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _)) (gap_pos hp hd).le
    have hleft := mul_nonneg (Real.exp_pos (d / 2)).le hJ
    have hright : 0 ≤ Real.exp d * d * Real.sqrt (c h * V d) := by positivity
    have hJsq : shortGapJ h d ^ 2 = c h * Real.exp d * compositionMoment p 0 d :=
      shortGapJ_sq hp hd
    have hs : (Real.exp (d / 2) * shortGapJ h d) ^ 2 =
        (Real.exp d * d * Real.sqrt (c h * V d)) ^ 2 := by
      simp only [mul_pow, hJsq, compositionMoment_eq_integralMarginal hp hd.ne',
        Real.sq_sqrt (mul_nonneg hc.le hV), ← Real.exp_nat_mul]
      rw [show (2 : ℕ) * (d / 2) = d by push_cast; ring]
      rw [show (2 : ℕ) * d = d + d by push_cast; ring, Real.exp_add]
      ring
    simpa only [abs_of_nonneg hleft, abs_of_nonneg hright] using
      (sq_eq_sq_iff_abs_eq_abs _ _).mp hs
  have hrepeat : 1 - upperTailRepeatCorrection h d =
      c h * (a d) ^ 2 * Real.exp (-(2 * d)) * (1 + d ^ 2 * V d) := by
    have hX := X_eq_marginal hp d
    rw [compositionMoment_eq_integralMarginal hp hd.ne'] at hX
    change 1 - upperTailLambda h d = _ at hX
    unfold upperTailLambda at hX
    unfold upperTailRepeatCorrection
    dsimp only [c, a, V] at *
    nlinarith only [hX]
  have h₀ : Real.exp (2 * d) * Real.exp (-(2 * d)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have h₁ : Real.exp (2 * d) * Real.sqrt (X h d) =
      Real.exp (d / 2) * shortGapJ h d * a d := by
    unfold shortGapJ
    calc
      _ = (Real.exp (d / 2) * Real.exp (3 * d / 2)) * Real.sqrt (X h d) := by
        rw [← Real.exp_add, show d / 2 + 3 * d / 2 = 2 * d by ring]
      _ = _ := by
        change _ = Real.exp (d / 2) * (Real.exp (3 * d / 2) * Real.sqrt (X h d) / a d) * a d
        field_simp [hgap]
  have h₂ : Real.exp (2 * d) * Real.exp (-(v + d)) = Real.exp (-u) := by
    rw [← Real.exp_add, show 2 * d + -(v + d) = -u by dsimp only [v]; ring]
  have h₃ : Real.exp (2 * d) * Real.exp (-((3 + h) * d)) = Real.exp (-((1 + h) * d)) := by
    rw [← Real.exp_add, show 2 * d + -((3 + h) * d) = -((1 + h) * d) by ring]
  change GAtUpperCollision h u d = _
  rw [← G_eq_GAtUpperCollision (u := u) (show 0 < h from rate_pos hp) hd]
  unfold G
  change Real.exp (2 * d) *
      (a u * (1 - upperTailRepeatCorrection h d - Real.sqrt (X h d) * Real.sqrt (X h v) -
        c h * a v * a d * Real.exp (-(v + d))) +
        a d * Real.exp (-((3 + h) * d)) * R h u) /
      (a d * Real.sqrt (W h u) * Real.sqrt (W h v)) = _
  rw [hrepeat]
  have hnum : Real.exp (2 * d) *
      (a u * (c h * (a d) ^ 2 * Real.exp (-(2 * d)) * (1 + d ^ 2 * V d) -
        Real.sqrt (X h d) * Real.sqrt (X h v) - c h * a v * a d * Real.exp (-(v + d))) +
        a d * Real.exp (-((3 + h) * d)) * R h u) =
      a d * (a u * (c h * a d * (1 + d ^ 2 * V d) -
        Real.exp (d / 2) * shortGapJ h d * Real.sqrt (X h v) -
        c h * a v * Real.exp (-u)) + Real.exp (-((1 + h) * d)) * R h u) := by
    calc
      _ = a u * (c h * (a d) ^ 2 * (Real.exp (2 * d) * Real.exp (-(2 * d))) *
          (1 + d ^ 2 * V d) - (Real.exp (2 * d) * Real.sqrt (X h d)) * Real.sqrt (X h v) -
          c h * a v * a d * (Real.exp (2 * d) * Real.exp (-(v + d)))) +
          a d * (Real.exp (2 * d) * Real.exp (-((3 + h) * d))) * R h u := by ring
      _ = _ := by rw [h₀, h₁, h₂, h₃]; ring
  rw [hnum, mul_assoc (a d) (Real.sqrt (W h u)) (Real.sqrt (W h v)),
    mul_div_mul_left _ _ hgap, hj]
  rfl

/-- The scalar function whose curvature controls the short-gap sign. -/
noncomputable def shortGapF (h t : ℝ) : ℝ :=
  Real.exp (3*t/2) * (1-Real.exp (-((3+h)*t))) / upperTailGap h t -
    Real.exp (-((3/2+h)*t))/4 - shortGapJ h t

private theorem shortGapF_contDiffAt {p : ℕ} (hp : 0 < p) {t : ℝ} (ht : 0 < t) :
    ContDiffAt ℝ 2 (shortGapF (rate p)) t := by
  let h := rate p
  have hX : ContDiffAt ℝ 2 (X h) t := by
    unfold X upperTailLambda upperTailGap
    fun_prop
  have hJ : ContDiffAt ℝ 2 (shortGapJ h) t := by
    unfold shortGapJ
    apply ContDiffAt.div _ (by unfold upperTailGap; fun_prop) (gap_pos hp ht).ne'
    exact (by fun_prop : ContDiffAt ℝ 2 (fun x : ℝ ↦ Real.exp (3*x/2)) t).mul
      (hX.sqrt (X_pos hp ht).ne')
  unfold shortGapF
  exact (ContDiffAt.sub (ContDiffAt.div (by fun_prop)
    (by unfold upperTailGap; fun_prop) (gap_pos hp ht).ne') (by fun_prop)).sub hJ

/-- Beyond gap two the geometric formula improves the bound on the marginal slope. -/
theorem shortGapJ_deriv_le_of_two_le {p : ℕ} (hp : 11 ≤ p) {t : ℝ} (ht : 2 ≤ t) :
    let h := 3 / (p : ℝ)
    deriv (shortGapJ h) t ≤ (11 / 5) * Real.exp (3 * t / 2) / upperTailGap h t := by
  let h := rate p
  let a := upperTailGap h
  let z : ℝ → ℝ := fun x ↦ Real.sqrt (X h x)
  let E : ℝ → ℝ := fun x ↦ Real.exp (3*x/2)
  have hp₀ : 0 < p := by omega
  have hpR : (11 : ℝ) ≤ p := by exact_mod_cast hp
  have hh := rate_pos hp₀
  have hhmax : h ≤ 3/11 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hpR
  have ht₀ : 0 < t := by linarith
  have ha : 0 < a t := gap_pos hp₀ ht₀
  have ha' : HasDerivAt a (Real.exp (-(h*t))) t := hasDerivAt_upperTailGap (t := t) hh
  have hzPos := X_pos hp₀ ht₀
  have hzDiff : DifferentiableAt ℝ z t := by
    unfold z
    have hX : DifferentiableAt ℝ (X h) t := by unfold X upperTailLambda upperTailGap; fun_prop
    exact (hX.hasDerivAt.sqrt hzPos.ne').differentiableAt
  have hE : HasDerivAt E (E t * (3 / 2)) t := by
    have ht := (((hasDerivAt_id' t).const_mul 3).div_const 2).exp
    convert ht using 1 <;> simp [E, mul_comm]
  have hJ := (hE.mul hzDiff.hasDerivAt).div ha' ha.ne'
  change HasDerivAt (fun x ↦ E x * z x / a x) _ t at hJ
  change deriv (fun x ↦ E x * z x / a x) t ≤ (11 / 5) * E t / a t
  rw [hJ.deriv, Pi.mul_apply]
  have hzB := middleGap_marginal_bounds hh hhmax ht
  change 0 ≤ z t ∧ z t ≤ 1 ∧ 0 ≤ deriv z t ∧ deriv z t ≤ 7 / 10 at hzB
  have hz' : (3/2) * z t + deriv z t - (Real.exp (-(h*t)) / a t) * z t ≤ 11/5 := by
    linarith only [hzB.2.1, hzB.2.2.2,
      mul_nonneg (div_nonneg (Real.exp_pos (-(h*t))).le ha.le) hzB.1]
  calc
    _ = E t * ((3/2) * z t + deriv z t - (Real.exp (-(h*t)) / a t) * z t) / a t := by
      field_simp [ha.ne']
    _ ≤ E t * (11/5) / a t :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hz' (Real.exp_pos _).le) ha.le
    _ = _ := by ring

/-- Regroup the normalized kernel so that all but one mixed-derivative
correction have a favorable sign on the short-gap region. -/
theorem logKernel_eq_shortGap {p : ℕ} (hp : 0 < p) {u d : ℝ}
    (hu : 0 < u) (hd : 0 < d) :
    let h := 3/(p : ℝ)
    let v := d+u
    let a := upperTailGap h
    logKernel p u v =
      (a u / Real.sqrt (W h u)) * (1 / Real.sqrt (W h v)) *
        (shortGapF h d + (R h u/a u-(3+h-1/4))*Real.exp (-((3/2+h)*d)) +
          (1-Real.sqrt (X h v))*shortGapJ h d - c h*a v*Real.exp (-((u+v)/2))) := by
  let h := rate p
  have haU : upperTailGap h u ≠ 0 := (gap_pos hp hu).ne'
  have haD : upperTailGap h d ≠ 0 := (gap_pos hp hd).ne'
  have hWu : Real.sqrt (W h u) ≠ 0 := (Real.sqrt_pos.mpr (W_pos hp hu)).ne'
  have hWv : Real.sqrt (W h (d+u)) ≠ 0 :=
    (Real.sqrt_pos.mpr (W_pos hp (add_pos hd hu))).ne'
  have hscale : Real.exp (-d/2)*Real.exp (2*d) = Real.exp (3*d/2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hgapExp : Real.exp (-((3/2+h)*d)) =
      Real.exp (3*d/2)*Real.exp (-((3+h)*d)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hcenterExp : Real.exp (-((u+(d+u))/2)) =
      Real.exp (3*d/2)*Real.exp (-((d+u)+d)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  dsimp only
  rw [logKernel_eq_exp_mul_G hp hu hd]
  change Real.exp (-d/2) * G h u d = _
  unfold G shortGapF shortGapJ upperTailRepeatCorrection
  dsimp only
  change Real.exp (-d/2) * _ =
    (upperTailGap h u / Real.sqrt (W h u)) * (1 / Real.sqrt (W h (d+u))) *
      ((Real.exp (3*d/2)*(1-Real.exp (-((3+h)*d)))/upperTailGap h d -
        Real.exp (-((3/2+h)*d))/4 - Real.exp (3*d/2)*Real.sqrt (X h d)/upperTailGap h d) +
        (R h u/upperTailGap h u-(3+h-1/4))*Real.exp (-((3/2+h)*d)) +
        (1-Real.sqrt (X h (d+u)))*(Real.exp (3*d/2)*Real.sqrt (X h d)/upperTailGap h d) -
        c h*upperTailGap h (d+u)*Real.exp (-((u+(d+u))/2)))
  rw [← mul_div_assoc, ← mul_assoc, hscale, hgapExp, hcenterExp]
  field_simp [haU, haD, hWu, hWv] <;> ring

private theorem G_contDiffAt {p : ℕ} (hp : 0 < p) {u d : ℝ} (hu : 0 < u) (hd : 0 < d) :
    ContDiffAt ℝ 2 (fun z : ℝ × ℝ ↦ G (rate p) z.1 z.2) (u,d) := by
  let h := rate p
  have ha : upperTailGap h d ≠ 0 := (gap_pos hp hd).ne'
  have hv : 0 < d+u := add_pos hd hu
  have hx₁ : X h d ≠ 0 := (X_pos hp hd).ne'
  have hx₂ : X h (d+u) ≠ 0 := (X_pos hp hv).ne'
  have hw₁ : W h u ≠ 0 := (W_pos hp hu).ne'
  have hw₂ : W h (d+u) ≠ 0 := (W_pos hp hv).ne'
  have hden : upperTailGap h d*Real.sqrt (W h u)*Real.sqrt (W h (d+u)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero ha (Real.sqrt_pos.mpr (W_pos hp hu)).ne')
      (Real.sqrt_pos.mpr (W_pos hp hv)).ne'
  unfold G
  dsimp only
  apply ContDiffAt.div
  · have hx₁' : ContDiffAt ℝ 2 (fun z : ℝ × ℝ ↦ Real.sqrt (X h z.2)) (u,d) :=
      (show ContDiffAt ℝ 2 (fun z : ℝ × ℝ ↦ X h z.2) (u,d) by
        unfold X upperTailLambda upperTailGap
        fun_prop).sqrt hx₁
    have hx₂' : ContDiffAt ℝ 2 (fun z : ℝ × ℝ ↦ Real.sqrt (X h (z.2+z.1))) (u,d) :=
      (show ContDiffAt ℝ 2 (fun z : ℝ × ℝ ↦ X h (z.2+z.1)) (u,d) by
        unfold X upperTailLambda upperTailGap
        fun_prop).sqrt hx₂
    unfold upperTailRepeatCorrection R upperTailGap
    fun_prop
  · have hw₁' : ContDiffAt ℝ 2 (fun z : ℝ × ℝ ↦ Real.sqrt (W h z.1)) (u,d) :=
      (show ContDiffAt ℝ 2 (fun z : ℝ × ℝ ↦ W h z.1) (u,d) by
        unfold W R upperTailGap
        fun_prop).sqrt hw₁
    have hw₂' : ContDiffAt ℝ 2 (fun z : ℝ × ℝ ↦ Real.sqrt (W h (z.2+z.1))) (u,d) :=
      (show ContDiffAt ℝ 2 (fun z : ℝ × ℝ ↦ W h (z.2+z.1)) (u,d) by
        unfold W R upperTailGap
        fun_prop).sqrt hw₂
    unfold upperTailGap
    fun_prop
  · exact hden

private noncomputable def scaleJet (u v : ℝ) : MixedJet ℝ :=
  let e := Real.exp (-(v-u)/2)
  ⟨e, e/2, -e/2, -e/4⟩

private theorem scaleJet_isAt (u v : ℝ) : MixedJet.IsAt scaleJet u v := by
  have hx (y : ℝ) : HasDerivAt (fun x : ℝ ↦ Real.exp (-(y-x)/2))
      (Real.exp (-(y-u)/2)/2) u := by
    have h := (((hasDerivAt_id' u).const_sub y).neg.div_const 2).exp
    change HasDerivAt (fun x : ℝ ↦ Real.exp (-(y-x)/2))
      (Real.exp (-(y-u)/2)*(-(-1 : ℝ)/2)) u at h
    convert h using 1
    ring
  have hy : HasDerivAt (fun y : ℝ ↦ Real.exp (-(y-u)/2))
      (-Real.exp (-(v-u)/2)/2) v := by
    have h := (((hasDerivAt_id' v).sub_const u).neg.div_const 2).exp
    change HasDerivAt (fun y : ℝ ↦ Real.exp (-(y-u)/2))
      (Real.exp (-(v-u)/2)*(-(1 : ℝ)/2)) v at h
    convert h using 1
    ring
  refine ⟨Eventually.of_forall hx, hy, ?_⟩
  change HasDerivAt (fun y : ℝ ↦ Real.exp (-(y-u)/2)/2) (-Real.exp (-(v-u)/2)/4) v
  convert hy.div_const 2 using 1
  ring

/-- The differential operator applied to the centered Taylor coefficients,
in independent lower-coordinate and gap variables. -/
noncomputable def scaledGapDerivative (F : ℝ → ℝ → ℝ) (u d : ℝ) : ℝ :=
  deriv (fun x ↦ deriv (F x) d) u - deriv (deriv (F u)) d -
    deriv (fun x ↦ F x d) u / 2 + deriv (F u) d - F u d / 4

noncomputable def scaledMixed (h u d : ℝ) : ℝ := scaledGapDerivative (G h) u d

theorem scaledMixed_eq_upperCollision {h u d : ℝ} (hh : 0 < h) (hd : 0 < d) :
    scaledMixed h u d = scaledGapDerivative (GAtUpperCollision h) u d := by
  have he (x : ℝ) : G h x =ᶠ[𝓝 d] GAtUpperCollision h x := by
    filter_upwards [eventually_gt_nhds hd] with y hy
    exact G_eq_GAtUpperCollision hh hy
  have hg : (fun x ↦ G h x d) = (fun x ↦ GAtUpperCollision h x d) :=
    funext fun _ ↦ G_eq_GAtUpperCollision hh hd
  have hgd : (fun x ↦ deriv (G h x) d) = (fun x ↦ deriv (GAtUpperCollision h x) d) :=
    funext fun x ↦ (he x).deriv_eq
  unfold scaledMixed scaledGapDerivative
  rw [hgd, (he u).deriv.deriv_eq, hg, (he u).deriv_eq, G_eq_GAtUpperCollision hh hd]

/-- The replay operator is the mixed partial in the original coordinates,
multiplied by the strictly positive exponential scale. -/
theorem exp_mul_logKernel_mixed_eq_scaledMixed {p : ℕ} (hp : 0 < p) {u v : ℝ}
    (hu : 0 < u) (huv : u < v) :
    Real.exp ((v-u)/2) * deriv (fun y ↦ deriv (fun x ↦ logKernel p x y) u) v =
      scaledMixed (3/(p : ℝ)) u (v-u) := by
  let h := rate p
  let d := v-u
  let J : ℝ → ℝ → MixedJet ℝ := fun x y ↦ (scaleJet x y).mul (upperGapJet (G h) x y)
  have hJ : MixedJet.IsAt J u v := (scaleJet_isAt u v).mul
    (upperGapJet_isAt (G_contDiffAt hp hu (sub_pos.mpr huv)))
  have hLoc : (fun y ↦ deriv (fun x ↦ logKernel p x y) u) =ᶠ[𝓝 v] fun y ↦ (J u y).du := by
    filter_upwards [eventually_gt_nhds huv, hJ.1] with y hy hJy
    have hEq : (fun x ↦ logKernel p x y) =ᶠ[𝓝 u] fun x ↦ (J x y).value := by
      filter_upwards [eventually_gt_nhds hu, eventually_lt_nhds hy] with x hx hxy
      have hk := logKernel_eq_exp_mul_G hp hx (sub_pos.mpr hxy)
      rwa [sub_add_cancel y x] at hk
    exact hEq.deriv_eq.trans hJy.deriv
  rw [hLoc.deriv_eq, hJ.2.2.deriv]
  have hcalc : (J u v).duv = Real.exp (-d/2) * scaledMixed h u d := by
    unfold J MixedJet.mul scaleJet upperGapJet scaledMixed scaledGapDerivative
    dsimp only [d]
    ring
  change Real.exp (d/2) * (J u v).duv = scaledMixed h u d
  rw [hcalc, ← mul_assoc, ← Real.exp_add, show d/2 + -d/2 = 0 by ring, Real.exp_zero, one_mul]

#print axioms logKernel_eq_exp_mul_G
#print axioms exp_mul_logKernel_mixed_eq_scaledMixed
#print axioms G_eq_GAtUpperCollision
#print axioms scaledMixed_eq_upperCollision
#print axioms logKernel_eq_shortGap
#print axioms shortGapJ_sq

private theorem shortGapQ_eq (h x : ℝ) (ha : upperTailGap h x ≠ 0) :
    R h x / upperTailGap h x - (3+h-1/4) = shortGapQuotient h x := by
  unfold R shortGapQuotient
  field_simp [ha] <;> ring

/-- Reduce the short-gap sign for the actual matrix kernel to curvature of
the scalar gap profile and the estimates for the marginal correction. -/
theorem logKernel_gap_mixed_of_profile_margin {p : ℕ} (hp : 11 ≤ p) {u v ε : ℝ}
    (hu : 4 ≤ u) (huv : u < v) :
    let h := rate p
    let d := v-u
    let a := upperTailGap h
    let P := fun x ↦ a x / Real.sqrt (W h x)
    let V := fun x ↦ 1 / Real.sqrt (W h x)
    let Z := fun x ↦ Real.sqrt (X h x)
    let α := fun x ↦ deriv P x / P x
    let β := fun x ↦ deriv V x / V x
    let m := 3 / 2 + h
    let Q := shortGapQuotient h
    let ξ := c h*a v*Real.exp (-((u+v)/2))
    0 ≤ shortGapF h d →
    ε < deriv (deriv (shortGapF h)) d - (α u - β v) * deriv (shortGapF h) d -
      (β v - m) * Real.exp (-m * d) * (deriv Q u + (α u + m) * Q u) →
    0 ≤ deriv (shortGapJ h) d →
    deriv (shortGapJ h) d / 2 ≤ deriv (deriv (shortGapJ h)) d →
    0 ≤ deriv Z v →
    deriv Z v * deriv (shortGapJ h) d ≤ ξ*(1/2-α u)*(1/2-α v) →
    deriv (fun y ↦ deriv (fun x ↦ logKernel p x y) u) v < -(P u * V v * ε) := by
  let h := rate p
  let d := v-u
  let a := upperTailGap h
  let P : ℝ → ℝ := fun x ↦ a x / Real.sqrt (W h x)
  let V : ℝ → ℝ := fun x ↦ 1 / Real.sqrt (W h x)
  let Z : ℝ → ℝ := fun x ↦ Real.sqrt (X h x)
  let α : ℝ → ℝ := fun x ↦ deriv P x / P x
  let β : ℝ → ℝ := fun x ↦ deriv V x / V x
  let m := 3 / 2 + h
  let Q := shortGapQuotient h
  let E : ℝ → ℝ := fun x ↦ Real.exp (-x/2)
  let C : ℝ → ℝ := fun x ↦ c h*a x*E x
  let ξ := c h*a v*Real.exp (-((u+v)/2))
  change 0 ≤ shortGapF h d →
    ε < deriv (deriv (shortGapF h)) d - (α u - β v) * deriv (shortGapF h) d -
      (β v - m) * Real.exp (-m * d) * (deriv Q u + (α u + m) * Q u) →
    0 ≤ deriv (shortGapJ h) d →
    deriv (shortGapJ h) d / 2 ≤ deriv (deriv (shortGapJ h)) d → 0 ≤ deriv Z v →
    deriv Z v * deriv (shortGapJ h) d ≤ ξ*(1/2-α u)*(1/2-α v) →
    _
  intro hf hmargin hj' hj'' hz' hc
  have hp₀ : 0 < p := by omega
  have hh := rate_pos hp₀
  have hhp : h ≤ 3/11 := by
    have hreal : (11 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hreal
  have hu₀ : 0 < u := by linarith
  have hv : 4 ≤ v := hu.trans huv.le
  have hv₀ := hu₀.trans huv
  have hd : 0 < d := sub_pos.mpr huv
  have hPpos {t : ℝ} (ht : 0 < t) : 0 < P t :=
    div_pos (gap_pos hp₀ ht) (Real.sqrt_pos.mpr (W_pos hp₀ ht))
  have hVpos {t : ℝ} (ht : 0 < t) : 0 < V t :=
    one_div_pos.mpr (Real.sqrt_pos.mpr (W_pos hp₀ ht))
  have hnorm {t : ℝ} (ht : 4 ≤ t) :
      0 ≤ α t ∧ α t < 1/7 ∧ -(1/t) ≤ β t ∧ β t < 0 :=
    shortGapNormalization_bounds hh hhp ht
  have hWdiff (t : ℝ) : DifferentiableAt ℝ (W h) t := by
    unfold W R upperTailGap
    fun_prop
  have hPdiff {t : ℝ} (ht : 0 < t) : DifferentiableAt ℝ P t :=
    (hasDerivAt_upperTailGap hh).differentiableAt.div
      ((hWdiff t).hasDerivAt.sqrt (W_pos hp₀ ht).ne').differentiableAt
      (Real.sqrt_pos.mpr (W_pos hp₀ ht)).ne'
  have hVdiff {t : ℝ} (ht : 0 < t) : DifferentiableAt ℝ V t :=
    (hasDerivAt_const t (1 : ℝ)).differentiableAt.div
      ((hWdiff t).hasDerivAt.sqrt (W_pos hp₀ ht).ne').differentiableAt
      (Real.sqrt_pos.mpr (W_pos hp₀ ht)).ne'
  have hPderiv {t : ℝ} (ht : 0 < t) : HasDerivAt P (α t*P t) t := by
    simpa only [α, div_mul_cancel₀ _ (hPpos ht).ne'] using (hPdiff ht).hasDerivAt
  have hVderiv : HasDerivAt V (β v*V v) v := by
    simpa only [β, div_mul_cancel₀ _ (hVpos hv₀).ne'] using (hVdiff hv₀).hasDerivAt
  have haEq : a =ᶠ[𝓝 v] fun x ↦ P x / V x := by
    filter_upwards [eventually_gt_nhds hv₀] with x hx
    dsimp [P, V]
    rw [div_div_eq_mul_div, div_one, div_mul_cancel₀ _ (Real.sqrt_pos.mpr (W_pos hp₀ hx)).ne']
  have haDeriv : HasDerivAt a ((α v-β v)*a v) v := by
    have H := ((hPderiv hv₀).div hVderiv (hVpos hv₀).ne').congr_of_eventuallyEq haEq
    refine H.congr_deriv ?_
    rw [haEq.eq_of_nhds]
    field_simp [(hVpos hv₀).ne'] <;> ring
  have he (t : ℝ) : HasDerivAt E (-(1/2)*E t) t := by
    have H := ((hasDerivAt_id' t).neg.div_const 2).exp
    convert H using 1 <;> simp [E] <;> ring
  have hC : HasDerivAt C ((α v-β v-1/2)*C v) v := by
    refine ((haDeriv.const_mul (c h)).mul (he v)).congr_deriv ?_
    dsimp only [C]
    ring
  have hX (t : ℝ) : ContDiff ℝ 2 (X h) := by
    unfold X upperTailLambda upperTailGap
    fun_prop
  have hJ : ContDiffAt ℝ 2 (shortGapJ h) d := by
    have hs := (hX d).contDiffAt.sqrt (X_pos hp₀ hd).ne'
    unfold shortGapJ
    apply ContDiffAt.div _ (by unfold upperTailGap; fun_prop) (gap_pos hp₀ hd).ne'
    exact (by fun_prop : ContDiffAt ℝ 2 (fun x : ℝ ↦ Real.exp (3*x/2)) d).mul hs
  have hF := shortGapF_contDiffAt hp₀ hd
  have hQ : DifferentiableAt ℝ (shortGapQuotient h) u := by
    unfold shortGapQuotient
    exact (hasDerivAt_const u (h+1/4)).differentiableAt.sub
      ((by fun_prop : DifferentiableAt ℝ (fun x : ℝ ↦ 1 - Real.exp (-((3+2*h)*x))) u).div
        (hasDerivAt_upperTailGap hh).differentiableAt (gap_pos hp₀ hu₀).ne')
  have hZ : DifferentiableAt ℝ Z v :=
    ((hX v).contDiffAt.sqrt (X_pos hp₀ hv₀).ne').differentiableAt (by norm_num)
  let F (x y : ℝ) := P x*V y*
    (shortGapF h (y-x) + shortGapQuotient h x*Real.exp (-(3/2+h)*(y-x)) +
      (1-Z y)*shortGapJ h (y-x) - E x*C y)
  have hEq {x y : ℝ} (hx : 0 < x) (hxy : x < y) : logKernel p x y = F x y := by
    have H := logKernel_eq_shortGap hp₀ hx (sub_pos.mpr hxy)
    dsimp only at H
    rw [sub_add_cancel] at H
    change _ = P x*V y*(shortGapF h (y-x) +
      (R h x/a x-(3+h-1/4))*Real.exp (-((3/2+h)*(y-x))) +
      (1-Z y)*shortGapJ h (y-x) - c h*a y*Real.exp (-((x+y)/2))) at H
    rw [shortGapQ_eq h x (gap_pos hp₀ hx).ne',
      show -((3/2+h)*(y-x)) = -(3/2+h)*(y-x) by ring] at H
    rw [H]
    have heq : Real.exp (-((x+y)/2)) = E x * E y := by
      unfold E
      rw [← Real.exp_add]
      congr 1
      ring
    unfold F C
    rw [heq]
    ring
  have hLoc : (fun y ↦ deriv (fun x ↦ logKernel p x y) u) =ᶠ[𝓝 v]
      (fun y ↦ deriv (fun x ↦ F x y) u) := by
    filter_upwards [eventually_gt_nhds huv] with y hy
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [eventually_gt_nhds hu₀, eventually_lt_nhds hy] with x hx hxy
    exact hEq hx hxy
  rw [hLoc.deriv_eq]
  change deriv (fun y ↦ deriv (fun x ↦ P x*V y*
    (shortGapF h (y-x) + shortGapQuotient h x*Real.exp (-(3/2+h)*(y-x)) +
      (1-Z y)*shortGapJ h (y-x) - Real.exp (-x/2)*C y)) u) v < _
  rw [shortGap_weighted_mixed_formula (hPderiv hu₀) hVderiv hF hJ hQ hZ hC]
  dsimp only
  have hξ : Real.exp (-u/2)*C v = ξ := by
    unfold C E ξ
    rw [show Real.exp (-u/2)*(c h*a v*Real.exp (-v/2)) =
        c h*a v*(Real.exp (-u/2)*Real.exp (-v/2)) by ring, ← Real.exp_add]
    congr 2
    ring
  rw [hξ, show -(P u * V v * ε) = P u * V v * (-ε) by ring]
  apply mul_lt_mul_of_pos_left _ (mul_pos (hPpos hu₀) (hVpos hv₀))
  have hn₁ := hnorm hu
  have hn₂ := hnorm hv
  have hβ : -1/4 ≤ β v := by
    have H := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4) hv
    linarith only [H, hn₂.2.2.1]
  have hj : 0 ≤ shortGapJ h d :=
    div_nonneg (mul_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _)) (gap_pos hp₀ hd).le
  have hz : 0 ≤ 1-Z v := by
    have H := Real.sqrt_le_sqrt (show X h v ≤ 1 by
      unfold X upperTailLambda
      have ha := (gap_pos hp₀ hv₀).le
      have hsum : 0 ≤ (1 + (3+h)*a v)*Real.exp (-((3+h)*v)) +
          ((3+h)*(3+2*h)/2)*(a v)^2*Real.exp (-(2*v)) := by positivity
      linarith only [hsum])
    rw [Real.sqrt_one] at H
    exact sub_nonneg.mpr H
  exact shortGap_mixed_lt_of_profile_margin hn₁.1 hn₁.2.1.le hn₂.2.2.2.le hβ
    hf hmargin hj hj' hj'' hz hz' hc

/-- Ordinary curvature and slope estimates give the short-gap mixed sign. -/
theorem logKernel_shortGap_mixed_of_scalar_bounds {p : ℕ} (hp : 11 ≤ p) {u v : ℝ}
    (hu : 4 ≤ u) (huv : u < v) :
    let h := rate p
    let d := v-u
    let a := upperTailGap h
    let P := fun x ↦ a x / Real.sqrt (W h x)
    let V := fun x ↦ 1 / Real.sqrt (W h x)
    let Z := fun x ↦ Real.sqrt (X h x)
    let α := fun x ↦ deriv P x / P x
    let ξ := c h*a v*Real.exp (-((u+v)/2))
    0 ≤ shortGapF h d →
    deriv (shortGapF h) d ≤ 0 →
    1/200 < deriv (deriv (shortGapF h)) d →
    0 ≤ deriv (shortGapJ h) d →
    deriv (shortGapJ h) d / 2 ≤ deriv (deriv (shortGapJ h)) d →
    0 ≤ deriv Z v →
    deriv Z v * deriv (shortGapJ h) d ≤ ξ*(1/2-α u)*(1/2-α v) →
    deriv (fun y ↦ deriv (fun x ↦ logKernel p x y) u) v < -(P u*V v/200) := by
  dsimp only
  intro hf hf' hf'' hj' hj'' hz' hc
  have hp₀ : 0 < p := by omega
  have hpR : (11 : ℝ) ≤ p := by exact_mod_cast hp
  have hh := rate_pos hp₀
  have hhmax : rate p ≤ 3 / 11 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hpR
  have hα := (shortGapNormalization_bounds hh hhmax hu).1
  have hβ := (shortGapNormalization_bounds hh hhmax (hu.trans huv.le)).2.2.2.le
  change 0 ≤ deriv (fun s ↦ upperTailGap (rate p) s / Real.sqrt (W (rate p) s)) u /
    (upperTailGap (rate p) u / Real.sqrt (W (rate p) u)) at hα
  change deriv (fun s ↦ 1 / Real.sqrt (W (rate p) s)) v /
    (1 / Real.sqrt (W (rate p) v)) ≤ 0 at hβ
  have hq := shortGapQuotient_nonneg hh hu
  have hq' : 0 ≤ deriv (shortGapQuotient (rate p)) u :=
    shortGapQuotient_deriv_nonneg hp₀ (by linarith)
  have hm : 0 ≤ 3 / 2 + rate p := by linarith
  have hfTerm := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr (hβ.trans hα)) hf'
  have hqTerm := mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hβ.trans hm))
      (Real.exp_pos (-(3 / 2 + rate p) * (v - u))).le)
    (add_nonneg hq' (mul_nonneg (add_nonneg hα hm) hq))
  have hsign := logKernel_gap_mixed_of_profile_margin hp hu huv (ε := 1 / 200)
    hf (by dsimp only; linarith only [hf'', hfTerm, hqTerm]) hj' hj'' hz' hc
  exact hsign.trans_eq (by ring)

#print axioms logKernel_shortGap_mixed_of_scalar_bounds

/-- The three scalar profile inequalities suffice everywhere on the
short-gap strip, including arbitrarily close to the diagonal. -/
theorem logKernel_shortGap_mixed_of_profile {p : ℕ} (hp : 11 ≤ p) {u v : ℝ}
    (hu : 4 ≤ u) (huv : u < v) (hdmax : v-u ≤ 2) :
    let h := rate p
    let F := shortGapF h
    let d := v-u
    0 ≤ F d →
    deriv F d ≤ 0 →
    1/200 < deriv (deriv F) d →
    deriv (fun y ↦ deriv (fun x ↦ logKernel p x y) u) v <
      -(upperTailGap h u / Real.sqrt (W h u) * (1 / Real.sqrt (W h v)) / 200) := by
  dsimp only
  intro hf hf' hf''
  let h := rate p
  let d := v-u
  let Z : ℝ → ℝ := fun x ↦ Real.sqrt (X h x)
  let P : ℝ → ℝ := fun x ↦ upperTailGap h x / Real.sqrt (W h x)
  let α : ℝ → ℝ := fun x ↦ deriv P x / P x
  have hp₀ : 0 < p := by omega
  have hh := rate_pos hp₀
  have hhp : h ≤ 3/11 := by
    have hpR : (11 : ℝ) ≤ p := by exact_mod_cast hp
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hpR
  have hd : 0 < d := sub_pos.mpr huv
  have hv : 4 ≤ v := hu.trans huv.le
  have he : shortGapJ h =ᶠ[𝓝 d] RefinedBMV.PositiveCenter.shortGapJ p := by
    filter_upwards [eventually_gt_nhds hd] with t ht
    rw [shortGapJ_eq_sqrt hp₀ ht]
    have hj : 0 ≤ shortGapJ h t :=
      div_nonneg (mul_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _)) (gap_pos hp₀ ht).le
    have hsq : shortGapJ h t ^ 2 = c h*Real.exp t*compositionMoment p 0 t :=
      shortGapJ_sq hp₀ ht
    change shortGapJ h t = Real.sqrt (c h*Real.exp t*compositionMoment p 0 t)
    rw [← hsq, Real.sqrt_sq hj]
  refine logKernel_shortGap_mixed_of_scalar_bounds hp hu huv hf hf' hf'' ?_ ?_ ?_ ?_
  · rw [he.deriv_eq]
    exact (shortGapJ_deriv_pos hp₀ hd.le).le
  · rw [he.deriv_eq, he.deriv.deriv_eq]
    exact shortGapJ_deriv_half_le_second hp₀ hd.le
  · exact (shortGap_marginal_deriv_bounds hh hhp hv).1
  · change deriv Z v * deriv (shortGapJ h) d ≤ _
    rw [he.deriv_eq]
    have hαu : α u ≤ 1/7 := (shortGapNormalization_bounds hh hhp hu).2.1.le
    have hαv : α v ≤ 1/7 := (shortGapNormalization_bounds hh hhp hv).2.1.le
    have hj := shortGapJ_deriv_le hp hd.le
    have hc := shortGap_correction_lt hh hhp hu hd hdmax hj hαu hαv
    dsimp only [d] at hc
    rw [show u+(v-u) = v by ring, show -(u+v)/2 = -((u+v)/2) by ring] at hc
    exact hc.le

#print axioms logKernel_shortGap_mixed_of_profile

/-- For gaps at least two, the profile margin alone suffices for the mixed sign. -/
theorem logKernel_middleGap_mixed_of_profile_margin {p : ℕ} (hp : 11 ≤ p) {u v : ℝ}
    (hu : 4 ≤ u) (hd : 2 ≤ v - u) :
    let h := rate p
    let d := v - u
    let P := fun t ↦ upperTailGap h t / Real.sqrt (W h t)
    let V := fun t ↦ 1 / Real.sqrt (W h t)
    let α := fun t ↦ deriv P t / P t
    let β := fun t ↦ deriv V t / V t
    let m := 3 / 2 + h
    let Q := shortGapQuotient h
    0 ≤ shortGapF h d →
    0 < deriv (deriv (shortGapF h)) d - (α u - β v) * deriv (shortGapF h) d -
      (β v - m) * Real.exp (-m * d) * (deriv Q u + (α u + m) * Q u) →
    deriv (fun y ↦ deriv (fun x ↦ logKernel p x y) u) v < 0 := by
  dsimp only
  intro hf hmargin
  let h := rate p
  let d := v - u
  let a := upperTailGap h
  let Z : ℝ → ℝ := fun t ↦ Real.sqrt (X h t)
  let P : ℝ → ℝ := fun t ↦ a t / Real.sqrt (W h t)
  let α : ℝ → ℝ := fun t ↦ deriv P t / P t
  have hp₀ : 0 < p := by omega
  have hpR : (11 : ℝ) ≤ p := by exact_mod_cast hp
  have hh := rate_pos hp₀
  have hhmax : h ≤ 3 / 11 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hpR
  have huv : u < v := by linarith
  have hv : 4 ≤ v := hu.trans huv.le
  have hαu : α u ≤ 1 / 7 := (shortGapNormalization_bounds hh hhmax hu).2.1.le
  have hαv : α v ≤ 1 / 7 := (shortGapNormalization_bounds hh hhmax hv).2.1.le
  have he : shortGapJ h =ᶠ[𝓝 d] RefinedBMV.PositiveCenter.shortGapJ p := by
    filter_upwards [eventually_gt_nhds (show 0 < d by dsimp [d]; linarith)] with t ht
    rw [shortGapJ_eq_sqrt hp₀ ht]
    have hj : 0 ≤ shortGapJ h t :=
      div_nonneg (mul_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _)) (gap_pos hp₀ ht).le
    have hsq : shortGapJ h t ^ 2 = c h * Real.exp t * compositionMoment p 0 t :=
      shortGapJ_sq hp₀ ht
    change shortGapJ h t = Real.sqrt (c h * Real.exp t * compositionMoment p 0 t)
    rw [← hsq, Real.sqrt_sq hj]
  have hj' : 0 ≤ deriv (shortGapJ h) d := by
    rw [he.deriv_eq]
    exact (shortGapJ_deriv_pos hp₀ (by dsimp [d]; linarith)).le
  have hj'' : deriv (shortGapJ h) d / 2 ≤ deriv (deriv (shortGapJ h)) d := by
    rw [he.deriv_eq, he.deriv.deriv_eq]
    exact shortGapJ_deriv_half_le_second hp₀ (by dsimp [d]; linarith)
  have hz' : 0 ≤ deriv Z v := (shortGap_marginal_deriv_bounds hh hhmax hv).1
  have hc := middleGap_correction_lt hh hhmax hu hd (shortGapJ_deriv_le_of_two_le hp hd) hαu hαv
  change deriv Z (u+d) * deriv (shortGapJ h) d <
    c h * a (u+d) * Real.exp (-(u+(u+d))/2) * (1/2-α u) * (1/2-α v) at hc
  rw [show u+d = v by dsimp [d]; ring, show -(u+v)/2 = -((u+v)/2) by ring] at hc
  have hsign := logKernel_gap_mixed_of_profile_margin hp hu huv (ε := 0)
    hf hmargin hj' hj'' hz' hc.le
  simpa only [mul_zero, neg_zero] using hsign

/-- Positivity of the short-gap profile follows from the difference of
squares and holds on the full positive gap axis. -/
theorem shortGapF_pos {p : ℕ} (hp : 0 < p) {t : ℝ} (ht : 0 < t) :
    0 < shortGapF (3/(p : ℝ)) t := by
  let h := rate p
  let g : ℝ := 3+h
  let k : ℝ := 3+2*h
  let a := upperTailGap h t
  let r := (1-Real.exp (-(g*t)))/a
  let e := Real.exp (3*t/2)
  let l := e*r
  let j := shortGapJ h t
  have hh : 0 < h := rate_pos hp
  have hg : 0 < g := by dsimp [g]; linarith
  have ha : 0 < a := gap_pos hp ht
  have he : 0 < e := Real.exp_pos _
  have hq : Real.exp (-(g*t)) < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos (mul_pos hg ht))
  have hr : 0 < r := div_pos (sub_pos.mpr hq) ha
  have hl : 0 < l := mul_pos he hr
  have hj : 0 ≤ j :=
    div_nonneg (mul_nonneg he.le (Real.sqrt_nonneg _)) ha.le
  have hmean : expGapMean g t ≤ expGapMean h t := by
    unfold expGapMean
    apply intervalIntegral.integral_mono_on zero_le_one
      (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _)
    intro s hs
    have hhg : h ≤ g := by dsimp [g]; linarith
    exact Real.exp_le_exp.mpr (neg_le_neg
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hhg ht.le) hs.1))
  have hrbound : r ≤ g := by
    apply (div_le_iff₀ ha).2
    have hcomparison := mul_le_mul_of_nonneg_left hmean (mul_nonneg hg.le ht.le)
    have h₁ := expGapMean_eq hg t
    have h₂ := expGapMean_eq hh t
    unfold upperTailGap at h₁
    have heq := (div_eq_iff hg.ne').mp h₁
    dsimp only [a]
    rw [heq, h₂]
    linarith only [hcomparison, show t*expGapMean g t*g = g*t*expGapMean g t by ring,
      show g*(t*expGapMean h t) = g*t*expGapMean h t by ring]
  have he₂ : e^2 = Real.exp (3*t) := by
    unfold e
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hx : 0 ≤ X h t := (X_pos hp ht).le
  have hsq :
      l^2-j^2 = c h*Real.exp t + Real.exp (-(h*t))/a*(g-r) := by
    calc
      _ = c h*(Real.exp (3*t)*Real.exp (-(2*t))) +
          (Real.exp (3*t)*Real.exp (-(g*t)))/a*(g-r) := by
        change (e*r)^2 - (e*Real.sqrt (X h t)/a)^2 = _
        rw [mul_pow e r, div_pow (e*Real.sqrt (X h t)), mul_pow e, Real.sq_sqrt hx, he₂]
        unfold X upperTailLambda
        dsimp only [r, g, a, c] at *
        field_simp [ha.ne'] <;> ring
      _ = _ := by
        rw [← Real.exp_add, show 3*t + -(2*t) = t by ring,
          ← Real.exp_add, show 3*t + -(g*t) = -(h*t) by dsimp [g]; ring]
  have hc : 0 < c h := by unfold c; positivity
  have hbudget : c h*Real.exp t ≤ l^2-j^2 := by
    rw [hsq]
    linarith only [mul_nonneg (div_nonneg (Real.exp_pos (-(h*t))).le ha.le)
      (sub_nonneg.mpr hrbound)]
  have hjl : j ≤ l := by
    have hpos : 0 < c h*Real.exp t := mul_pos hc (Real.exp_pos _)
    by_contra! hcontra
    have hneg := mul_pos (sub_pos.mpr hcontra) (add_pos_of_nonneg_of_pos hj hl)
    nlinarith only [hneg, hbudget, hpos]
  have hlbound : l ≤ g*e := by
    rw [mul_comm g]
    exact mul_le_mul_of_nonneg_left hrbound he.le
  have hbig : c h*Real.exp t ≤ (l-j)*(2*g*e) := calc
    _ ≤ l^2-j^2 := hbudget
    _ = (l-j)*(l+j) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (sub_nonneg.mpr hjl)
  have hmul : (2*g*e)*(k/4*Real.exp (-t/2)) = c h*Real.exp t := by
    have hE : e*Real.exp (-t/2) = Real.exp t := by
      unfold e
      rw [← Real.exp_add, show 3*t/2 + -t/2 = t by ring]
    calc
      _ = c h*(e*Real.exp (-t/2)) := by dsimp [c, g, k]; ring
      _ = _ := by rw [hE]
  have hdiff : k/4*Real.exp (-t/2) ≤ l-j := by
    apply le_of_mul_le_mul_left _ (show 0 < 2*g*e by positivity)
    rw [hmul, mul_comm (2*g*e)]
    exact hbig
  have hm : Real.exp (-((3/2+h)*t)) ≤ Real.exp (-t/2) := by
    apply Real.exp_le_exp.mpr
    nlinarith only [mul_nonneg hh.le ht.le, ht]
  have hk : 1 < k := by dsimp [k]; linarith
  have hsmall : Real.exp (-((3/2+h)*t))/4 < k/4*Real.exp (-t/2) := calc
    _ ≤ Real.exp (-t/2)/4 := by linarith
    _ < _ := by
      have h := mul_lt_mul_of_pos_right hk (Real.exp_pos (-t/2))
      linarith
  unfold shortGapF
  rw [mul_div_assoc]
  change 0 < l - Real.exp (-((3/2+h)*t))/4 - j
  linarith

#print axioms shortGapF_pos

/-- The one-variable profile including the constant part of the geometric correction. -/
noncomputable def middleGapProfile (h t : ℝ) : ℝ :=
  shortGapF h t + Real.exp (-((3 / 2 + h) * t)) / 4

/-- Two gap-dependent estimates suffice for the mixed sign uniformly in the lower coordinate. -/
theorem logKernel_middleGap_mixed_of_recentered {p : ℕ} (hp : 11 ≤ p) {u v : ℝ}
    (hu : 4 ≤ u) (hd : 2 ≤ v - u)
    (hslope : middleGapSlopeBudget (rate p) (v - u) ≤
      -deriv (middleGapProfile (rate p)) (v - u))
    (hcurve : 0 < deriv (deriv (middleGapProfile (rate p))) (v - u)) :
    deriv (fun y ↦ deriv (fun x ↦ logKernel p x y) u) v < 0 := by
  let h := rate p
  let d := v - u
  let m : ℝ := 3 / 2 + h
  let E : ℝ → ℝ := fun t ↦ Real.exp (-(m * t))
  let P : ℝ → ℝ := fun t ↦ upperTailGap h t / Real.sqrt (W h t)
  let V : ℝ → ℝ := fun t ↦ 1 / Real.sqrt (W h t)
  let α : ℝ → ℝ := fun t ↦ deriv P t / P t
  let β : ℝ → ℝ := fun t ↦ deriv V t / V t
  let r := upperTailSlope h u * (1 - Real.exp (-((3 + h) * u)))
  have hp₀ : 0 < p := by omega
  have hh := rate_pos hp₀
  have hpR : (11 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hhmax : h ≤ 3 / 11 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hpR
  have hu₀ : 0 < u := by linarith
  have hd₀ : 0 < d := by dsimp [d]; linarith
  have huv : u < v := sub_pos.mp hd₀
  have hv : 4 ≤ v := hu.trans huv.le
  have hv₀ : 0 < v := hu₀.trans huv
  have hvd : u + d = v := by dsimp [d]; ring
  have huNorm : 0 ≤ α u ∧ α u < 1 / 7 ∧ -(1 / u) ≤ β u ∧ β u < 0 :=
    shortGapNormalization_bounds hh hhmax hu
  have hvNorm : 0 ≤ α v ∧ α v < 1 / 7 ∧ -(1 / v) ≤ β v ∧ β v < 0 :=
    shortGapNormalization_bounds hh hhmax hv
  have hβbound {t : ℝ} (ht : 4 ≤ t) : upperTailSlope h t / 2 ≤ -β t := by
    have ht' : β t ≤ -upperTailSlope h t / 2 := shortGap_upperLogDeriv_le hh hhmax ht
    simpa only [neg_div, neg_neg] using neg_le_neg ht'
  have hlog : α u - β u = upperTailSlope h u := shortGapNormalization_logDiff hh hu₀
  have hq : shortGapQuotient h u = 1 / 4 - r := shortGapQuotient_recenter hh hu₀
  have hqd : -deriv (shortGapQuotient h) u + (α u + m) * r =
      (3 / 2 + β u + upperTailSlope (3 + h) u) * r :=
    shortGapQuotient_recentered_slope hh hu₀ hlog
  have hgeo : (m - β v) * (3 / 2 + β u + upperTailSlope (3 + h) u) * r * E d ≤
      -β v * middleGapSlopeBudget h d := by
    have hbv' : upperTailSlope h (u + d) / 2 ≤ -β v := by simpa only [hvd] using hβbound hv
    have hbvmax : -β v ≤ 1 / (u + d) := by
      rw [hvd]
      simpa only [neg_neg] using neg_le_neg hvNorm.2.2.1
    have hb := middleGap_geometric_absorption hh hhmax hu hd (hβbound hu) hbv' hbvmax
    change (m + -β v) * (3 / 2 - (-β u) + upperTailSlope (3 + h) u) * r * E d ≤ _ at hb
    simpa only [← sub_eq_add_neg, sub_neg_eq_add] using hb
  have hE (t : ℝ) : HasDerivAt E (-m * E t) t := by
    convert (((hasDerivAt_id' t).const_mul m).neg.exp) using 1 <;> simp [E] <;> ring
  have hfirst {t : ℝ} (ht : 0 < t) : deriv (middleGapProfile h) t =
      deriv (shortGapF h) t + (-m * E t) / 4 :=
    (((shortGapF_contDiffAt hp₀ ht).differentiableAt (by norm_num)).hasDerivAt.add
      ((hE t).div_const 4)).deriv
  have hsecond : deriv (deriv (middleGapProfile h)) d =
      deriv (deriv (shortGapF h)) d + m ^ 2 * E d / 4 := by
    have heq : deriv (middleGapProfile h) =ᶠ[𝓝 d]
        fun t ↦ deriv (shortGapF h) t + (-m * E t) / 4 := by
      filter_upwards [eventually_gt_nhds hd₀] with t ht using hfirst ht
    have hFd : DifferentiableAt ℝ (deriv (shortGapF h)) d :=
      ((shortGapF_contDiffAt hp₀ hd₀).derivWithin (m := 1) (by norm_num)).differentiableAt one_ne_zero
    rw [heq.deriv_eq, (hFd.hasDerivAt.fun_add (((hE d).const_mul (-m)).div_const 4)).deriv]
    ring
  have hB : 0 ≤ middleGapSlopeBudget h d := by
    have ha := (gap_pos hp₀ hd₀).le
    have hmd : 0 ≤ 3 / 2 + h + 1 / (4 + d) := by positivity
    unfold middleGapSlopeBudget
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hmd)
      (add_nonneg zero_le_one (div_nonneg ha (by norm_num)))) (Real.exp_pos _).le
  change middleGapSlopeBudget h d ≤ -deriv (middleGapProfile h) d at hslope
  change 0 < deriv (deriv (middleGapProfile h)) d at hcurve
  have hβ : 0 ≤ -β v := neg_nonneg.mpr hvNorm.2.2.2.le
  have hgain := mul_le_mul_of_nonneg_left hslope hβ
  have hα := mul_nonneg huNorm.1 (hB.trans hslope)
  have hαβ : 0 ≤ α u * (-β v) * E d / 4 :=
    div_nonneg (mul_nonneg (mul_nonneg huNorm.1 hβ) (Real.exp_pos _).le) (by norm_num)
  refine logKernel_middleGap_mixed_of_profile_margin hp hu hd (shortGapF_pos hp₀ hd₀).le ?_
  rw [neg_mul]
  change 0 < deriv (deriv (shortGapF h)) d - (α u - β v) * deriv (shortGapF h) d -
    (β v - m) * E d * (deriv (shortGapQuotient h) u + (α u + m) * shortGapQuotient h u)
  have hrecenter : deriv (deriv (shortGapF h)) d - (α u - β v) * deriv (shortGapF h) d -
        (β v - m) * E d * (deriv (shortGapQuotient h) u + (α u + m) * shortGapQuotient h u) =
      deriv (deriv (middleGapProfile h)) d - (α u - β v) * deriv (middleGapProfile h) d +
        α u * (-β v) * E d / 4 -
        (m - β v) * ((3 / 2 + β u + upperTailSlope (3 + h) u) * r) * E d := by
    rw [hfirst hd₀, hsecond, hq, ← hqd]
    ring
  rw [hrecenter]
  nlinarith only [hcurve, hgeo, hgain, hα, hαβ]

#print axioms logKernel_middleGap_mixed_of_recentered

/-- A certificate for the scalar discriminant and endpoint slope implies the
strict mixed sign on the entire unbounded short-gap region. -/
theorem logKernel_shortGap_mixed_of_certificate {p : ℕ} (hp : 11 ≤ p) {u v : ℝ}
    (hu : 4 ≤ u) (huv : u < v) (hdmax : v-u ≤ 2)
    (hD : ∀ t ∈ Set.Icc (0 : ℝ) 2,
      0 < shortGapProfileD (shortGapProfileT p (3/(p : ℝ))) (shortGapProfileU p) t)
    (hH : 0 < shortGapProfileH (shortGapProfileT p (3/(p : ℝ))) (shortGapProfileU p) 2) :
    deriv (fun y ↦ deriv (fun x ↦ logKernel p x y) u) v < 0 := by
  let h := rate p
  let d := v-u
  let J := RefinedBMV.PositiveCenter.shortGapJ p
  have hp₀ : 0 < p := by omega
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp₀
  have hh := rate_pos hp₀
  have hd : 0 < d := sub_pos.mpr huv
  have hcancel : h*(p : ℝ) = 3 := div_mul_cancel₀ 3 hpR.ne'
  have hprofile := shortGapProfile_of_signs hh hcancel (shortGapProfileU_contDiff p)
    (shortGapProfileU_pos hp₀) (J := J) rfl (shortGapJ_deriv_pos hp₀ (by norm_num)) hD hH
  have he : shortGapF h =ᶠ[𝓝 d] fun t ↦ shortGapProfileT p h t - J t := by
    filter_upwards [eventually_gt_nhds hd] with t ht
    unfold shortGapF shortGapProfileT
    rw [show Real.exp (3*t/2)*(1-Real.exp (-((3+h)*t)))/upperTailGap h t =
      h*∑ l ∈ Finset.range (p+1), Real.exp ((h*l-3/2)*t) from shortGap_geometric_eq hp₀ ht]
    have hj : 0 ≤ shortGapJ h t :=
      div_nonneg (mul_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _)) (gap_pos hp₀ ht).le
    have hsq : shortGapJ h t ^ 2 = c h * Real.exp t * compositionMoment p 0 t :=
      shortGapJ_sq hp₀ ht
    have hj_eq : shortGapJ h t = J t := by
      unfold J
      rw [shortGapJ_eq_sqrt hp₀ ht]
      change shortGapJ h t = Real.sqrt (c h * Real.exp t * compositionMoment p 0 t)
      rw [← hsq, Real.sqrt_sq hj]
    rw [hj_eq, show -((3/2+h)*t) = -(3/2+h)*t by ring]
  have hs := hprofile d ⟨hd.le, hdmax⟩
  have hf' : deriv (shortGapF h) d ≤ 0 := he.deriv_eq.trans_lt hs.2 |>.le
  have hf'' : 1/200 < deriv (deriv (shortGapF h)) d :=
    hs.1.trans_eq he.deriv.deriv_eq.symm
  have hm := logKernel_shortGap_mixed_of_profile hp hu huv hdmax
    (shortGapF_pos hp₀ hd).le hf' hf''
  refine hm.trans_le (neg_nonpos.mpr ?_)
  exact div_nonneg (mul_nonneg (div_nonneg (gap_pos hp₀ (by linarith)).le (Real.sqrt_nonneg _))
    (one_div_nonneg.mpr (Real.sqrt_nonneg _))) (by norm_num)

#print axioms logKernel_shortGap_mixed_of_certificate

/-- The mixed derivative is strictly negative throughout the unbounded short-gap strip. -/
theorem logKernel_shortGap_mixed {p : ℕ} (hp : 11 ≤ p) {u v : ℝ}
    (hu : 4 ≤ u) (huv : u < v) (hdmax : v - u ≤ 2) :
    deriv (fun y ↦ deriv (fun x ↦ logKernel p x y) u) v < 0 := by
  obtain ⟨hD, hH⟩ := shortGap_profile_signs hp
  exact logKernel_shortGap_mixed_of_certificate hp hu huv hdmax hD hH

#print axioms logKernel_shortGap_mixed

end RefinedBMV.PositiveCenter.CompactGap
