/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/CompactGapIdentities
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact scaled kernel identities before the short- and middle-gap estimates. -/

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

end RefinedBMV.PositiveCenter.CompactGap
