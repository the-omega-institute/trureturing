/- GID: D5/S3/Quantum/Matrix/HsfQubitCoupledScalar
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/HsfQubitCoupledScalar
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Real.Sqrt]
   utility: none
   digest: Coupled scalar cubic trace bounds for two spectral levels. -/

module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic
public import D5.S3.Quantum.Matrix.HsfQubitCubicCertificate

@[expose] public section

noncomputable section
namespace D5.S3.Quantum.Matrix.HsfQubitCoupledScalar

def mean (a b : ℝ) : ℝ := 2 * (a ^ 2 + a * b + b ^ 2) / (3 * (a + b))
def excess (a b : ℝ) : ℝ := mean a b - Real.sqrt (a * b)
def penalty (a b : ℝ) : ℝ :=
  2 * (a - b) ^ 2 * (a ^ 2 + 3 * a * b + b ^ 2) / (9 * (a + b))

theorem excess_nonneg (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    0 ≤ excess a b := by
  have hs : 0 < a + b := add_pos ha hb
  have hr := Real.sqrt_nonneg (a * b)
  have hr2 := Real.sq_sqrt (mul_pos ha hb).le
  have har : 2 * Real.sqrt (a * b) ≤ a + b :=
    two_mul_le_add_of_sq_le_mul ha.le hb.le hr2.le
  have hp := mul_nonneg (sub_nonneg.mpr har)
    (show 0 ≤ 2 * (a + b) + Real.sqrt (a * b) by positivity)
  have hm : Real.sqrt (a * b) ≤ mean a b := by
    apply (le_div_iff₀ (show 0 < 3 * (a + b) by positivity)).mpr
    nlinarith only [hp, hr2]
  exact sub_nonneg.mpr hm

private theorem small_margin (d e beta theta D S z x : ℝ)
    (hd : 0 < d) (hdmax : d ≤ 1 / 3)
    (he : 0 ≤ e) (hemax : e ≤ (4 / 9) * d ^ 2)
    (hbeta : (22 / 81) * d ^ 2 ≤ beta)
    (hth : 0 ≤ theta) (hthmax : theta ≤ 4)
    (hD : D = (4 - theta) / 3) (hDpos : 0 < D)
    (hS : 0 ≤ S) (hvariance : 4 * d ^ 2 * z ^ 2 ≤ S * D) :
    2 * theta * e * z * x + (theta * e ^ 2 - beta) * x ^ 2 ≤ S := by
  have hd2 : d ^ 2 ≤ 1 / 9 := by nlinarith
  have he2 : e ^ 2 ≤ (16 / 81) * d ^ 4 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hemax)
      (add_nonneg (show 0 ≤ (4 / 9:ℝ) * d ^ 2 by positivity) he)]
  have htD : theta ^ 2 * D ≤ 256 / 81 := by
    have h := mul_nonneg (sq_nonneg (theta - 8 / 3))
      (show 0 ≤ theta + 4 / 3 by linarith)
    rw [hD]
    nlinarith only [h]
  have hfac : theta ^ 2 * D + 4 * d ^ 2 * theta ≤ 256 / 81 + 16 * d ^ 2 := by
    nlinarith only [htD, mul_le_mul_of_nonneg_left hthmax (sq_nonneg d)]
  have hfac0 : 0 ≤ theta ^ 2 * D + 4 * d ^ 2 * theta := by positivity
  have hcost1 := mul_le_mul he2 hfac hfac0 (show 0 ≤ (16 / 81:ℝ) * d ^ 4 by positivity)
  have hcost2 : (16 / 81) * d ^ 4 * (256 / 81 + 16 * d ^ 2) ≤ (6400 / 6561) * d ^ 4 := by
    have h := mul_le_mul_of_nonneg_left hd2 (show 0 ≤ d ^ 4 by positivity)
    nlinarith only [h]
  have hcost3 : (6400 / 6561) * d ^ 4 ≤ 4 * d ^ 2 * beta := by
    have h := mul_le_mul_of_nonneg_left hbeta (show 0 ≤ 4 * d ^ 2 by positivity)
    nlinarith only [h, sq_nonneg (d ^ 2)]
  have hcost : theta ^ 2 * e ^ 2 * D ≤ 4 * d ^ 2 * (beta - theta * e ^ 2) := by
    nlinarith only [hcost1,hcost2,hcost3]
  have hd4 : 0 < 4 * d ^ 2 := by positivity
  have hc : 0 ≤ beta - theta * e ^ 2 := by
    have ht0 : 0 ≤ theta ^ 2 * e ^ 2 * D := by positivity
    nlinarith only [hcost, ht0, hd4]
  have hm1 := mul_le_mul_of_nonneg_left hvariance
    (show 0 ≤ theta ^ 2 * e ^ 2 by positivity)
  have hm2 := mul_le_mul_of_nonneg_left hcost hS
  have hm : (theta * e * z) ^ 2 ≤ S * (beta - theta * e ^ 2) := by
    apply (mul_le_mul_iff_right₀ hd4).mp
    nlinarith only [hm1, hm2]
  have hx2 := mul_le_mul_of_nonneg_right hm (sq_nonneg x)
  have hyoung := two_mul_le_add_of_sq_le_mul hS
    (mul_nonneg hc (sq_nonneg x))
    (show (theta * e * z * x) ^ 2 ≤ S * ((beta - theta * e ^ 2) * x ^ 2) by nlinarith only [hx2])
  nlinarith only [hyoung]

private theorem coupled_of_margin (a b u v x w e beta : ℝ)
    (hA : 0 ≤ 2 * a - u) (hC : 0 ≤ 2 * b - v)
    (he : 0 ≤ e) (hx : 0 ≤ x) (hw : 0 ≤ w)
    (hth : 0 ≤ 3 * (u + v) - 2 * (a + b))
    (hcouple : w ≤ Real.sqrt ((2 * a - u) * (2 * b - v)) + e * x)
    (hmargin : 2 * (3 * (u + v) - 2 * (a + b)) * e * Real.sqrt ((2 * a - u) * (2 * b - v)) * x + 
      ((3 * (u + v) - 2 * (a + b)) * e ^ 2 - beta) * x ^ 2 ≤
      (2 * a - u) * (u + v - 2 * b) ^ 2 + (2 * b - v) * (u + v - 2 * a) ^ 2) :
    (u + v) * (u ^ 2 - u * v + v ^ 2 + 3 * w ^ 2) ≤
      2 * (a * (u ^ 2 + w ^ 2) + b * (v ^ 2 + w ^ 2)) + beta * x ^ 2 := by
  have hr := Real.sq_sqrt (mul_nonneg hA hC)
  have hs0 : 0 ≤ Real.sqrt ((2 * a - u) * (2 * b - v)) + e * x := by positivity
  have hsq : w ^ 2 ≤ (Real.sqrt ((2 * a - u) * (2 * b - v)) + e * x) ^ 2 :=
    (sq_le_sq₀ hw hs0).mpr hcouple
  have hm := mul_le_mul_of_nonneg_left hsq hth
  have hrt := congrArg (fun z : ℝ => (3 * (u + v) - 2 * (a + b)) * z) hr
  nlinarith only [hrt,hm,hmargin]

private theorem normalized_small (a b u v x w : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hs : a + b = 1) (hab : b < a)
    (hcontrast : a ≤ 2 * b)
    (huL : -2 * a ≤ u) (huR : u ≤ 2 * a)
    (hvL : -2 * b ≤ v) (hvR : v ≤ 2 * b)
    (htrace : 0 ≤ u + v) (hx : 0 ≤ x) (hw : 0 ≤ w)
    (hth : 0 ≤ 3 * (u + v) - 2 * (a + b))
    (hDpos : 0 < 2 * (a + b) - (u + v))
    (hcouple : w ≤ Real.sqrt ((2 * a - u) * (2 * b - v)) + excess a b * x) :
    (u + v) * (u ^ 2 - u * v + v ^ 2 + 3 * w ^ 2) ≤
      2 * (a * (u ^ 2 + w ^ 2) + b * (v ^ 2 + w ^ 2)) + penalty a b * x ^ 2 := by
  let d := a - b
  let r := Real.sqrt (a * b)
  let A := 2 * a - u
  let C := 2 * b - v
  let theta := 3 * (u + v) - 2 * (a + b)
  let D := 2 * (a + b) - (u + v)
  let S := A * (u + v - 2 * b) ^ 2 + C * (u + v - 2 * a) ^ 2
  have hA : 0 ≤ A := by dsimp [A]; linarith
  have hC : 0 ≤ C := by dsimp [C]; linarith
  have hd : 0 < d := sub_pos.mpr hab
  have hdmax : d ≤ 1 / 3 := by dsimp [d]; linarith
  have hd2 : d ^ 2 ≤ 1 / 9 := by nlinarith
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = (1 - d ^ 2) / 4 := by
    dsimp [r,d]
    rw [Real.sq_sqrt (mul_pos ha hb).le]
    nlinarith only [sq_nonneg (a + b - 1),hs]
  have hrmin : 2 / 5 ≤ r := by nlinarith
  have hrmax : r ≤ 1 / 2 := by nlinarith [sq_nonneg d]
  have hrat : 1 / 2 - r ≤ (5 / 18) * d ^ 2 := by
    have hm := mul_le_mul_of_nonneg_right
      (show 9 / 10 ≤ 1 / 2 + r by linarith) (show 0 ≤ 1 / 2 - r by linarith)
    nlinarith only [hm,hr2]
  have haeq : a = 1 - b := by linarith
  have hem : excess a b = (3 + d ^ 2) / 6 - r := by
    dsimp [excess,mean]
    rw [hs]
    dsimp [d,r]
    rw [haeq]
    ring
  have hep : excess a b ≤ (4 / 9) * d ^ 2 := by rw [hem]; linarith
  have hpen : penalty a b = d ^ 2 * (5 - d ^ 2) / 18 := by
    dsimp [penalty,d]
    rw [hs,haeq]
    ring
  have hbeta : (22 / 81) * d ^ 2 ≤ penalty a b := by
    rw [hpen]
    have hm := mul_le_mul_of_nonneg_left hd2 (sq_nonneg d)
    nlinarith only [hm]
  have htheta : 0 ≤ theta := hth
  have hthetamax : theta ≤ 4 := by dsimp [theta]; linarith
  have hDeq : D = (4 - theta) / 3 := by dsimp [D,theta]; linarith
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hz2 := Real.sq_sqrt (mul_nonneg hA hC)
  have hvar : 4 * d ^ 2 * (Real.sqrt (A * C)) ^ 2 ≤ S * D := by
    rw [hz2]
    have heq : S * D - 4 * d ^ 2 * A * C = 
        (A * (u + v - 2 * b) + C * (u + v - 2 * a)) ^ 2 := by
      dsimp [S,D,A,C,d]
      ring
    nlinarith only [heq,sq_nonneg (A * (u + v - 2 * b) + C * (u + v - 2 * a))]
  have hm := small_margin d (excess a b) (penalty a b) theta D S
    (Real.sqrt (A * C)) x hd hdmax (excess_nonneg a b ha hb) hep hbeta
    htheta hthetamax hDeq hDpos hS hvar
  exact coupled_of_margin a b u v x w (excess a b) (penalty a b)
    hA hC (excess_nonneg a b ha hb) hx hw hth hcouple hm

private theorem large_margin (t A C ell x e beta : ℝ)
    (ht : 0 ≤ t) (ht2 : 2 * t ^ 2 ≤ 1)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hCmax : C ≤ 4 * t ^ 2)
    (he : 0 ≤ e) (hbeta : 0 ≤ beta)
    (hx : 0 ≤ x) (hrow : x ^ 2 ≤ 2 * A)
    (htheta : 0 ≤ 3 * ell - 2 * (1 + t ^ 2))
    (hJ : ∀ y : ℝ, 0 ≤ y → y ^ 2 ≤ 2 →
      0 ≤ 2 * (1 - 2 * t ^ 2) * (4 * e * t * y + e ^ 2 * y ^ 2) + beta * y ^ 2-
        (9 / 4) * (4 * e * t * y + e ^ 2 * y ^ 2) ^ 2) :
    2 * (3 * ell - 2 * (1 + t ^ 2)) * e * Real.sqrt (A * C) * x + 
      ((3 * ell - 2 * (1 + t ^ 2)) * e ^ 2 - beta) * x ^ 2 ≤
      A * (ell - 2 * t ^ 2) ^ 2 + C * (ell - 2) ^ 2 := by
  by_cases hAz : A = 0
  · have hxz : x = 0 := by rw [hAz] at hrow; nlinarith only [hrow,sq_nonneg x]
    rw [hAz,hxz]
    simp only [zero_mul, Real.sqrt_zero, mul_zero, zero_pow, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_add]
    positivity
  have hAp : 0 < A := lt_of_le_of_ne hA (Ne.symm hAz)
  let y := x / Real.sqrt A
  have hsAp : 0 < Real.sqrt A := Real.sqrt_pos.mpr hAp
  have hy : 0 ≤ y := div_nonneg hx hsAp.le
  have hy2 : y ^ 2 ≤ 2 := by
    dsimp [y]
    rw [div_pow, Real.sq_sqrt hA]
    exact (div_le_iff₀ hAp).mpr (by nlinarith only [hrow])
  have hxy : x = Real.sqrt A * y := by dsimp [y]; field_simp
  have hsC : Real.sqrt C ≤ 2 * t :=
    (Real.sqrt_le_left (by positivity)).mpr (by nlinarith only [hCmax])
  have hcross := mul_le_mul_of_nonneg_left hsC
    (show 0 ≤ 2 * (3 * ell - 2 * (1 + t ^ 2)) * e * y by positivity)
  let T := 4 * e * t * y + e ^ 2 * y ^ 2
  have hJn := hJ y hy hy2
  have hpos : 0 ≤ (ell - 2 * t ^ 2) ^ 2 - (3 * ell - 2 * (1 + t ^ 2)) * T + beta * y ^ 2 := by
    have hid : (ell - 2 * t ^ 2) ^ 2 - (3 * ell - 2 * (1 + t ^ 2)) * T + beta * y ^ 2 = 
        (ell - 2 * t ^ 2 - 3 * T / 2) ^ 2 + 
        (2 * (1 - 2 * t ^ 2) * T + beta * y ^ 2 - (9 / 4) * T ^ 2) := by ring
    rw [hid]
    exact add_nonneg (sq_nonneg _) hJn
  have hbound : -(ell - 2 * t ^ 2) ^ 2 + 
      2 * (3 * ell - 2 * (1 + t ^ 2)) * e * Real.sqrt C * y + 
      ((3 * ell - 2 * (1 + t ^ 2)) * e ^ 2 - beta) * y ^ 2 ≤ 0 := by
    dsimp [T] at hpos
    nlinarith only [hcross,hpos]
  have hm := mul_nonpos_of_nonneg_of_nonpos hA hbound
  have hcpos := mul_nonneg hC (sq_nonneg (ell - 2))
  have hid :
      2 * (3 * ell - 2 * (1 + t ^ 2)) * e * Real.sqrt (A * C) * x + 
        ((3 * ell - 2 * (1 + t ^ 2)) * e ^ 2 - beta) * x ^ 2-
        (A * (ell - 2 * t ^ 2) ^ 2 + C * (ell - 2) ^ 2) = 
      A * (-(ell - 2 * t ^ 2) ^ 2 + 
        2 * (3 * ell - 2 * (1 + t ^ 2)) * e * Real.sqrt C * y + 
        ((3 * ell - 2 * (1 + t ^ 2)) * e ^ 2 - beta) * y ^ 2) - C * (ell - 2) ^ 2 := by
    rw [Real.sqrt_mul hA,hxy]
    nlinarith only [congrArg (fun z : ℝ =>
      (2 * (3 * ell - 2 * (1 + t ^ 2)) * e * Real.sqrt C * y + 
        ((3 * ell - 2 * (1 + t ^ 2)) * e ^ 2 - beta) * y ^ 2) * z)
        (Real.sq_sqrt hA)]
  linarith only [hid,hm,hcpos]

private theorem normalized_large (t u v x w : ℝ)
    (ht : 0 < t) (ht2 : 2 * t ^ 2 ≤ 1)
    (huL : -2 ≤ u) (huR : u ≤ 2)
    (hvL : -2 * t ^ 2 ≤ v) (hvR : v ≤ 2 * t ^ 2)
    (hx : 0 ≤ x) (hw : 0 ≤ w)
    (hth : 0 ≤ 3 * (u + v) - 2 * (1 + t ^ 2))
    (hcouple : w ≤ Real.sqrt ((2 - u) * (2 * t ^ 2 - v)) + excess 1 (t ^ 2) * x)
    (hrow : x ^ 2 ≤ 2 * (2 - u)) :
    (u + v) * (u ^ 2 - u * v + v ^ 2 + 3 * w ^ 2) ≤
      2 * ((u ^ 2 + w ^ 2) + t ^ 2 * (v ^ 2 + w ^ 2)) + penalty 1 (t ^ 2) * x ^ 2 := by
  have heq : excess 1 (t ^ 2) = HsfQubitCubicCertificate.e t := by
    dsimp [excess,mean,HsfQubitCubicCertificate.e]
    rw [one_mul,Real.sqrt_sq ht.le]
    field_simp
    ring
  have hbeq : penalty 1 (t ^ 2) = HsfQubitCubicCertificate.beta t := by
    dsimp [penalty,HsfQubitCubicCertificate.beta]
    ring
  have he : 0 ≤ excess 1 (t ^ 2) := excess_nonneg 1 (t ^ 2) (by norm_num) (sq_pos_of_pos ht)
  have hb : 0 ≤ penalty 1 (t ^ 2) := by
    dsimp [penalty]
    positivity
  have hA : 0 ≤ 2 - u := by linarith
  have hC : 0 ≤ 2 * t ^ 2 - v := by linarith
  have hCm : 2 * t ^ 2 - v ≤ 4 * t ^ 2 := by linarith
  have hJ (y : ℝ) (hy : 0 ≤ y) (hy2 : y ^ 2 ≤ 2) :
      0 ≤ 2 * (1 - 2 * t ^ 2) * (4 * excess 1 (t ^ 2) * t * y + (excess 1 (t ^ 2)) ^ 2 * y ^ 2) + 
        penalty 1 (t ^ 2) * y ^ 2 - (9 / 4) * (4 * excess 1 (t ^ 2) * t * y + (excess 1 (t ^ 2)) ^ 2 * y ^ 2) ^ 2 := by
    rw [heq,hbeq]
    exact HsfQubitCubicCertificate.rectangular_J_nonneg t y ht.le ht2 hy hy2
  have hm := large_margin t (2 - u) (2 * t ^ 2 - v) (u + v) x
    (excess 1 (t ^ 2)) (penalty 1 (t ^ 2)) ht.le ht2 hA hC hCm he hb hx hrow hth hJ
  simpa only [one_mul] using
    coupled_of_margin 1 (t ^ 2) u v x w (excess 1 (t ^ 2)) (penalty 1 (t ^ 2))
      (by simpa using hA) hC he hx hw hth
      (by simpa only [mul_one] using hcouple) (by simpa only [mul_one] using hm)

private theorem excess_scale (s a b : ℝ) (hs : 0 < s) (ha : 0 < a) (hb : 0 < b) :
    excess (s * a) (s * b) = s * excess a b := by
  have hroot : Real.sqrt ((s * a) * (s * b)) = s * Real.sqrt (a * b) := by
    rw [show (s * a) * (s * b) = s ^ 2 * (a * b) by ring,
      Real.sqrt_mul (sq_nonneg s),Real.sqrt_sq hs.le]
  dsimp [excess,mean]
  rw [hroot]
  field_simp [show 3 * (s * a + s * b) ≠ 0 by positivity,
    show 3 * (a + b) ≠ 0 by positivity] <;> ring

private theorem penalty_scale (s a b : ℝ) (hs : 0 < s) (ha : 0 < a) (hb : 0 < b) :
    penalty (s * a) (s * b) = s ^ 3 * penalty a b := by
  dsimp [penalty]
  field_simp [show 9 * (s * a + s * b) ≠ 0 by positivity,
    show 9 * (a + b) ≠ 0 by positivity] <;> ring

private theorem bound_scale (s a b u v x w : ℝ)
    (hs : 0 < s) (ha : 0 < a) (hb : 0 < b)
    (h : (u + v) * (u ^ 2 - u * v + v ^ 2 + 3 * w ^ 2) ≤
      2 * (a * (u ^ 2 + w ^ 2) + b * (v ^ 2 + w ^ 2)) + penalty a b * x ^ 2) :
    (s * u + s * v) * ((s * u) ^ 2 - (s * u) * (s * v) + (s * v) ^ 2 + 3 * (s * w) ^ 2) ≤
      2 * ((s * a) * ((s * u) ^ 2 + (s * w) ^ 2) + (s * b) * ((s * v) ^ 2 + (s * w) ^ 2)) + 
        penalty (s * a) (s * b) * x ^ 2 := by
  rw [penalty_scale s a b hs ha hb]
  have hm := mul_le_mul_of_nonneg_left h (pow_nonneg hs.le 3)
  nlinarith only [hm]

private theorem coupling_scale_down (s a b u v x w : ℝ)
    (hs : 0 < s) (ha : 0 < a) (hb : 0 < b)
    (hA : u ≤ 2 * a) (hC : v ≤ 2 * b)
    (h : s * w ≤ Real.sqrt ((2 * (s * a) - s * u) * (2 * (s * b) - s * v)) + 
      excess (s * a) (s * b) * x) :
    w ≤ Real.sqrt ((2 * a - u) * (2 * b - v)) + excess a b * x := by
  have hroot : Real.sqrt ((2 * (s * a) - s * u) * (2 * (s * b) - s * v)) = 
      s * Real.sqrt ((2 * a - u) * (2 * b - v)) := by
    rw [show (2 * (s * a) - s * u) * (2 * (s * b) - s * v) = s ^ 2 * ((2 * a - u) * (2 * b - v)) by ring,
      Real.sqrt_mul (sq_nonneg s),Real.sqrt_sq hs.le]
  rw [hroot,excess_scale s a b hs ha hb] at h
  apply (mul_le_mul_iff_right₀ hs).mp
  nlinarith only [h]

private theorem coupling_div (s a b u v x w : ℝ)
    (hs : 0 < s) (ha : 0 < a) (hb : 0 < b)
    (huR : u ≤ 2 * a) (hvR : v ≤ 2 * b)
    (h : w ≤ Real.sqrt ((2 * a - u) * (2 * b - v)) + excess a b * x) :
    w / s ≤ Real.sqrt ((2 * (a / s) - u / s) * (2 * (b / s) - v / s)) + excess (a / s) (b / s) * x := by
  have hmul (z : ℝ) : s * (z / s) = z := by field_simp
  apply coupling_scale_down s (a / s) (b / s) (u / s) (v / s) x (w / s)
    hs (div_pos ha hs) (div_pos hb hs)
  · convert div_le_div_of_nonneg_right huR hs.le using 1 <;> ring
  · convert div_le_div_of_nonneg_right hvR hs.le using 1 <;> ring
  · simpa only [hmul] using h

private theorem bound_div (s a b u v x w : ℝ)
    (hs : 0 < s) (ha : 0 < a) (hb : 0 < b)
    (h : (u / s + v / s) * ((u / s) ^ 2 - (u / s) * (v / s) + (v / s) ^ 2 + 3 * (w / s) ^ 2) ≤
      2 * ((a / s) * ((u / s) ^ 2 + (w / s) ^ 2) + (b / s) * ((v / s) ^ 2 + (w / s) ^ 2)) + 
        penalty (a / s) (b / s) * x ^ 2) :
    (u + v) * (u ^ 2 - u * v + v ^ 2 + 3 * w ^ 2) ≤
      2 * (a * (u ^ 2 + w ^ 2) + b * (v ^ 2 + w ^ 2)) + penalty a b * x ^ 2 := by
  have hmul (z : ℝ) : s * (z / s) = z := by field_simp
  simpa only [hmul] using bound_scale s (a / s) (b / s) (u / s) (v / s) x (w / s)
    hs (div_pos ha hs) (div_pos hb hs) h

/-- The full one-sided cubic estimate for two ordered positive spectral levels.
The coupling and row hypotheses follow from the original four PSD endpoints;
neither an optimizer condition nor a trace restriction beyond sign is imposed. -/
theorem coupled_cubic_le (a b u v x w : ℝ)
    (hb : 0 < b) (hab : b ≤ a)
    (huL : -2 * a ≤ u) (huR : u ≤ 2 * a)
    (hvL : -2 * b ≤ v) (hvR : v ≤ 2 * b)
    (htrace : 0 ≤ u + v) (hx : 0 ≤ x) (hw : 0 ≤ w)
    (hcouple : w ≤ Real.sqrt ((2 * a - u) * (2 * b - v)) + excess a b * x)
    (hrow : x ^ 2 ≤ 2 * (2 * a - u) / a) :
    (u + v) * (u ^ 2 - u * v + v ^ 2 + 3 * w ^ 2) ≤
      2 * (a * (u ^ 2 + w ^ 2) + b * (v ^ 2 + w ^ 2)) + penalty a b * x ^ 2 := by
  have ha : 0 < a := hb.trans_le hab
  have hA : 0 ≤ 2 * a - u := by linarith
  have hC : 0 ≤ 2 * b - v := by linarith
  have hpen : 0 ≤ penalty a b := by dsimp [penalty]; positivity
  by_cases hth : 3 * (u + v) - 2 * (a + b) ≤ 0
  · have hm := mul_nonpos_of_nonpos_of_nonneg hth (sq_nonneg w)
    have hAa := mul_nonneg hA (sq_nonneg u)
    have hCv := mul_nonneg hC (sq_nonneg v)
    have hpx := mul_nonneg hpen (sq_nonneg x)
    nlinarith only [hm,hAa,hCv,hpx]
  have htheta : 0 ≤ 3 * (u + v) - 2 * (a + b) := le_of_lt (lt_of_not_ge hth)
  by_cases heq : a = b
  · have he0 : excess a b = 0 := by
      rw [heq]
      dsimp [excess,mean]
      simp only [←pow_two,Real.sqrt_sq hb.le]
      field_simp [hb.ne']
      ring
    apply coupled_of_margin a b u v x w (excess a b) (penalty a b)
      hA hC (excess_nonneg a b ha hb) hx hw htheta hcouple
    rw [he0]
    have hp := mul_nonneg hpen (sq_nonneg x)
    have hS : 0 ≤ (2 * a - u) * (u + v - 2 * b) ^ 2 + (2 * b - v) * (u + v - 2 * a) ^ 2 := by positivity
    nlinarith only [hp,hS]
  have habs : b < a := lt_of_le_of_ne hab (Ne.symm heq)
  by_cases hDz : 2 * (a + b) - (u + v) = 0
  · have hAz : 2 * a - u = 0 := by linarith
    have hCz : 2 * b - v = 0 := by linarith
    have hxz : x = 0 := by rw [hAz] at hrow; simp only [mul_zero,zero_div] at hrow; nlinarith only [hrow,sq_nonneg x]
    have hwz : w = 0 := by rw [hAz,hxz] at hcouple; simp at hcouple; linarith
    have hu : u = 2 * a := by linarith
    have hv : v = 2 * b := by linarith
    rw [hwz,hxz,hu,hv]
    ring_nf
    exact le_rfl
  have hDp : 0 < 2 * (a + b) - (u + v) :=
    lt_of_le_of_ne (by linarith) (Ne.symm hDz)
  by_cases hcontrast : a ≤ 2 * b
  · let s := a + b
    have hs : 0 < s := add_pos ha hb
    apply bound_div s a b u v x w hs ha hb
    apply normalized_small (a / s) (b / s) (u / s) (v / s) x (w / s)
      (div_pos ha hs) (div_pos hb hs)
    · dsimp [s]; rw [←add_div,div_self hs.ne']
    · exact (div_lt_div_iff_of_pos_right hs).mpr habs
    · convert div_le_div_of_nonneg_right hcontrast hs.le using 1 <;> ring
    · convert div_le_div_of_nonneg_right huL hs.le using 1 <;> ring
    · convert div_le_div_of_nonneg_right huR hs.le using 1 <;> ring
    · convert div_le_div_of_nonneg_right hvL hs.le using 1 <;> ring
    · convert div_le_div_of_nonneg_right hvR hs.le using 1 <;> ring
    · simpa only [←add_div] using div_nonneg htrace hs.le
    · exact hx
    · exact div_nonneg hw hs.le
    · convert div_nonneg htheta hs.le using 1 <;> ring
    · convert div_pos hDp hs using 1 <;> ring
    · exact coupling_div s a b u v x w hs ha hb huR hvR hcouple
  · let t := Real.sqrt (b / a)
    have ht : 0 < t := Real.sqrt_pos.mpr (div_pos hb ha)
    have htq : t ^ 2 = b / a := Real.sq_sqrt (div_pos hb ha).le
    have ht2 : 2 * t ^ 2 ≤ 1 := by
      rw [htq]
      convert (div_le_iff₀ ha).mpr (show 2 * b ≤ 1 * a by linarith) using 1 <;> ring
    apply bound_div a a b u v x w ha ha hb
    have haa : a / a = 1 := div_self ha.ne'
    rw [haa,←htq]
    simp only [one_mul]
    apply normalized_large t (u / a) (v / a) x (w / a) ht ht2
    · convert div_le_div_of_nonneg_right huL ha.le using 1 <;> field_simp
    · exact (div_le_iff₀ ha).mpr (by linarith)
    · rw [htq]; convert div_le_div_of_nonneg_right hvL ha.le using 1 <;> ring
    · rw [htq]; convert div_le_div_of_nonneg_right hvR ha.le using 1 <;> ring
    · exact hx
    · exact div_nonneg hw ha.le
    · rw [htq]
      convert div_nonneg htheta ha.le using 1 <;> field_simp <;> ring
    · simpa only [haa,htq,mul_one] using coupling_div a a b u v x w ha ha hb huR hvR hcouple
    · convert hrow using 1 <;> field_simp <;> ring

#print axioms excess_nonneg
#print axioms coupled_cubic_le

end D5.S3.Quantum.Matrix.HsfQubitCoupledScalar
