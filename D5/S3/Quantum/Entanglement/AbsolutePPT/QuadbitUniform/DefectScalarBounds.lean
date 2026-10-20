/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/DefectScalarBounds
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/DefectScalarBounds
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: none
   digest: Scalar defect transport and ordered-head middle-energy inequalities. -/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound
noncomputable section

theorem affine_defect_transport (theta N j w c E : ℝ)
    (ht : 0 ≤ theta) (hw : 0 ≤ w) (hj : 6 ≤ j)
    (ha0 : 0 ≤ 2*theta*(N+3+2*w)-(2+w))
    (ha1 : 2*theta*(N+3+2*w)-(2+w) ≤ 1/4)
    (hF0 : 0 ≤ theta*(N+3+2*w)^2-(N+11+3*w+w^2))
    (hE0 : E ≤ 5-4*w-w^2)
    (hE1 : E ≤ 5-4*w-w^2+(c-(3-4*w))/4) :
    (2+w)*(N+w*j+c)-(1+w)*N+E ≤ theta*(N+w*j+c)^2 := by
  let L := N+3+2*w
  let e := w*(j-6)
  let a := 2*theta*L-(2+w)
  have he : 0 ≤ e := mul_nonneg hw (by linarith)
  have ha : 0 ≤ a := ha0
  have ha' : 0 ≤ 1/4-a := sub_nonneg.mpr ha1
  have hF : 0 ≤ theta*L^2-(2+w)*L+(1+w)*N-(5-4*w-w^2) := by
    dsimp [L]
    nlinarith only [hF0]
  by_cases hc : 3-4*w ≤ c
  · let d := c-(3-4*w)
    have hd : 0 ≤ d := sub_nonneg.mpr hc
    have hpos : 0 ≤ theta*(e+d)^2+a*(e+d) :=
      add_nonneg (mul_nonneg ht (sq_nonneg _))
        (mul_nonneg ha (add_nonneg he hd))
    have hid : theta*(N+w*j+c)^2-
        ((2+w)*(N+w*j+c)-(1+w)*N+(5-4*w-w^2)) =
        (theta*L^2-(2+w)*L+(1+w)*N-(5-4*w-w^2))+
        theta*(e+d)^2+a*(e+d) := by dsimp [L,e,d,a]; ring
    linarith
  · let d := (3-4*w)-c
    have hd : 0 ≤ d := by dsimp [d]; linarith
    have hpos : 0 ≤ theta*(e-d)^2+a*e+(1/4-a)*d :=
      add_nonneg (add_nonneg (mul_nonneg ht (sq_nonneg _)) (mul_nonneg ha he))
        (mul_nonneg ha' hd)
    have hid : theta*(N+w*j+c)^2-
        ((2+w)*(N+w*j+c)-(1+w)*N+(5-4*w-w^2-d/4)) =
        (theta*L^2-(2+w)*L+(1+w)*N-(5-4*w-w^2))+
        theta*(e-d)^2+a*e+(1/4-a)*d := by dsimp [L,e,d,a]; ring
    have hE : E ≤ 5-4*w-w^2-d/4 := by dsimp [d]; linarith [hE1]
    linarith

-- Shared original scalar PSD consequences, extracted from flat_five_moment.
-- Both the original zero-jump proof and the middle-energy proof consume them.
theorem flat_third_head_le_one (a b e : ℝ)
    (hab : b ≤ a) (hbe : e ≤ b) (he0 : 0 ≤ e)
    (hdet : a ^ 2 + b ^ 2 + e ^ 2 + a * b * e ≤ 4) : e ≤ 1 := by
  have hb0 : 0 ≤ b := he0.trans hbe
  have ha0 : 0 ≤ a := hb0.trans hab
  have hae : e ≤ a := hbe.trans hab
  have habprod : e ^ 2 ≤ a * b := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hae) hb0,
      mul_nonneg he0 (sub_nonneg.mpr hbe)]
  have hecube : e ^ 3 + 3 * e ^ 2 ≤ 4 := by
    nlinarith [mul_le_mul_of_nonneg_right habprod he0,
      mul_nonneg (sub_nonneg.mpr hae) (add_nonneg ha0 he0),
      mul_nonneg (sub_nonneg.mpr hbe) (add_nonneg hb0 he0)]
  by_contra h
  have hesq : 1 < e ^ 2 := by
    nlinarith [mul_pos (by linarith : 0 < e - 1) (by linarith : 0 < e + 1)]
  have hp := mul_nonneg (sq_nonneg e) (by linarith : 0 ≤ e - 1)
  nlinarith only [hecube, hesq, hp]

theorem flat_endpoint_ge_third (e : ℝ) (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    e ≤ 2 - e ^ 2 := by
  have hp := mul_nonneg (sub_nonneg.mpr he1) (by linarith : 0 ≤ e + 2)
  nlinarith only [hp]

theorem flat_pair_square_le_low (a b e : ℝ)
    (hae : e ≤ a) (hbe : e ≤ b) :
    a ^ 2 + b ^ 2 ≤ (a + b - e) ^ 2 + e ^ 2 := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hae) (sub_nonneg.mpr hbe)]

theorem flat_pair_square_le_high (a b e : ℝ)
    (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hdet : a ^ 2 + b ^ 2 + e ^ 2 + a * b * e ≤ 4)
    (hs : (2 - e ^ 2) + e ≤ a + b) :
    a ^ 2 + b ^ 2 ≤ (2 - e ^ 2) ^ 2 + e ^ 2 := by
  let A := 2 - e ^ 2
  change A + e ≤ a + b at hs
  change a ^ 2 + b ^ 2 ≤ A ^ 2 + e ^ 2
  have hAe : e ≤ A := flat_endpoint_ge_third e he0 he1
  have hpoly : (2 - e) * (a ^ 2 + b ^ 2 - (A ^ 2 + e ^ 2)) ≤
      -e * ((a + b) - (A + e)) * ((a + b) + (A + e)) := by
    dsimp [A]
    nlinarith only [hdet]
  have hp := mul_nonneg (mul_nonneg he0 (sub_nonneg.mpr hs))
    (by linarith [hAe] : 0 ≤ (a + b) + (A + e))
  by_contra h
  have hpos := mul_pos (by linarith : 0 < 2 - e)
    (by linarith : 0 < a ^ 2 + b ^ 2 - (A ^ 2 + e ^ 2))
  linarith only [hpoly, hp, hpos]

-- The middle proof uses scalar comparison points, not replacement PSD spectra.
-- In particular, the second minimum entry may be negative at such a point.
private def middleFormula (w z e : ℝ) : ℝ :=
  z ^ 2 + 2 * e ^ 2 - w * (z + 2 * e) +
    e * min (2 * (e - w)) (4 - 3 * w - z - 2 * e)

private def middleFull (w e : ℝ) : ℝ :=
  4 - 2 * w - 4 * w * e + w * e ^ 2 + e ^ 4

private def middleTrunc (w e : ℝ) : ℝ :=
  4 - 2 * w + 2 * e - 5 * w * e + (w - 4) * e ^ 2 + e ^ 3 + e ^ 4

private theorem middleFormula_eq_min (w z e : ℝ) (he0 : 0 ≤ e) :
    middleFormula w z e =
      min (z ^ 2 + 4 * e ^ 2 - w * z - 4 * w * e)
        (z ^ 2 - (w + e) * z + (4 - 5 * w) * e) := by
  unfold middleFormula
  rw [mul_min_of_nonneg _ _ he0, ← min_add_add_left]
  congr 1 <;> ring

private theorem middleFormula_mono (w z A e : ℝ)
    (hw0 : 0 ≤ w) (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hz : 1 + w ≤ z) (hzA : z ≤ A) :
    middleFormula w z e ≤ middleFormula w A e := by
  rw [middleFormula_eq_min w z e he0, middleFormula_eq_min w A e he0]
  apply min_le_min
  · have hp := mul_nonneg (sub_nonneg.mpr hzA)
      (by linarith : 0 ≤ A + z - w)
    nlinarith only [hp]
  · have hp := mul_nonneg (sub_nonneg.mpr hzA)
      (by linarith : 0 ≤ A + z - w - e)
    nlinarith only [hp]

private theorem middle_secant_nonneg (w e : ℝ) (hw : 2 / 9 ≤ w) (hw1 : w ≤ 1 / 2)
    (he : 0 ≤ e) (he1 : e ≤ (3 / 5)) :
    0 ≤ 4 * w - (e + w) * (e ^ 2 + w ^ 2 + w) := by
  have wlo : 0 ≤ w - (2 / 9) := by linarith
  have whi : 0 ≤ (1 / 2) - w := by linarith
  have elo : 0 ≤ e - 0 := by linarith
  have ehi : 0 ≤ (3 / 5) - e := by linarith
  calc
    4 * w - (e + w) * (e ^ 2 + w ^ 2 + w) = (4832 / 27) * ((1 / 2) - w) ^ 3 * ((3 / 5) - e) ^ 3 +
      (22576 / 45) * ((1 / 2) - w) ^ 3 * (e - 0) ^ 1 * ((3 / 5) - e) ^ 2 +
      (101072 / 225) * ((1 / 2) - w) ^ 3 * (e - 0) ^ 2 * ((3 / 5) - e) ^ 1 +
      (269416 / 3375) * ((1 / 2) - w) ^ 3 * (e - 0) ^ 3 +
      (2224 / 3) * (w - (2 / 9)) ^ 1 * ((1 / 2) - w) ^ 2 * ((3 / 5) - e) ^ 3 +
      (10332 / 5) * (w - (2 / 9)) ^ 1 * ((1 / 2) - w) ^ 2 * (e - 0) ^ 1 * ((3 / 5) - e) ^ 2 +
      (45884 / 25) * (w - (2 / 9)) ^ 1 * ((1 / 2) - w) ^ 2 * (e - 0) ^ 2 * ((3 / 5) - e) ^ 1 +
      (138872 / 375) * (w - (2 / 9)) ^ 1 * ((1 / 2) - w) ^ 2 * (e - 0) ^ 3 +
      918 * (w - (2 / 9)) ^ 2 * ((1 / 2) - w) ^ 1 * ((3 / 5) - e) ^ 3 +
      (12672 / 5) * (w - (2 / 9)) ^ 2 * ((1 / 2) - w) ^ 1 * (e - 0) ^ 1 * ((3 / 5) - e) ^ 2 +
      (55494 / 25) * (w - (2 / 9)) ^ 2 * ((1 / 2) - w) ^ 1 * (e - 0) ^ 2 * ((3 / 5) - e) ^ 1 +
      (57924 / 125) * (w - (2 / 9)) ^ 2 * ((1 / 2) - w) ^ 1 * (e - 0) ^ 3 +
      351 * (w - (2 / 9)) ^ 3 * ((3 / 5) - e) ^ 3 +
      (4779 / 5) * (w - (2 / 9)) ^ 3 * (e - 0) ^ 1 * ((3 / 5) - e) ^ 2 +
      (20493 / 25) * (w - (2 / 9)) ^ 3 * (e - 0) ^ 2 * ((3 / 5) - e) ^ 1 +
      (21033 / 125) * (w - (2 / 9)) ^ 3 * (e - 0) ^ 3 := by ring
    _ ≥ 0 := by positivity

private theorem middle_trunc_gap (w e : ℝ) (hw : 2 / 9 ≤ w) (hw1 : w ≤ 1 / 2)
    (he : (3 / 5) ≤ e) (he1 : e ≤ 1) :
    0 ≤ 4 - 2 * w - 4 * w ^ 2 + w ^ 3 + w ^ 4 - (4 - 2 * w + 2 * e - 5 * w * e + (w - 4) * e ^ 2 + e ^ 3 + e ^ 4) := by
  have wlo : 0 ≤ w - (2 / 9) := by linarith
  have whi : 0 ≤ (1 / 2) - w := by linarith
  have elo : 0 ≤ e - (3 / 5) := by linarith
  have ehi : 0 ≤ 1 - e := by linarith
  calc
    4 - 2 * w - 4 * w ^ 2 + w ^ 3 + w ^ 4 - (4 - 2 * w + 2 * e - 5 * w * e + (w - 4) * e ^ 2 + e ^ 3 + e ^ 4) = (1217674 / 625) * ((1 / 2) - w) ^ 4 * (1 - e) ^ 4 +
      (306394 / 25) * ((1 / 2) - w) ^ 4 * (e - (3 / 5)) ^ 1 * (1 - e) ^ 3 +
      (622158 / 25) * ((1 / 2) - w) ^ 4 * (e - (3 / 5)) ^ 2 * (1 - e) ^ 2 +
      (96854 / 5) * ((1 / 2) - w) ^ 4 * (e - (3 / 5)) ^ 3 * (1 - e) ^ 1 +
      4624 * ((1 / 2) - w) ^ 4 * (e - (3 / 5)) ^ 4 +
      (6071571 / 625) * (w - (2 / 9)) ^ 1 * ((1 / 2) - w) ^ 3 * (1 - e) ^ 4 +
      (1486971 / 25) * (w - (2 / 9)) ^ 1 * ((1 / 2) - w) ^ 3 * (e - (3 / 5)) ^ 1 * (1 - e) ^ 3 +
      (2977317 / 25) * (w - (2 / 9)) ^ 1 * ((1 / 2) - w) ^ 3 * (e - (3 / 5)) ^ 2 * (1 - e) ^ 2 +
      (464481 / 5) * (w - (2 / 9)) ^ 1 * ((1 / 2) - w) ^ 3 * (e - (3 / 5)) ^ 3 * (1 - e) ^ 1 +
      22896 * (w - (2 / 9)) ^ 1 * ((1 / 2) - w) ^ 3 * (e - (3 / 5)) ^ 4 +
      (19895463 / 1250) * (w - (2 / 9)) ^ 2 * ((1 / 2) - w) ^ 2 * (1 - e) ^ 4 +
      (2468799 / 25) * (w - (2 / 9)) ^ 2 * ((1 / 2) - w) ^ 2 * (e - (3 / 5)) ^ 1 * (1 - e) ^ 3 +
      (4968378 / 25) * (w - (2 / 9)) ^ 2 * ((1 / 2) - w) ^ 2 * (e - (3 / 5)) ^ 2 * (1 - e) ^ 2 +
      (781569 / 5) * (w - (2 / 9)) ^ 2 * ((1 / 2) - w) ^ 2 * (e - (3 / 5)) ^ 3 * (1 - e) ^ 1 +
      (78813 / 2) * (w - (2 / 9)) ^ 2 * ((1 / 2) - w) ^ 2 * (e - (3 / 5)) ^ 4 +
      (53739693 / 5000) * (w - (2 / 9)) ^ 3 * ((1 / 2) - w) ^ 1 * (1 - e) ^ 4 +
      (3457647 / 50) * (w - (2 / 9)) ^ 3 * ((1 / 2) - w) ^ 1 * (e - (3 / 5)) ^ 1 * (1 - e) ^ 3 +
      (14133123 / 100) * (w - (2 / 9)) ^ 3 * ((1 / 2) - w) ^ 1 * (e - (3 / 5)) ^ 2 * (1 - e) ^ 2 +
      (1124847 / 10) * (w - (2 / 9)) ^ 3 * ((1 / 2) - w) ^ 1 * (e - (3 / 5)) ^ 3 * (1 - e) ^ 1 +
      (231093 / 8) * (w - (2 / 9)) ^ 3 * ((1 / 2) - w) ^ 1 * (e - (3 / 5)) ^ 4 +
      (26368659 / 10000) * (w - (2 / 9)) ^ 4 * (1 - e) ^ 4 +
      (1778031 / 100) * (w - (2 / 9)) ^ 4 * (e - (3 / 5)) ^ 1 * (1 - e) ^ 3 +
      (7407369 / 200) * (w - (2 / 9)) ^ 4 * (e - (3 / 5)) ^ 2 * (1 - e) ^ 2 +
      (597051 / 20) * (w - (2 / 9)) ^ 4 * (e - (3 / 5)) ^ 3 * (1 - e) ^ 1 +
      (124659 / 16) * (w - (2 / 9)) ^ 4 * (e - (3 / 5)) ^ 4 := by ring
    _ ≥ 0 := by positivity

private theorem middle_upper_endpoint (w e : ℝ)
    (hw : 2 / 9 ≤ w) (hw1 : w ≤ 1 / 2) (hwe : w ≤ e) (he1 : e ≤ 1) :
    middleFormula w (2 - e ^ 2) e ≤ 4 - 2 * w - 4 * w ^ 2 + w ^ 3 + w ^ 4 := by
  have he0 : 0 ≤ e := by linarith
  have hpoly : middleFormula w (2 - e ^ 2) e =
      min (middleFull w e) (middleTrunc w e) := by
    rw [middleFormula_eq_min w (2 - e ^ 2) e he0]
    congr 1 <;> dsimp [middleFull, middleTrunc] <;> ring
  rw [hpoly]
  by_cases he : e ≤ 3 / 5
  · have hp := mul_nonneg (sub_nonneg.mpr hwe) (middle_secant_nonneg w e hw hw1 he0 he)
    apply (min_le_left _ _).trans
    dsimp [middleFull]
    nlinarith only [hp]
  · apply (min_le_right _ _).trans
    have hp := middle_trunc_gap w e hw hw1 (by linarith) he1
    dsimp [middleTrunc]
    linarith only [hp]

-- The original tail chord is used only at (a,b,e,x,y).
-- The shared fixed-e suppliers then permit the scalar comparison to A=2-e².
theorem flat_five_middle_energy (w a b e x y : ℝ)
    (hw : 2 / 9 ≤ w) (hw1 : w ≤ 1 / 2) (ha : 1 + w ≤ a)
    (hab : b ≤ a) (hbe : e ≤ b) (hex : x ≤ e) (hxy : y ≤ x) (hyw : w ≤ y)
    (hmass : a + b + e + x + y ≤ 4 - w)
    (hdet : a ^ 2 + b ^ 2 + e ^ 2 + a * b * e ≤ 4) :
    a * (a - w) + b * (b - w) + e * (e - w) + x * (x - w) + y * (y - w) ≤
      4 - 2 * w - 4 * w ^ 2 + w ^ 3 + w ^ 4 := by
  have hw0 : 0 ≤ w := by linarith
  have hwe : w ≤ e := hyw.trans (hxy.trans hex)
  have he0 : 0 ≤ e := hw0.trans hwe
  have hae : e ≤ a := hbe.trans hab
  have he1 := flat_third_head_le_one a b e hab hbe he0 hdet
  let A := 2 - e ^ 2
  have hmin : x + y - 2 * w ≤ min (2 * (e - w)) (4 - 3 * w - (a + b) - e) :=
    le_min (by linarith) (by linarith only [hmass])
  have hc : x * (x - w) + y * (y - w) ≤
      e * min (2 * (e - w)) (4 - 3 * w - (a + b) - e) := by
    have hm := mul_le_mul_of_nonneg_left hmin he0
    have hx := mul_nonneg (by linarith : 0 ≤ x - w) (sub_nonneg.mpr hex)
    have hy := mul_nonneg (by linarith : 0 ≤ y - w) (by linarith : 0 ≤ e - y)
    nlinarith only [hm, hx, hy]
  have hG : a * (a - w) + b * (b - w) + e * (e - w) +
      x * (x - w) + y * (y - w) ≤ middleFormula w A e := by
    by_cases hs : a + b ≤ A + e
    · have hz : 1 + w ≤ a + b - e := by linarith
      have hzA : a + b - e ≤ A := by linarith
      have hq := flat_pair_square_le_low a b e hae hbe
      have hmono := middleFormula_mono w (a + b - e) A e hw0 he0 he1 hz hzA
      have hmin_eq : 4 - 3 * w - (a + b) - e =
          4 - 3 * w - (a + b - e) - 2 * e := by ring
      rw [hmin_eq] at hc
      dsimp [middleFormula] at hmono ⊢
      nlinarith only [hq, hc, hmono]
    · have hs' : A + e ≤ a + b := le_of_lt (lt_of_not_ge hs)
      have hq := flat_pair_square_le_high a b e he0 he1 hdet hs'
      have hm : min (2 * (e - w)) (4 - 3 * w - (a + b) - e) ≤
          min (2 * (e - w)) (4 - 3 * w - A - 2 * e) :=
        min_le_min le_rfl (by linarith)
      have hcmp := mul_le_mul_of_nonneg_left hm he0
      have hwcmp := mul_nonneg hw0 (sub_nonneg.mpr hs')
      change a ^ 2 + b ^ 2 ≤ A ^ 2 + e ^ 2 at hq
      dsimp [middleFormula]
      nlinarith only [hq, hc, hcmp, hwcmp]
  exact hG.trans (middle_upper_endpoint w e hw hw1 hwe he1)

end
end D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound
