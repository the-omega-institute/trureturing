/- GID: D5/S3/Geometry/Hyperideal/DoubleStarBernstein
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/DoubleStarBernstein
   mirror-E: none(waiver:exact-local-real-inequalities)
   anchors: []
   utility: none
   digest: Exact local real inequalities for CFMP opposite-edge transitions; no global geometric realization claimed. -/

import Mathlib.Tactic
import Mathlib.Analysis.Real.Sqrt

set_option autoImplicit false

/-! Exact closed-interval inequalities for the CFMP opposite-edge fan.
Every certificate is exposed as a polynomial identity checked by Lean's ring tactic. -/
namespace D5.S3.Geometry.Hyperideal.DoubleStarBernstein



def rad (x a b : ℝ) : ℝ := x^2 + a^2 + b^2 + 2*x*a*b - 1
def numerator (x a b c d o : ℝ) : ℝ := a*c + b*d + x*(a*d+b*c) - (x^2-1)*o
def denSq (x a b c d : ℝ) : ℝ := rad x a b * rad x c d
def margin (x a b c d o : ℝ) : ℝ :=
  4 * numerator x a b c d o ^ 2 - 3 * denSq x a b c d

private theorem endpoint_positive {x a c : ℝ} {n : ℕ}
    (hx₁ : 12 ≤ x) (hx₂ : x ≤ 20) (ha : 0 < a) (hc : 0 < c) :
    0 < a * (20-x)^n + c * (x-12)^n := by
  have hleft : 0 ≤ 20-x := sub_nonneg.mpr hx₂
  have hright : 0 ≤ x-12 := sub_nonneg.mpr hx₁
  rcases lt_or_ge x 20 with h | h
  · have hs : 0 < 20-x := sub_pos.mpr h
    exact add_pos_of_pos_of_nonneg (mul_pos ha (pow_pos hs _))
      (mul_nonneg hc.le (pow_nonneg hright _))
  · have hs : 0 < x-12 := by linarith only [h]
    exact add_pos_of_nonneg_of_pos (mul_nonneg ha.le (pow_nonneg hleft _))
      (mul_pos hc (pow_pos hs _))

private theorem quadratic_positive {x a b c : ℝ}
    (hx₁ : 12 ≤ x) (hx₂ : x ≤ 20) (ha : 0 < a) (hb : 0 ≤ b) (hc : 0 < c) :
    0 < a*(20-x)^2 + b*(x-12)*(20-x) + c*(x-12)^2 := by
  have hp := endpoint_positive (n:=2) hx₁ hx₂ ha hc
  have hb' := mul_nonneg (mul_nonneg hb (sub_nonneg.mpr hx₁)) (sub_nonneg.mpr hx₂)
  linarith only [hp, hb']

private theorem quartic_positive {x a b c d e : ℝ}
    (hx₁ : 12 ≤ x) (hx₂ : x ≤ 20) (ha : 0 < a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hd : 0 ≤ d) (he : 0 < e) :
    0 < a*(20-x)^4 + b*(x-12)*(20-x)^3 + c*(x-12)^2*(20-x)^2 +
      d*(x-12)^3*(20-x) + e*(x-12)^4 := by
  have hl : 0 ≤ 20-x := sub_nonneg.mpr hx₂
  have hr : 0 ≤ x-12 := sub_nonneg.mpr hx₁
  have hp := endpoint_positive (n:=4) hx₁ hx₂ ha he
  have hb' := mul_nonneg (mul_nonneg hb hr) (pow_nonneg hl 3)
  have hc' := mul_nonneg (mul_nonneg hc (pow_nonneg hr 2)) (pow_nonneg hl 2)
  have hd' := mul_nonneg (mul_nonneg hd (pow_nonneg hr 3)) hl
  linarith only [hp, hb', hc', hd']

theorem first_at_one (x : ℝ) (hx₁ : 12 ≤ x) (hx₂ : x ≤ 20) :
    0 < numerator x (101/100) (3/2) 500 (101/100) 1 ∧ 0 < margin x (101/100) (3/2) 500 (101/100) 1 := by
  constructor
  · have h : 0 < (46878781/5000) * (20-x)^2 + (61419183/2500) * (x-12) * (20-x) + (15127917/1000) * (x-12)^2 :=
      @quadratic_positive x (46878781/5000) (61419183/2500) (15127917/1000) hx₁ hx₂ (by norm_num) (by norm_num) (by norm_num)
    have hpoly : 64 * (numerator x (101/100) (3/2) 500 (101/100) 1) = (46878781/5000) * (20-x)^2 + (61419183/2500) * (x-12) * (20-x) + (15127917/1000) * (x-12)^2 := by
      unfold numerator
      ring
    linarith only [h, hpoly]
  · have h : 0 < (20792730463555873/100000000) * (20-x)^4 + (5466442001538693/5000000) * (x-12) * (20-x)^3 + (105352796153144499/50000000) * (x-12)^2 * (20-x)^2 + (44033706183379977/25000000) * (x-12)^3 * (20-x) + (53965751594448897/100000000) * (x-12)^4 :=
      @quartic_positive x (20792730463555873/100000000) (5466442001538693/5000000) (105352796153144499/50000000) (44033706183379977/25000000) (53965751594448897/100000000) hx₁ hx₂ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hpoly : 4096 * (margin x (101/100) (3/2) 500 (101/100) 1) = (20792730463555873/100000000) * (20-x)^4 + (5466442001538693/5000000) * (x-12) * (20-x)^3 + (105352796153144499/50000000) * (x-12)^2 * (20-x)^2 + (44033706183379977/25000000) * (x-12)^3 * (20-x) + (53965751594448897/100000000) * (x-12)^4 := by
      unfold margin numerator denSq rad
      ring
    linarith only [h, hpoly]

theorem middle_at_one (x : ℝ) (hx₁ : 12 ≤ x) (hx₂ : x ≤ 20) :
    0 < numerator x 500 (101/100) 500 (101/100) 1 ∧ 0 < margin x 500 (101/100) 500 (101/100) 1 := by
  constructor
  · have h : 0 < (2619780201/10000) * (20-x)^2 + (2659220201/5000) * (x-12) * (20-x) + (2698020201/10000) * (x-12)^2 :=
      @quadratic_positive x (2619780201/10000) (2659220201/5000) (2698020201/10000) hx₁ hx₂ (by norm_num) (by norm_num) (by norm_num)
    have hpoly : 64 * (numerator x 500 (101/100) 500 (101/100) 1) = (2619780201/10000) * (20-x)^2 + (2659220201/5000) * (x-12) * (20-x) + (2698020201/10000) * (x-12)^2 := by
      unfold numerator
      ring
    linarith only [h, hpoly]
  · have h : 0 < (6818268334502440401/100000000) * (20-x)^4 + (6906147662872120401/25000000) * (x-12) * (20-x)^3 + (20972519078424921203/50000000) * (x-12)^2 * (20-x)^2 + (7072164046711000401/25000000) * (x-12)^3 * (20-x) + (7149940756580200401/100000000) * (x-12)^4 :=
      @quartic_positive x (6818268334502440401/100000000) (6906147662872120401/25000000) (20972519078424921203/50000000) (7072164046711000401/25000000) (7149940756580200401/100000000) hx₁ hx₂ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hpoly : 4096 * (margin x 500 (101/100) 500 (101/100) 1) = (6818268334502440401/100000000) * (20-x)^4 + (6906147662872120401/25000000) * (x-12) * (20-x)^3 + (20972519078424921203/50000000) * (x-12)^2 * (20-x)^2 + (7072164046711000401/25000000) * (x-12)^3 * (20-x) + (7149940756580200401/100000000) * (x-12)^4 := by
      unfold margin numerator denSq rad
      ring
    linarith only [h, hpoly]

theorem last_at_one (x : ℝ) (hx₁ : 12 ≤ x) (hx₂ : x ≤ 20) :
    0 < numerator x 500 (101/100) (101/100) (101/100) 1 ∧ 0 < margin x 500 (101/100) (101/100) (101/100) 1 := by
  constructor
  · have h : 0 < (64352613/10000) * (20-x)^2 + (83633417/5000) * (x-12) * (20-x) + (102274221/10000) * (x-12)^2 :=
      @quadratic_positive x (64352613/10000) (83633417/5000) (102274221/10000) hx₁ hx₂ (by norm_num) (by norm_num) (by norm_num)
    have hpoly : 64 * (numerator x 500 (101/100) (101/100) (101/100) 1) = (64352613/10000) * (20-x)^2 + (83633417/5000) * (x-12) * (20-x) + (102274221/10000) * (x-12)^2 := by
      unfold numerator
      ring
    linarith only [h, hpoly]
  · have h : 0 < (1613565813784899/50000000) * (20-x)^4 + (1993697878684197/12500000) * (x-12) * (20-x)^3 + (7137192372056149/25000000) * (x-12)^2 * (20-x)^2 + (2724632348828457/12500000) * (x-12)^3 * (20-x) + (2985575152153419/50000000) * (x-12)^4 :=
      @quartic_positive x (1613565813784899/50000000) (1993697878684197/12500000) (7137192372056149/25000000) (2724632348828457/12500000) (2985575152153419/50000000) hx₁ hx₂ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hpoly : 4096 * (margin x 500 (101/100) (101/100) (101/100) 1) = (1613565813784899/50000000) * (20-x)^4 + (1993697878684197/12500000) * (x-12) * (20-x)^3 + (7137192372056149/25000000) * (x-12)^2 * (20-x)^2 + (2724632348828457/12500000) * (x-12)^3 * (20-x) + (2985575152153419/50000000) * (x-12)^4 := by
      unfold margin numerator denSq rad
      ring
    linarith only [h, hpoly]

theorem first_at_six (x : ℝ) (hx₁ : 12 ≤ x) (hx₂ : x ≤ 20) :
    0 < numerator x (101/100) (3/2) 500 (101/100) 6 ∧ 0 < margin x (101/100) (3/2) 500 (101/100) 6 := by
  constructor
  · have h : 0 < (43303781/5000) * (20-x)^2 + (55444183/2500) * (x-12) * (20-x) + (13132917/1000) * (x-12)^2 :=
      @quadratic_positive x (43303781/5000) (55444183/2500) (13132917/1000) hx₁ hx₂ (by norm_num) (by norm_num) (by norm_num)
    have hpoly : 64 * (numerator x (101/100) (3/2) 500 (101/100) 6) = (43303781/5000) * (20-x)^2 + (55444183/2500) * (x-12) * (20-x) + (13132917/1000) * (x-12)^2 := by
      unfold numerator
      ring
    linarith only [h, hpoly]
  · have h : 0 < (15634287917155873/100000000) * (20-x)^4 + (3935838255298693/5000000) * (x-12) * (20-x)^3 + (71770652864344499/50000000) * (x-12)^2 * (20-x)^2 + (27953670250579977/25000000) * (x-12)^3 * (20-x) + (31413606062448897/100000000) * (x-12)^4 :=
      @quartic_positive x (15634287917155873/100000000) (3935838255298693/5000000) (71770652864344499/50000000) (27953670250579977/25000000) (31413606062448897/100000000) hx₁ hx₂ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hpoly : 4096 * (margin x (101/100) (3/2) 500 (101/100) 6) = (15634287917155873/100000000) * (20-x)^4 + (3935838255298693/5000000) * (x-12) * (20-x)^3 + (71770652864344499/50000000) * (x-12)^2 * (20-x)^2 + (27953670250579977/25000000) * (x-12)^3 * (20-x) + (31413606062448897/100000000) * (x-12)^4 := by
      unfold margin numerator denSq rad
      ring
    linarith only [h, hpoly]

theorem middle_at_six (x : ℝ) (hx₁ : 12 ≤ x) (hx₂ : x ≤ 20) :
    0 < numerator x 500 (101/100) 500 (101/100) 6 ∧ 0 < margin x 500 (101/100) 500 (101/100) 6 := by
  constructor
  · have h : 0 < (2612630201/10000) * (20-x)^2 + (2647270201/5000) * (x-12) * (20-x) + (2678070201/10000) * (x-12)^2 :=
      @quadratic_positive x (2612630201/10000) (2647270201/5000) (2678070201/10000) hx₁ hx₂ (by norm_num) (by norm_num) (by norm_num)
    have hpoly : 64 * (numerator x 500 (101/100) 500 (101/100) 6) = (2612630201/10000) * (20-x)^2 + (2647270201/5000) * (x-12) * (20-x) + (2678070201/10000) * (x-12)^2 := by
      unfold numerator
      ring
    linarith only [h, hpoly]
  · have h : 0 < (6668621397005240401/100000000) * (20-x)^4 + (6705210241515720401/25000000) * (x-12) * (20-x)^3 + (20179567328205321203/50000000) * (x-12)^2 * (20-x)^2 + (6731946519063400401/25000000) * (x-12)^3 * (20-x) + (6720928742500600401/100000000) * (x-12)^4 :=
      @quartic_positive x (6668621397005240401/100000000) (6705210241515720401/25000000) (20179567328205321203/50000000) (6731946519063400401/25000000) (6720928742500600401/100000000) hx₁ hx₂ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hpoly : 4096 * (margin x 500 (101/100) 500 (101/100) 6) = (6668621397005240401/100000000) * (20-x)^4 + (6705210241515720401/25000000) * (x-12) * (20-x)^3 + (20179567328205321203/50000000) * (x-12)^2 * (20-x)^2 + (6731946519063400401/25000000) * (x-12)^3 * (20-x) + (6720928742500600401/100000000) * (x-12)^4 := by
      unfold margin numerator denSq rad
      ring
    linarith only [h, hpoly]

theorem last_at_two (x : ℝ) (hx₁ : 12 ≤ x) (hx₂ : x ≤ 20) :
    0 < numerator x 500 (101/100) (101/100) (101/100) 2 ∧ 0 < margin x 500 (101/100) (101/100) (101/100) 2 := by
  constructor
  · have h : 0 < (62922613/10000) * (20-x)^2 + (81243417/5000) * (x-12) * (20-x) + (98284221/10000) * (x-12)^2 :=
      @quadratic_positive x (62922613/10000) (81243417/5000) (98284221/10000) hx₁ hx₂ (by norm_num) (by norm_num) (by norm_num)
    have hpoly : 64 * (numerator x 500 (101/100) (101/100) (101/100) 2) = (62922613/10000) * (20-x)^2 + (81243417/5000) * (x-12) * (20-x) + (98284221/10000) * (x-12)^2 := by
      unfold numerator
      ring
    linarith only [h, hpoly]
  · have h : 0 < (1249558667424899/50000000) * (20-x)^4 + (1453736215924197/12500000) * (x-12) * (20-x)^3 + (4766343115216149/25000000) * (x-12)^2 * (20-x)^2 + (1587439104788457/12500000) * (x-12)^3 * (20-x) + (1385118784993419/50000000) * (x-12)^4 :=
      @quartic_positive x (1249558667424899/50000000) (1453736215924197/12500000) (4766343115216149/25000000) (1587439104788457/12500000) (1385118784993419/50000000) hx₁ hx₂ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hpoly : 4096 * (margin x 500 (101/100) (101/100) (101/100) 2) = (1249558667424899/50000000) * (20-x)^4 + (1453736215924197/12500000) * (x-12) * (20-x)^3 + (4766343115216149/25000000) * (x-12)^2 * (20-x)^2 + (1587439104788457/12500000) * (x-12)^3 * (20-x) + (1385118784993419/50000000) * (x-12)^4 := by
      unfold margin numerator denSq rad
      ring
    linarith only [h, hpoly]

theorem last_at_six (x : ℝ) (hx₁ : 12 ≤ x) (hx₂ : x ≤ 20) :
    0 < numerator x 500 (101/100) (101/100) (101/100) 6 ∧ margin x 500 (101/100) (101/100) (101/100) 6 < 0 := by
  constructor
  · have h : 0 < (57202613/10000) * (20-x)^2 + (71683417/5000) * (x-12) * (20-x) + (82324221/10000) * (x-12)^2 :=
      @quadratic_positive x (57202613/10000) (71683417/5000) (82324221/10000) hx₁ hx₂ (by norm_num) (by norm_num) (by norm_num)
    have hpoly : 64 * (numerator x 500 (101/100) (101/100) (101/100) 6) = (57202613/10000) * (20-x)^2 + (71683417/5000) * (x-12) * (20-x) + (82324221/10000) * (x-12)^2 := by
      unfold numerator
      ring
    linarith only [h, hpoly]
  · have h : 0 < (124673918015101/50000000) * (20-x)^4 + (569402435115803/12500000) * (x-12) * (20-x)^3 + (4031857912143851/25000000) * (x-12)^2 * (20-x)^2 + (2579889871371543/12500000) * (x-12)^3 * (20-x) + (4379902683646581/50000000) * (x-12)^4 :=
      @quartic_positive x (124673918015101/50000000) (569402435115803/12500000) (4031857912143851/25000000) (2579889871371543/12500000) (4379902683646581/50000000) hx₁ hx₂ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hpoly : 4096 * (- margin x 500 (101/100) (101/100) (101/100) 6) = (124673918015101/50000000) * (20-x)^4 + (569402435115803/12500000) * (x-12) * (20-x)^3 + (4031857912143851/25000000) * (x-12)^2 * (20-x)^2 + (2579889871371543/12500000) * (x-12)^3 * (20-x) + (4379902683646581/50000000) * (x-12)^4 := by
      unfold margin numerator denSq rad
      ring
    linarith only [h, hpoly]

theorem first_at_thirty (x : ℝ) (hx₁ : 12 ≤ x) (hx₂ : x ≤ 20) :
    0 < numerator x (101/100) (3/2) 500 (101/100) 30 ∧ margin x (101/100) (3/2) 500 (101/100) 30 < 0 := by
  constructor
  · have h : 0 < (26143781/5000) * (20-x)^2 + (26764183/2500) * (x-12) * (20-x) + (3556917/1000) * (x-12)^2 :=
      @quadratic_positive x (26143781/5000) (26764183/2500) (3556917/1000) hx₁ hx₂ (by norm_num) (by norm_num) (by norm_num)
    have hpoly : 64 * (numerator x (101/100) (3/2) 500 (101/100) 30) = (26143781/5000) * (20-x)^2 + (26764183/2500) * (x-12) * (20-x) + (3556917/1000) * (x-12)^2 := by
      unfold numerator
      ring
    linarith only [h, hpoly]
  · have h : 0 < (3433234705564127/100000000) * (20-x)^4 + (1508084366653307/5000000) * (x-12) * (20-x)^3 + (41733993321895501/50000000) * (x-12)^2 * (20-x)^2 + (22681999826860023/25000000) * (x-12)^3 * (20-x) + (32515134091151103/100000000) * (x-12)^4 :=
      @quartic_positive x (3433234705564127/100000000) (1508084366653307/5000000) (41733993321895501/50000000) (22681999826860023/25000000) (32515134091151103/100000000) hx₁ hx₂ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hpoly : 4096 * (- margin x (101/100) (3/2) 500 (101/100) 30) = (3433234705564127/100000000) * (20-x)^4 + (1508084366653307/5000000) * (x-12) * (20-x)^3 + (41733993321895501/50000000) * (x-12)^2 * (20-x)^2 + (22681999826860023/25000000) * (x-12)^3 * (20-x) + (32515134091151103/100000000) * (x-12)^4 := by
      unfold margin numerator denSq rad
      ring
    linarith only [h, hpoly]

theorem middle_at_250 (x : ℝ) (hx₁ : 12 ≤ x) (hx₂ : x ≤ 20) :
    0 < numerator x 500 (101/100) 500 (101/100) 250 ∧ margin x 500 (101/100) 500 (101/100) 250 < 0 := by
  constructor
  · have h : 0 < (2263710201/10000) * (20-x)^2 + (2064110201/5000) * (x-12) * (20-x) + (1704510201/10000) * (x-12)^2 :=
      @quadratic_positive x (2263710201/10000) (2064110201/5000) (1704510201/10000) hx₁ hx₂ (by norm_num) (by norm_num) (by norm_num)
    have hpoly : 64 * (numerator x 500 (101/100) 500 (101/100) 250) = (2263710201/10000) * (20-x)^2 + (2064110201/5000) * (x-12) * (20-x) + (1704510201/10000) * (x-12)^2 := by
      unfold numerator
      ring
    linarith only [h, hpoly]
  · have h : 0 < (137189375258119599/100000000) * (20-x)^4 + (2269952795876599599/25000000) * (x-12) * (20-x)^3 + (14353501264911158797/50000000) * (x-12)^2 * (20-x)^2 + (7553167663739479599/25000000) * (x-12)^3 * (20-x) + (10345891162183879599/100000000) * (x-12)^4 :=
      @quartic_positive x (137189375258119599/100000000) (2269952795876599599/25000000) (14353501264911158797/50000000) (7553167663739479599/25000000) (10345891162183879599/100000000) hx₁ hx₂ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hpoly : 4096 * (- margin x 500 (101/100) 500 (101/100) 250) = (137189375258119599/100000000) * (20-x)^4 + (2269952795876599599/25000000) * (x-12) * (20-x)^3 + (14353501264911158797/50000000) * (x-12)^2 * (20-x)^2 + (7553167663739479599/25000000) * (x-12)^3 * (20-x) + (10345891162183879599/100000000) * (x-12)^4 := by
      unfold margin numerator denSq rad
      ring
    linarith only [h, hpoly]


end D5.S3.Geometry.Hyperideal.DoubleStarBernstein
