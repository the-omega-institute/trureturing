/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FourRateSupermodularity
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FourRateSupermodularity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The exact four-rate rational envelope is supermodular on its closed real cube. -/

import Mathlib.Tactic
import Mathlib.Data.Fin.VecNotation

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourRateSupermodularity

def lower : ℝ := 2 / 9
def upper : ℝ := 6 / 25
def threshold : ℝ := 16 / 729
def tailCap : ℝ := 1944 / 390625
def slope : ℝ := 1116529 / 806625
def intercept : ℝ := -151298 / 268875
def seam : ℝ := tailCap / threshold

def ceilingRate (X : Fin 4 → ℝ) : ℝ :=
  min (threshold / (X 1 * X 2)) (tailCap / (X 1 * X 2 * X 3))

def envelope (X : Fin 4 → ℝ) : ℝ :=
  ceilingRate X * (1 + X 1 + X 1 * X 2) -
    slope * ceilingRate X * (1 + X 0) / (ceilingRate X + X 0) - intercept

def H (X : Fin 4 → ℝ) : ℝ := envelope X - X 0 * X 1

def InCube (X : Fin 4 → ℝ) : Prop :=
  ∀ i, lower ≤ X i ∧ X i ≤ upper

private def rationalPart (a b c : ℝ) : ℝ :=
  -slope * (1 + a) / (1 + a * b * c)

set_option maxHeartbeats 2000000 in
-- Clearing four variable denominators requires the expanded rational identity.
private lemma rational_zero_rectangle
    (a A b B c : ℝ)
    (ha : lower ≤ a) (hb : lower ≤ b)
    (haA : a ≤ A) (hbB : b ≤ B) (hc : 9 ≤ c)
    (hcap : A * B * c ≤ 2 / 3) :
    (A - a) * (B - b) ≤ rationalPart a b c + rationalPart A B c -
      rationalPart a B c - rationalPart A b c := by
  have ha0 : 0 < a := by dsimp [lower] at ha; linarith
  have hA0 : 0 < A := lt_of_lt_of_le ha0 haA
  have hb0 : 0 < b := by dsimp [lower] at hb; linarith
  have hB0 : 0 < B := lt_of_lt_of_le hb0 hbB
  have hc0 : 0 < c := by linarith
  have hsmall : a * b * c ≤ A * B * c :=
    mul_le_mul_of_nonneg_right (mul_le_mul haA hbB (le_of_lt hb0) (le_of_lt hA0))
      (le_of_lt hc0)
  have hmid₁ : a * B * c ≤ A * B * c :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right haA (le_of_lt hB0))
      (le_of_lt hc0)
  have hmid₂ : A * b * c ≤ A * B * c :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbB (le_of_lt hA0))
      (le_of_lt hc0)
  have hprod : (A * B * c) * (a * b * c) ≤ (2 / 3 : ℝ) * (2 / 3) :=
    mul_le_mul hcap (le_trans hsmall hcap) (by positivity) (by norm_num)
  let N := 1 + a + A + a * A * c * (b + B) - (A * B * c) * (a * b * c)
  have hN : 1 ≤ N := by
    dsimp [N, lower] at *
    have hp : 0 ≤ a * A * c * (b + B) := by positivity
    nlinarith
  have hp₀ : 0 < 1 + a * b * c := by positivity
  have hp₁ : 0 < 1 + a * B * c := by positivity
  have hp₂ : 0 < 1 + A * b * c := by positivity
  have hp₃ : 0 < 1 + A * B * c := by positivity
  let D := (1 + a * b * c) * (1 + a * B * c) *
    (1 + A * b * c) * (1 + A * B * c)
  have hD0 : 0 < D := by dsimp [D]; positivity
  have hD : D ≤ 8 := by
    have h₀ : 1 + a * b * c ≤ 5 / 3 := by linarith
    have h₁ : 1 + a * B * c ≤ 5 / 3 := by linarith
    have h₂ : 1 + A * b * c ≤ 5 / 3 := by linarith
    have h₃ : 1 + A * B * c ≤ 5 / 3 := by linarith
    have h₄ := mul_le_mul h₀ h₁ (le_of_lt hp₁) (by norm_num : (0 : ℝ) ≤ 5 / 3)
    have h₅ := mul_le_mul h₂ h₃ (le_of_lt hp₃) (by norm_num : (0 : ℝ) ≤ 5 / 3)
    have h₆ := mul_le_mul h₄ h₅ (by positivity)
      (by norm_num : (0 : ℝ) ≤ (5 / 3) * (5 / 3))
    dsimp [D]
    nlinarith
  have hsc : 12 ≤ slope * c := by dsimp [slope]; nlinarith
  have hnum : D ≤ slope * c * N := by
    have hp := mul_le_mul_of_nonneg_left hN (by linarith : 0 ≤ slope * c)
    nlinarith
  have hratio : 1 ≤ slope * c * N / D := (le_div_iff₀ hD0).2 (by simpa using hnum)
  have hdelta : 0 ≤ (A - a) * (B - b) := mul_nonneg (sub_nonneg.mpr haA) (sub_nonneg.mpr hbB)
  calc
    (A - a) * (B - b) ≤ (A - a) * (B - b) * (slope * c * N / D) := by
      simpa using mul_le_mul_of_nonneg_left hratio hdelta
    _ = rationalPart a b c + rationalPart A B c -
        rationalPart a B c - rationalPart A b c := by
      dsimp [rationalPart, N, D]
      field_simp
      <;> ring

private lemma rational_active_rectangle
    (a b B c C d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hbB : b ≤ B) (hcC : c ≤ C) (hd : 0 < d)
    (hcap : a * B * C * d ≤ 2 / 3) :
    0 ≤ rationalPart a (b*c) d + rationalPart a (B*C) d -
      rationalPart a (b*C) d - rationalPart a (B*c) d := by
  have hB : 0 < B := lt_of_lt_of_le hb hbB
  have hC : 0 < C := lt_of_lt_of_le hc hcC
  have hsmall : a * b * c * d ≤ a * B * C * d := by
    have hp := mul_le_mul hbB hcC (le_of_lt hc) (le_of_lt hB)
    have h := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ a * d)
    nlinarith
  have hprod : (a * B * C * d) * (a * b * c * d) ≤ (2 / 3 : ℝ) * (2 / 3) :=
    mul_le_mul hcap (le_trans hsmall hcap) (by positivity) (by norm_num)
  have hN : 0 ≤ 1 - (a * B * C * d) * (a * b * c * d) := by nlinarith
  have hk : 0 < slope := by norm_num [slope]
  have hpos : 0 ≤ slope * (1+a) * a * d * (B-b) * (C-c) *
      (1 - (a * B * C * d) * (a * b * c * d)) /
      ((1+a*b*c*d)*(1+a*b*C*d)*(1+a*B*c*d)*(1+a*B*C*d)) := by
    apply div_nonneg
    · exact mul_nonneg (by positivity) hN
    · positivity
  calc
    0 ≤ slope * (1+a) * a * d * (B-b) * (C-c) *
      (1 - (a * B * C * d) * (a * b * c * d)) /
      ((1+a*b*c*d)*(1+a*b*C*d)*(1+a*B*c*d)*(1+a*B*C*d)) := hpos
    _ = rationalPart a (b*c) d + rationalPart a (B*C) d -
      rationalPart a (b*C) d - rationalPart a (B*c) d := by
      dsimp [rationalPart]
      field_simp
      <;> ring

private lemma reciprocal_rectangle
    (K b B c C d : ℝ) (hK : 0 ≤ K) (hb : 0 < b) (hc : 0 < c)
    (hbB : b ≤ B) (hcC : c ≤ C) (hd : 0 < d) :
    0 ≤ K/(b*c*d) + K/(B*C*d) - K/(b*C*d) - K/(B*c*d) := by
  have hB : 0 < B := lt_of_lt_of_le hb hbB
  have hC : 0 < C := lt_of_lt_of_le hc hcC
  calc
    0 ≤ K * (B-b) * (C-c) / (b*B*c*C*d) := by positivity
    _ = K/(b*c*d) + K/(B*C*d) - K/(b*C*d) - K/(B*c*d) := by
      field_simp
      <;> ring

private lemma coefficient_bounds (b c : ℝ)
    (hb : lower ≤ b ∧ b ≤ upper) (hc : lower ≤ c ∧ c ≤ upper) :
    9 ≤ b*c/tailCap := by
  have hb0 : 0 ≤ b := by norm_num [lower] at hb ⊢; linarith [hb.1]
  have hlo : 0 ≤ lower := by norm_num [lower]
  have h := mul_le_mul hb.1 hc.1 hlo hb0
  norm_num [lower, tailCap] at *
  linarith

private lemma product_cap (a b c d : ℝ)
    (ha : lower ≤ a ∧ a ≤ upper) (hb : lower ≤ b ∧ b ≤ upper)
    (hc : lower ≤ c ∧ c ≤ upper) (hd : lower ≤ d ∧ d ≤ upper) :
    a*b*c*d/tailCap ≤ 2/3 := by
  have hb0 : 0 ≤ b := by dsimp [lower] at hb; linarith [hb.1]
  have hc0 : 0 ≤ c := by dsimp [lower] at hc; linarith [hc.1]
  have hd0 : 0 ≤ d := by dsimp [lower] at hd; linarith [hd.1]
  have hu0 : 0 ≤ upper := by norm_num [upper]
  have hab := mul_le_mul ha.2 hb.2 hb0 hu0
  have hcd := mul_le_mul hc.2 hd.2 hd0 hu0
  have h := mul_le_mul hab hcd (mul_nonneg hc0 hd0) (by positivity)
  norm_num [upper, tailCap] at *
  nlinarith

private def smooth (a b c d : ℝ) : ℝ :=
  tailCap/(b*c*d) + tailCap/(c*d) + tailCap/d -
    slope*(1+a)/(1+a*b*c*d/tailCap) - intercept - a*b


private lemma box_pos {a : ℝ} (ha : lower ≤ a ∧ a ≤ upper) : 0 < a := by
  dsimp [lower] at ha
  linarith [ha.1]

private lemma smooth_rectangle_zero_one (a A b B c d : ℝ)
    (ha : lower ≤ a ∧ a ≤ upper) (hA : lower ≤ A ∧ A ≤ upper)
    (hb : lower ≤ b ∧ b ≤ upper) (hB : lower ≤ B ∧ B ≤ upper)
    (hc : lower ≤ c ∧ c ≤ upper) (hd : lower ≤ d ∧ d ≤ upper)
    (haA : a ≤ A) (hbB : b ≤ B) :
    0 ≤ smooth a b c d + smooth A B c d -
      smooth a B c d - smooth A b c d := by
  have hp := product_cap A B c d hA hB hc hd
  have hcap : A * B * (c*d/tailCap) ≤ 2/3 := by
    convert hp using 1 <;> ring
  have h := rational_zero_rectangle a A b B (c*d/tailCap)
    ha.1 hb.1 haA hbB (coefficient_bounds c d hc hd) hcap
  have hr (x y : ℝ) : rationalPart x y (c*d/tailCap) =
      -slope*(1+x)/(1+x*y*c*d/tailCap) := by
    dsimp [rationalPart]
    congr 1
    ring
  rw [hr a b, hr A B, hr a B, hr A b] at h
  simp only [neg_mul, neg_div] at h
  dsimp [smooth]
  nlinarith


private lemma smooth_rectangle_zero_two (a A b c C d : ℝ)
    (ha : lower ≤ a ∧ a ≤ upper) (hA : lower ≤ A ∧ A ≤ upper)
    (hb : lower ≤ b ∧ b ≤ upper) (hc : lower ≤ c ∧ c ≤ upper)
    (hC : lower ≤ C ∧ C ≤ upper) (hd : lower ≤ d ∧ d ≤ upper)
    (haA : a ≤ A) (hcC : c ≤ C) :
    0 ≤ smooth a b c d + smooth A b C d -
      smooth a b C d - smooth A b c d := by
  have hp := product_cap A b C d hA hb hC hd
  have hcap : A * C * (b*d/tailCap) ≤ 2/3 := by convert hp using 1 <;> ring
  have h := rational_zero_rectangle a A c C (b*d/tailCap)
    ha.1 hc.1 haA hcC (coefficient_bounds b d hb hd) hcap
  have hr (x y : ℝ) : rationalPart x y (b*d/tailCap) =
      -slope*(1+x)/(1+x*b*y*d/tailCap) := by dsimp [rationalPart]; congr 1; ring
  rw [hr a c, hr A C, hr a C, hr A c] at h
  simp only [neg_mul, neg_div] at h
  have hdelta : 0 ≤ (A-a)*(C-c) := by positivity
  dsimp [smooth]
  nlinarith

private lemma smooth_rectangle_zero_three (a A b c d D : ℝ)
    (ha : lower ≤ a ∧ a ≤ upper) (hA : lower ≤ A ∧ A ≤ upper)
    (hb : lower ≤ b ∧ b ≤ upper) (hc : lower ≤ c ∧ c ≤ upper)
    (hd : lower ≤ d ∧ d ≤ upper) (hD : lower ≤ D ∧ D ≤ upper)
    (haA : a ≤ A) (hdD : d ≤ D) :
    0 ≤ smooth a b c d + smooth A b c D -
      smooth a b c D - smooth A b c d := by
  have hp := product_cap A b c D hA hb hc hD
  have hcap : A * D * (b*c/tailCap) ≤ 2/3 := by convert hp using 1 <;> ring
  have h := rational_zero_rectangle a A d D (b*c/tailCap)
    ha.1 hd.1 haA hdD (coefficient_bounds b c hb hc) hcap
  have hr (x y : ℝ) : rationalPart x y (b*c/tailCap) =
      -slope*(1+x)/(1+x*b*c*y/tailCap) := by dsimp [rationalPart]; congr 1; ring
  rw [hr a d, hr A D, hr a D, hr A d] at h
  simp only [neg_mul, neg_div] at h
  have hdelta : 0 ≤ (A-a)*(D-d) := by positivity
  dsimp [smooth]
  nlinarith

private lemma smooth_rectangle_one_two (a b B c C d : ℝ)
    (ha : lower ≤ a ∧ a ≤ upper) (hb : lower ≤ b ∧ b ≤ upper)
    (hB : lower ≤ B ∧ B ≤ upper) (hc : lower ≤ c ∧ c ≤ upper)
    (hC : lower ≤ C ∧ C ≤ upper) (hd : lower ≤ d ∧ d ≤ upper)
    (hbB : b ≤ B) (hcC : c ≤ C) :
    0 ≤ smooth a b c d + smooth a B C d -
      smooth a b C d - smooth a B c d := by
  have hp := product_cap a B C d ha hB hC hd
  have hcap : a * B * C * (d/tailCap) ≤ 2/3 := by convert hp using 1 <;> ring
  have hq : 0 < tailCap := by norm_num [tailCap]
  have h := rational_active_rectangle a b B c C (d/tailCap)
    (box_pos ha) (box_pos hb) (box_pos hc) hbB hcC (div_pos (box_pos hd) hq) hcap
  have hr (x y : ℝ) : rationalPart a (x*y) (d/tailCap) =
      -slope*(1+a)/(1+a*x*y*d/tailCap) := by dsimp [rationalPart]; congr 1; ring
  rw [hr b c, hr B C, hr b C, hr B c] at h
  simp only [neg_mul, neg_div] at h
  have hP := reciprocal_rectangle tailCap b B c C d (le_of_lt hq)
    (box_pos hb) (box_pos hc) hbB hcC (box_pos hd)
  dsimp [smooth]
  nlinarith

private lemma smooth_rectangle_one_three (a b B c d D : ℝ)
    (ha : lower ≤ a ∧ a ≤ upper) (hb : lower ≤ b ∧ b ≤ upper)
    (hB : lower ≤ B ∧ B ≤ upper) (hc : lower ≤ c ∧ c ≤ upper)
    (hd : lower ≤ d ∧ d ≤ upper) (hD : lower ≤ D ∧ D ≤ upper)
    (hbB : b ≤ B) (hdD : d ≤ D) :
    0 ≤ smooth a b c d + smooth a B c D -
      smooth a b c D - smooth a B c d := by
  have hp := product_cap a B c D ha hB hc hD
  have hcap : a * B * D * (c/tailCap) ≤ 2/3 := by convert hp using 1 <;> ring
  have hq : 0 < tailCap := by norm_num [tailCap]
  have h := rational_active_rectangle a b B d D (c/tailCap)
    (box_pos ha) (box_pos hb) (box_pos hd) hbB hdD (div_pos (box_pos hc) hq) hcap
  have hr (x y : ℝ) : rationalPart a (x*y) (c/tailCap) =
      -slope*(1+a)/(1+a*x*c*y/tailCap) := by dsimp [rationalPart]; congr 1; ring
  rw [hr b d, hr B D, hr b D, hr B d] at h
  simp only [neg_mul, neg_div] at h
  have hP := reciprocal_rectangle tailCap b B d D c (le_of_lt hq)
    (box_pos hb) (box_pos hd) hbB hdD (box_pos hc)
  have hdprod (x y : ℝ) : x*y*c = x*c*y := by ring
  simp only [hdprod] at hP
  dsimp [smooth]
  nlinarith

private lemma smooth_rectangle_two_three (a b c C d D : ℝ)
    (ha : lower ≤ a ∧ a ≤ upper) (hb : lower ≤ b ∧ b ≤ upper)
    (hc : lower ≤ c ∧ c ≤ upper) (hC : lower ≤ C ∧ C ≤ upper)
    (hd : lower ≤ d ∧ d ≤ upper) (hD : lower ≤ D ∧ D ≤ upper)
    (hcC : c ≤ C) (hdD : d ≤ D) :
    0 ≤ smooth a b c d + smooth a b C D -
      smooth a b c D - smooth a b C d := by
  have hp := product_cap a b C D ha hb hC hD
  have hcap : a * C * D * (b/tailCap) ≤ 2/3 := by convert hp using 1 <;> ring
  have hq : 0 < tailCap := by norm_num [tailCap]
  have h := rational_active_rectangle a c C d D (b/tailCap)
    (box_pos ha) (box_pos hc) (box_pos hd) hcC hdD (div_pos (box_pos hb) hq) hcap
  have hr (x y : ℝ) : rationalPart a (x*y) (b/tailCap) =
      -slope*(1+a)/(1+a*b*x*y/tailCap) := by dsimp [rationalPart]; congr 1; ring
  rw [hr c d, hr C D, hr c D, hr C d] at h
  simp only [neg_mul, neg_div] at h
  have hP := reciprocal_rectangle tailCap c C d D b (le_of_lt hq)
    (box_pos hc) (box_pos hd) hcC hdD (box_pos hb)
  have hdprod (x y : ℝ) : x*y*b = b*x*y := by ring
  simp only [hdprod] at hP
  have hP' := reciprocal_rectangle tailCap c C d D 1 (le_of_lt hq)
    (box_pos hc) (box_pos hd) hcC hdD (by norm_num)
  simp only [mul_one] at hP'
  dsimp [smooth]
  nlinarith


private lemma cube_inf {X Y : Fin 4 → ℝ} (hX : InCube X) (hY : InCube Y) :
    InCube (X ⊓ Y) := by
  intro i
  exact ⟨le_inf (hX i).1 (hY i).1, le_trans inf_le_left (hX i).2⟩

private lemma cube_sup {X Y : Fin 4 → ℝ} (hX : InCube X) (hY : InCube Y) :
    InCube (X ⊔ Y) := by
  intro i
  exact ⟨le_trans (hX i).1 le_sup_left, sup_le (hX i).2 (hY i).2⟩

private def smoothValue (X : Fin 4 → ℝ) : ℝ := smooth (X 0) (X 1) (X 2) (X 3)

set_option maxHeartbeats 2000000 in
-- The coordinate sorting uses all faces of an arbitrary real rectangle.
private lemma smooth_supermodular (X Y : Fin 4 → ℝ) (hX : InCube X) (hY : InCube Y) :
    smoothValue X + smoothValue Y ≤ smoothValue (X ⊓ Y) + smoothValue (X ⊔ Y) := by
  let a : Fin 4 → ℝ := X ⊓ Y
  let b : Fin 4 → ℝ := X ⊔ Y
  have ha : InCube a := cube_inf hX hY
  have hb : InCube b := cube_sup hX hY
  have hab (i : Fin 4) : a i ≤ b i := le_trans inf_le_left le_sup_left
  have h010 := smooth_rectangle_zero_one (a 0) (b 0) (a 1) (b 1) (a 2) (a 3)
    (ha 0) (hb 0) (ha 1) (hb 1) (ha 2) (ha 3) (hab 0) (hab 1)
  have h011 := smooth_rectangle_zero_one (a 0) (b 0) (a 1) (b 1) (b 2) (a 3)
    (ha 0) (hb 0) (ha 1) (hb 1) (hb 2) (ha 3) (hab 0) (hab 1)
  have h012 := smooth_rectangle_zero_one (a 0) (b 0) (a 1) (b 1) (a 2) (b 3)
    (ha 0) (hb 0) (ha 1) (hb 1) (ha 2) (hb 3) (hab 0) (hab 1)
  have h013 := smooth_rectangle_zero_one (a 0) (b 0) (a 1) (b 1) (b 2) (b 3)
    (ha 0) (hb 0) (ha 1) (hb 1) (hb 2) (hb 3) (hab 0) (hab 1)
  have h020 := smooth_rectangle_zero_two (a 0) (b 0) (a 1) (a 2) (b 2) (a 3)
    (ha 0) (hb 0) (ha 1) (ha 2) (hb 2) (ha 3) (hab 0) (hab 2)
  have h021 := smooth_rectangle_zero_two (a 0) (b 0) (b 1) (a 2) (b 2) (a 3)
    (ha 0) (hb 0) (hb 1) (ha 2) (hb 2) (ha 3) (hab 0) (hab 2)
  have h022 := smooth_rectangle_zero_two (a 0) (b 0) (a 1) (a 2) (b 2) (b 3)
    (ha 0) (hb 0) (ha 1) (ha 2) (hb 2) (hb 3) (hab 0) (hab 2)
  have h023 := smooth_rectangle_zero_two (a 0) (b 0) (b 1) (a 2) (b 2) (b 3)
    (ha 0) (hb 0) (hb 1) (ha 2) (hb 2) (hb 3) (hab 0) (hab 2)
  have h030 := smooth_rectangle_zero_three (a 0) (b 0) (a 1) (a 2) (a 3) (b 3)
    (ha 0) (hb 0) (ha 1) (ha 2) (ha 3) (hb 3) (hab 0) (hab 3)
  have h031 := smooth_rectangle_zero_three (a 0) (b 0) (b 1) (a 2) (a 3) (b 3)
    (ha 0) (hb 0) (hb 1) (ha 2) (ha 3) (hb 3) (hab 0) (hab 3)
  have h032 := smooth_rectangle_zero_three (a 0) (b 0) (a 1) (b 2) (a 3) (b 3)
    (ha 0) (hb 0) (ha 1) (hb 2) (ha 3) (hb 3) (hab 0) (hab 3)
  have h033 := smooth_rectangle_zero_three (a 0) (b 0) (b 1) (b 2) (a 3) (b 3)
    (ha 0) (hb 0) (hb 1) (hb 2) (ha 3) (hb 3) (hab 0) (hab 3)
  have h120 := smooth_rectangle_one_two (a 0) (a 1) (b 1) (a 2) (b 2) (a 3)
    (ha 0) (ha 1) (hb 1) (ha 2) (hb 2) (ha 3) (hab 1) (hab 2)
  have h121 := smooth_rectangle_one_two (b 0) (a 1) (b 1) (a 2) (b 2) (a 3)
    (hb 0) (ha 1) (hb 1) (ha 2) (hb 2) (ha 3) (hab 1) (hab 2)
  have h122 := smooth_rectangle_one_two (a 0) (a 1) (b 1) (a 2) (b 2) (b 3)
    (ha 0) (ha 1) (hb 1) (ha 2) (hb 2) (hb 3) (hab 1) (hab 2)
  have h123 := smooth_rectangle_one_two (b 0) (a 1) (b 1) (a 2) (b 2) (b 3)
    (hb 0) (ha 1) (hb 1) (ha 2) (hb 2) (hb 3) (hab 1) (hab 2)
  have h130 := smooth_rectangle_one_three (a 0) (a 1) (b 1) (a 2) (a 3) (b 3)
    (ha 0) (ha 1) (hb 1) (ha 2) (ha 3) (hb 3) (hab 1) (hab 3)
  have h131 := smooth_rectangle_one_three (b 0) (a 1) (b 1) (a 2) (a 3) (b 3)
    (hb 0) (ha 1) (hb 1) (ha 2) (ha 3) (hb 3) (hab 1) (hab 3)
  have h132 := smooth_rectangle_one_three (a 0) (a 1) (b 1) (b 2) (a 3) (b 3)
    (ha 0) (ha 1) (hb 1) (hb 2) (ha 3) (hb 3) (hab 1) (hab 3)
  have h133 := smooth_rectangle_one_three (b 0) (a 1) (b 1) (b 2) (a 3) (b 3)
    (hb 0) (ha 1) (hb 1) (hb 2) (ha 3) (hb 3) (hab 1) (hab 3)
  have h230 := smooth_rectangle_two_three (a 0) (a 1) (a 2) (b 2) (a 3) (b 3)
    (ha 0) (ha 1) (ha 2) (hb 2) (ha 3) (hb 3) (hab 2) (hab 3)
  have h231 := smooth_rectangle_two_three (b 0) (a 1) (a 2) (b 2) (a 3) (b 3)
    (hb 0) (ha 1) (ha 2) (hb 2) (ha 3) (hb 3) (hab 2) (hab 3)
  have h232 := smooth_rectangle_two_three (a 0) (b 1) (a 2) (b 2) (a 3) (b 3)
    (ha 0) (hb 1) (ha 2) (hb 2) (ha 3) (hb 3) (hab 2) (hab 3)
  have h233 := smooth_rectangle_two_three (b 0) (b 1) (a 2) (b 2) (a 3) (b 3)
    (hb 0) (hb 1) (ha 2) (hb 2) (ha 3) (hb 3) (hab 2) (hab 3)
  dsimp [smoothValue]
  by_cases h0 : X 0 ≤ Y 0 <;> by_cases h1 : X 1 ≤ Y 1 <;>
    by_cases h2 : X 2 ≤ Y 2 <;> by_cases h3 : X 3 ≤ Y 3 <;>
    simp_all only [a, b, Pi.inf_apply, Pi.sup_apply,
      min_def, max_def, ite_true, ite_false] <;> linarith

private def clip (X : Fin 4 → ℝ) : Fin 4 → ℝ :=
  fun i => if i = 3 then max seam (X i) else X i

private lemma cube_clip {X : Fin 4 → ℝ} (hX : InCube X) : InCube (clip X) := by
  have hseam : lower ≤ seam ∧ seam ≤ upper := by norm_num [lower, upper, seam, tailCap, threshold]
  intro i
  by_cases hi : i = 3
  · simp only [clip, hi, if_true]
    exact ⟨le_trans (hX 3).1 (le_max_right _ _), max_le hseam.2 (hX 3).2⟩
  · simpa only [clip, hi, if_false] using hX i

private lemma clip_inf (X Y : Fin 4 → ℝ) : clip (X ⊓ Y) = clip X ⊓ clip Y := by
  funext i
  by_cases hi : i = 3
  · simp only [clip, hi, if_true, Pi.inf_apply]
    exact max_min_distrib_left _ _ _
  · simp only [clip, hi, if_false, Pi.inf_apply]

private lemma clip_sup (X Y : Fin 4 → ℝ) : clip (X ⊔ Y) = clip X ⊔ clip Y := by
  funext i
  by_cases hi : i = 3
  · simp only [clip, hi, if_true, Pi.sup_apply]
    rw [max_max_max_comm, max_self]
  · simp only [clip, hi, if_false, Pi.sup_apply]

private lemma ceiling_rate_clip (X : Fin 4 → ℝ) (hX : InCube X) :
    ceilingRate X = tailCap / (X 1 * X 2 * max seam (X 3)) := by
  have h₁ := box_pos (hX 1)
  have h₂ := box_pos (hX 2)
  have h₃ := box_pos (hX 3)
  have hT : 0 < threshold := by norm_num [threshold]
  have hq : 0 < tailCap := by norm_num [tailCap]
  have hp : 0 < X 1 * X 2 := mul_pos h₁ h₂
  by_cases hd : X 3 ≤ seam
  · have htx : X 3 * threshold ≤ tailCap := (le_div_iff₀ hT).1 hd
    have hcross := mul_le_mul_of_nonneg_left htx (le_of_lt hp)
    have hbranch : threshold / (X 1 * X 2) ≤ tailCap / (X 1 * X 2 * X 3) := by
      apply (div_le_div_iff₀ hp (mul_pos hp h₃)).2
      nlinarith
    rw [ceilingRate, min_eq_left hbranch, max_eq_left hd]
    dsimp [seam]
    field_simp
    <;> ring
  · have hd' : seam ≤ X 3 := le_of_not_ge hd
    have htx : tailCap ≤ X 3 * threshold := (div_le_iff₀ hT).1 hd'
    have hcross := mul_le_mul_of_nonneg_left htx (le_of_lt hp)
    have hbranch : tailCap / (X 1 * X 2 * X 3) ≤ threshold / (X 1 * X 2) := by
      apply (div_le_div_iff₀ (mul_pos hp h₃) hp).2
      nlinarith
    rw [ceilingRate, min_eq_right hbranch, max_eq_right hd']

private lemma H_eq_smooth (X : Fin 4 → ℝ) (hX : InCube X) :
    H X = smoothValue (clip X) := by
  have h₀ := box_pos (hX 0)
  have h₁ := box_pos (hX 1)
  have h₂ := box_pos (hX 2)
  have h₃ := box_pos (hX 3)
  have hd : 0 < max seam (X 3) := lt_of_lt_of_le h₃ (le_max_right _ _)
  have hq : 0 < tailCap := by norm_num [tailCap]
  have hg : 0 < tailCap / (X 1 * X 2 * max seam (X 3)) := by positivity
  have hden : 0 < tailCap / (X 1 * X 2 * max seam (X 3)) + X 0 := by positivity
  rw [H, envelope, ceiling_rate_clip X hX]
  dsimp [smoothValue, smooth, clip]
  norm_num only [Fin.reduceFinMk, Fin.isValue, reduceIte]
  field_simp
  <;> ring

/-- Supermodularity of the exact min-envelope, including its branch seam and closed edges. -/
theorem four_rate_supermodular (X Y : Fin 4 → ℝ) (hX : InCube X) (hY : InCube Y) :
    H X + H Y ≤ H (X ⊓ Y) + H (X ⊔ Y) := by
  rw [H_eq_smooth X hX, H_eq_smooth Y hY,
    H_eq_smooth (X ⊓ Y) (cube_inf hX hY), H_eq_smooth (X ⊔ Y) (cube_sup hX hY),
    clip_inf, clip_sup]
  exact smooth_supermodular (clip X) (clip Y) (cube_clip hX) (cube_clip hY)

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourRateSupermodularity
