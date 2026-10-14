/- GID: D5/S3/ArithSums/ThreeCoordinateSlabGap
   generality: G
   mirror-B: D5/B/S3/ArithSums/ThreeCoordinateSlabGap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Three-coordinate distances separate the lower envelope from its resource mean. -/

import D5.S3.ArithSums.TwoPointSlabSupport

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Set
open scoped BigOperators

namespace D5.S3.ArithSums.ThreeCoordinateSlabGap

open TwoPointSlabSupport

/-- The three lower coordinates, with a common translation. -/
def base (T s t : ℝ) : Fin 3 → ℝ := ![T, T + s, T + t]

/-- The total width of the box. -/
def totalWidth (h : Fin 3 → ℝ) : ℝ := h 0 + h 1 + h 2

/-- Squared error bound independent of the common translation and the remote coordinate. -/
def errorBound (S Q : ℝ) : ℝ :=
  ((S + 4 * Q) ^ 2 + (2 * S + 4 * Q) ^ 2 + (S + Q) ^ 2) / 9

/-- Radius computed from the genuine distances to pairs of endpoints. -/
def slabRadius (c h : Fin 3 → ℝ) (M₀ M₁ : ℝ) : ℝ :=
  Real.sqrt ((∑ i, (pairDistance (Icc (M₀ / 3) (M₁ / 3)) (c i) (c i + h i)) ^ 2) / 6)

/-- Lower endpoint of the three-coordinate moment envelope. -/
def slabLower (c h : Fin 3 → ℝ) (M₀ M₁ : ℝ) : ℝ :=
  M₁ / 3 - slabRadius c h M₀ M₁

/-- Mean available to the first two coordinates under a common resource budget. -/
def lowMean (T s q B : ℝ) : ℝ := T + (s + min q B) / 2

/-- The explicitly linearized lower endpoint. -/
def linearLower (T s r q B : ℝ) : ℝ := T + s / 2 + (4 * q - r) / 9 + B / 6

private theorem pair_distance_left (a b c d : ℝ) (hab : a ≤ b)
    (hcd : c ≤ d) (hda : d ≤ a) : pairDistance (Icc a b) c d = a - d := by
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  apply le_antisymm
  · exact (min_le_right _ _).trans (by simpa [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hda)]
      using Metric.infDist_le_dist_of_mem (x := d) ha)
  · apply le_min
    · apply (Metric.le_infDist ⟨a, ha⟩).mpr
      intro y hy
      rw [Real.dist_eq, abs_of_nonpos (by linarith [hy.1])]
      linarith [hy.1]
    · apply (Metric.le_infDist ⟨a, ha⟩).mpr
      intro y hy
      rw [Real.dist_eq, abs_of_nonpos (by linarith [hy.1])]
      linarith [hy.1]

private theorem pair_distance_right (a b c d : ℝ) (hab : a ≤ b)
    (hcd : c ≤ d) (hbc : b ≤ c) : pairDistance (Icc a b) c d = c - b := by
  have hb : b ∈ Icc a b := ⟨hab, le_rfl⟩
  apply le_antisymm
  · exact (min_le_left _ _).trans (by simpa [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hbc)]
      using Metric.infDist_le_dist_of_mem (x := c) hb)
  · apply le_min
    · apply (Metric.le_infDist ⟨b, hb⟩).mpr
      intro y hy
      rw [Real.dist_eq, abs_of_nonneg (by linarith [hy.2])]
      linarith [hy.2]
    · apply (Metric.le_infDist ⟨b, hb⟩).mpr
      intro y hy
      rw [Real.dist_eq, abs_of_nonneg (by linarith [hy.2])]
      linarith [hy.2]

private theorem distance_coordinates (h : Fin 3 → ℝ) (S T s t r q : ℝ)
    (hh : ∀ i, 0 < h i) (hS : 0 ≤ S) (hs : 0 ≤ s) (hsS : s ≤ S)
    (hr : 0 ≤ r) (hrq : r ≤ q) (hq : q ≤ totalWidth h)
    (ht : 2 * S + 3 * totalWidth h ≤ t) :
    (fun i => pairDistance
      (Icc ((3 * T + s + t + r) / 3) ((3 * T + s + t + q) / 3))
      (base T s t i) (base T s t i + h i)) =
      ![(t + s + r) / 3 - h 0, (t + r - 2 * s) / 3 - h 1,
        (2 * t - s - q) / 3] := by
  have h0 := hh 0
  have h1 := hh 1
  have h2 := hh 2
  dsimp [totalWidth] at hq ht
  have hab : (3 * T + s + t + r) / 3 ≤ (3 * T + s + t + q) / 3 := by linarith
  funext i
  fin_cases i
  · change pairDistance _ T (T + h 0) = (t + s + r) / 3 - h 0
    rw [pair_distance_left _ _ _ _ hab (by linarith) (by linarith)]
    ring
  · change pairDistance _ (T + s) (T + s + h 1) = (t + r - 2 * s) / 3 - h 1
    rw [pair_distance_left _ _ _ _ hab (by linarith) (by linarith)]
    ring
  · change pairDistance _ (T + t) (T + t + h 2) = (2 * t - s - q) / 3
    rw [pair_distance_right _ _ _ _ hab (by linarith) (by linarith)]
    ring

private theorem error_coordinates_bound (h : Fin 3 → ℝ) (S s r q : ℝ)
    (hh : ∀ i, 0 < h i) (hS : 0 ≤ S) (hs : 0 ≤ s) (hsS : s ≤ S)
    (hr : 0 ≤ r) (hrq : r ≤ q) (hq : q ≤ totalWidth h) :
    ((s + r) / 3 - h 0) ^ 2 + ((r - 2 * s) / 3 - h 1) ^ 2 +
      ((-s - q) / 3) ^ 2 ≤ errorBound S (totalWidth h) := by
  have h0 := hh 0
  have h1 := hh 1
  have h2 := hh 2
  have hQ : 0 < totalWidth h := by dsimp [totalWidth]; linarith
  have h0Q : h 0 ≤ totalWidth h := by dsimp [totalWidth]; linarith
  have h1Q : h 1 ≤ totalWidth h := by dsimp [totalWidth]; linarith
  have ha : |(s + r) / 3 - h 0| ≤ (S + 4 * totalWidth h) / 3 :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  have hb : |(r - 2 * s) / 3 - h 1| ≤ (2 * S + 4 * totalWidth h) / 3 :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  have hc : |(-s - q) / 3| ≤ (S + totalWidth h) / 3 :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  have ha2 := sq_le_sq₀ (abs_nonneg ((s + r) / 3 - h 0)) (by positivity) |>.mpr ha
  have hb2 := sq_le_sq₀ (abs_nonneg ((r - 2 * s) / 3 - h 1)) (by positivity) |>.mpr hb
  have hc2 := sq_le_sq₀ (abs_nonneg ((-s - q) / 3)) (by positivity) |>.mpr hc
  simp only [sq_abs] at ha2 hb2 hc2
  dsimp [errorBound]
  nlinarith

private theorem radius_remainder (a b c t K : ℝ) (ht : 0 < t)
    (hW : a ^ 2 + b ^ 2 + c ^ 2 ≤ K) (hK : 6 * K ≤ t ^ 2) :
    let ρ := Real.sqrt (((t / 3 + a) ^ 2 + (t / 3 + b) ^ 2 + (2 * t / 3 + c) ^ 2) / 6)
    let z := t / 3 + (a + b + 2 * c) / 6
    0 ≤ ρ - z ∧ ρ - z ≤ K / (2 * t) := by
  dsimp only
  let ρ := Real.sqrt (((t / 3 + a) ^ 2 + (t / 3 + b) ^ 2 + (2 * t / 3 + c) ^ 2) / 6)
  let z := t / 3 + (a + b + 2 * c) / 6
  have hN : 0 ≤ a ^ 2 + b ^ 2 + c ^ 2 := by positivity
  have hP : (a + b + 2 * c) ^ 2 ≤ 6 * (a ^ 2 + b ^ 2 + c ^ 2) := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (2 * a - c), sq_nonneg (2 * b - c)]
  have hp : -t ≤ a + b + 2 * c := by nlinarith
  have hz : t / 6 ≤ z := by dsimp [z]; linarith
  have hr0 : 0 ≤ ρ := Real.sqrt_nonneg _
  have hr2 : ρ ^ 2 = ((t / 3 + a) ^ 2 + (t / 3 + b) ^ 2 +
      (2 * t / 3 + c) ^ 2) / 6 := Real.sq_sqrt (by positivity)
  have hid : ρ ^ 2 - z ^ 2 =
      (a ^ 2 + b ^ 2 + c ^ 2) / 6 - (a + b + 2 * c) ^ 2 / 36 := by
    rw [hr2]; dsimp [z]; ring
  have hzr : z ≤ ρ := by nlinarith
  refine ⟨sub_nonneg.mpr hzr, ?_⟩
  apply (le_div_iff₀ (by positivity : 0 < 2 * t)).mpr
  have hprod := mul_nonneg (sub_nonneg.mpr hzr)
    (show 0 ≤ ρ + z - t / 3 by linarith)
  nlinarith [sq_nonneg (a + b + 2 * c)]

/-- The actual distance endpoint has a uniform, explicitly bounded linearization error. -/
theorem slab_linearization_error (h : Fin 3 → ℝ) (S T s t r q : ℝ)
    (hh : ∀ i, 0 < h i) (hS : 0 ≤ S) (hs : 0 ≤ s) (hsS : s ≤ S)
    (hr : 0 ≤ r) (hrq : r ≤ q) (hq : q ≤ totalWidth h)
    (ht : 2 * S + 3 * totalWidth h ≤ t)
    (htK : Real.sqrt (6 * errorBound S (totalWidth h)) ≤ t) :
    0 ≤ linearLower T s r q (h 0 + h 1) -
      slabLower (base T s t) h (3 * T + s + t + r) (3 * T + s + t + q) ∧
    linearLower T s r q (h 0 + h 1) -
      slabLower (base T s t) h (3 * T + s + t + r) (3 * T + s + t + q) ≤
      errorBound S (totalWidth h) / (2 * t) := by
  have htp : 0 < t := by
    have h0 := hh 0; have h1 := hh 1; have h2 := hh 2
    dsimp [totalWidth] at ht
    linarith
  have hK0 : 0 ≤ errorBound S (totalWidth h) := by unfold errorBound; positivity
  have hKsq := Real.sq_sqrt (show 0 ≤ 6 * errorBound S (totalWidth h) by positivity)
  have hK : 6 * errorBound S (totalWidth h) ≤ t ^ 2 := by
    nlinarith [Real.sqrt_nonneg (6 * errorBound S (totalWidth h))]
  have hw := error_coordinates_bound h S s r q hh hS hs hsS hr hrq hq
  have he := radius_remainder ((s + r) / 3 - h 0) ((r - 2 * s) / 3 - h 1)
    ((-s - q) / 3) t (errorBound S (totalWidth h)) htp hw hK
  have hd := distance_coordinates h S T s t r q hh hS hs hsS hr hrq hq ht
  have hsum := congrArg (fun f : Fin 3 → ℝ => ∑ i, (f i) ^ 2) hd
  dsimp [slabLower, slabRadius]
  rw [hsum]
  simp only [Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.sum_univ_zero, add_zero]
  dsimp only [linearLower] at *
  ring_nf at he ⊢
  exact he

/-- A common actual slab and its two-coordinate resource mean are separated uniformly. -/
theorem saturated_lower_gap (h : Fin 3 → ℝ) (S T s t r q δ : ℝ)
    (hh : ∀ i, 0 < h i) (hS : 0 ≤ S) (hs : 0 ≤ s) (hsS : s ≤ S)
    (hr : 0 ≤ r) (hrq : r ≤ q) (hq : q ≤ totalWidth h)
    (hδ : 0 < δ) (hgap : δ ≤ q - r)
    (ht : 2 * S + 3 * totalWidth h ≤ t)
    (htK : Real.sqrt (6 * errorBound S (totalWidth h)) ≤ t)
    (htδ : 9 * errorBound S (totalWidth h) / δ ≤ t) :
    lowMean T s q (h 0 + h 1) + δ / 18 ≤
      slabLower (base T s t) h (3 * T + s + t + r) (3 * T + s + t + q) := by
  have he := slab_linearization_error h S T s t r q hh hS hs hsS hr hrq hq ht htK
  have htp : 0 < t := by
    have h0 := hh 0; have h1 := hh 1; have h2 := hh 2
    dsimp [totalWidth] at ht
    linarith
  have herror : errorBound S (totalWidth h) / (2 * t) ≤ δ / 18 := by
    have htδ' := (div_le_iff₀ hδ).mp htδ
    apply (div_le_iff₀ (by positivity : 0 < 2 * t)).mpr
    nlinarith
  have hlin : lowMean T s q (h 0 + h 1) + δ / 9 ≤
      linearLower T s r q (h 0 + h 1) := by
    unfold lowMean linearLower
    rcases le_total q (h 0 + h 1) with hqB | hBq
    · rw [min_eq_left hqB]; linarith
    · rw [min_eq_right hBq]; linarith
  linarith [he.2]

end D5.S3.ArithSums.ThreeCoordinateSlabGap
