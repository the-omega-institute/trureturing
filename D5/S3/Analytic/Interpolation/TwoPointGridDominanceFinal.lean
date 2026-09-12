/- GID: D5/S3/Analytic/Interpolation/TwoPointGridDominanceFinal
   generality: G
   mirror-B: D5/B/S3/Analytic/Interpolation/TwoPointGridDominanceFinal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The two-point grid dual obeys the distance envelope with equality exactly at the diagonal. -/

import D5.S3.Analytic.Interpolation.TwoPointGridDominanceBound
import D5.S3.Analytic.Knapsack.GreedyFillPair

open Set
open scoped BigOperators

noncomputable section

namespace D5.S3.Analytic.Interpolation.TwoPointGridDominanceFinal

open TwoPointGridDominance TwoPointGridDominanceBound
open Knapsack.FractionalKnapsackDual Knapsack.GreedyFillPair

open private gridDistance_nonneg gridDistance_le logValue_strictMono logValue_strictConcave
  from D5.S3.Analytic.Interpolation.TwoPointGridDominanceBound
open private grid_dual_eq_fractional_sup corner_le_grid_dual
  from D5.S3.Analytic.Interpolation.TwoPointGridDominance

theorem psiTwo_strictMono_mean {m n V : ℝ} (hmn : m < n)
    (hL : Real.sqrt (V / 2) < m) : psiTwo m V < psiTwo n V := by
  unfold psiTwo
  apply add_lt_add
  · exact logValue_strictMono (sub_pos.mpr hL)
      (sub_pos.mpr (hL.trans hmn)) (by linarith)
  · have hm : 0 < m + Real.sqrt (V / 2) := by linarith [Real.sqrt_nonneg (V / 2)]
    have hn : 0 < n + Real.sqrt (V / 2) := by linarith [Real.sqrt_nonneg (V / 2)]
    exact logValue_strictMono hm hn (by linarith)

theorem pair_value_spread_strict {m r R : ℝ} (hr : 0 ≤ r) (hrR : r < R) (hRm : R < m) :
    logValue (m - R) + logValue (m + R) < logValue (m - r) + logValue (m + r) := by
  have hR : 0 < R := hr.trans_lt hrR
  let a := (R + r) / (2 * R)
  let b := (R - r) / (2 * R)
  have ha : 0 < a := div_pos (by linarith) (by positivity)
  have hb : 0 < b := div_pos (by linarith) (by positivity)
  have hab : a + b = 1 := by dsimp [a, b]; field_simp; ring
  have hleft : a * (m - R) + b * (m + R) = m - r := by
    dsimp [a, b]; field_simp; ring
  have hright : a * (m + R) + b * (m - R) = m + r := by
    dsimp [a, b]; field_simp; ring
  have hx : m - R ∈ Ioi (0 : ℝ) := sub_pos.mpr hRm
  have hy : m + R ∈ Ioi (0 : ℝ) := by change 0 < m + R; linarith
  have hxy : m - R ≠ m + R := by linarith
  have h1 := logValue_strictConcave.2 hx hy hxy ha hb hab
  have h2 := logValue_strictConcave.2 hy hx hxy.symm ha hb hab
  simp only [smul_eq_mul, hleft, hright] at h1 h2
  have hsum := add_lt_add h1 h2
  have hid : (a * logValue (m - R) + b * logValue (m + R)) +
      (a * logValue (m + R) + b * logValue (m - R)) =
      logValue (m - R) + logValue (m + R) := by
    calc
      _ = (a + b) * (logValue (m - R) + logValue (m + R)) := by ring
      _ = _ := by rw [hab, one_mul]
  rw [hid] at hsum
  exact hsum

theorem fractional_row_bound_strict {c d t u M₀ M₁ θ : ℝ}
    (hc : 0 < c) (hcd : c < d) (ht : 0 < t)
    (hM : M₀ < M₁)
    (htwo : {p : ℝ × ℝ | (p.1 = c ∨ p.1 = d) ∧ (p.2 = t ∨ p.2 = u) ∧
      M₀ ≤ p.1 + p.2 ∧ p.1 + p.2 ≤ M₁}.Nontrivial)
    (hθ : θ ∈ Ioo 0 1) (hbudget : (1 - θ) * c + θ * d + t = M₁) :
    (1 - θ) * logValue c + θ * logValue d + logValue t <
      psiTwo (M₁ / 2) (gridDistance (M₀ / 2) (M₁ / 2) c d ^ 2 +
        gridDistance (M₀ / 2) (M₁ / 2) t u ^ 2) := by
  let m := M₁ / 2
  let a := M₀ / 2
  let z := (1 - θ) * c + θ * d
  let s := z - m
  let v := gridDistance a m c d
  let e := gridDistance a m t u
  have ham : a ≤ m := by dsimp [a, m]; linarith
  have hcz : c < z := by dsimp [z]; nlinarith [hθ.1]
  have hzd : z < d := by dsimp [z]; nlinarith [hθ.2]
  have hzpos : 0 < z := hc.trans hcz
  have htform : t = m - s := by dsimp [m, s, z]; linarith [hbudget]
  have hzform : z = m + s := by dsimp [s]; ring
  have him : m ∈ Icc a m := ⟨ham, le_rfl⟩
  have he : e ≤ |s| := by
    have hh := gridDistance_le (Or.inl (show t = t from Eq.refl t)) him (d := u)
    simpa only [e, htform, sub_sub_cancel_left, abs_neg] using hh
  have hv0 : 0 ≤ v := gridDistance_nonneg _ _ _ _
  have he0 : 0 ≤ e := gridDistance_nonneg _ _ _ _
  have he2 : e ^ 2 ≤ s ^ 2 := by nlinarith [sq_abs s]
  have hsum : (z + t) / 2 = m := by dsimp [m, z]; linarith [hbudget]
  change _ < psiTwo m (v ^ 2 + e ^ 2)
  by_cases hsmall : v ^ 2 + e ^ 2 ≤ 2 * s ^ 2
  · have hj := logValue_strictConcave.2 hc (hc.trans hcd) hcd.ne
      (by linarith [hθ.2] : 0 < 1 - θ) hθ.1 (by ring)
    simp only [smul_eq_mul] at hj
    have hp := pair_bound hzpos ht (V := v ^ 2 + e ^ 2) (by rw [htform, hzform]; nlinarith)
    rw [hsum] at hp
    change _ < logValue z at hj
    linarith
  have hsv : |s| < v := by nlinarith [sq_abs s, abs_nonneg s]
  have hv : 0 < v := (abs_nonneg s).trans_lt hsv
  have hlow := two_actual_corners_lower_mem htwo
    (by dsimp [z] at hcz; linarith [hbudget])
    (by dsimp [z] at hzd; linarith [hbudget])
  have hca : c < a := by
    by_contra hn
    have hac : a ≤ c := le_of_not_gt hn
    by_cases hcm : c ≤ m
    · have hd0 : Metric.infDist c (Icc a m) = 0 := Metric.infDist_zero_of_mem ⟨hac, hcm⟩
      have hh : v ≤ 0 := by dsimp [v, gridDistance]; rw [hd0]; exact min_le_left _ _
      linarith
    · have hh := gridDistance_le (Or.inl (Eq.refl c)) him (d := d)
      rw [abs_of_nonneg (by linarith : 0 ≤ c - m)] at hh
      have hzsm : c - m < s := by dsimp [s]; linarith
      linarith [le_abs_self s]
  have hmd : m < d := by
    by_contra hn
    have hdm : d ≤ m := le_of_not_gt hn
    by_cases had : a ≤ d
    · have hd0 : Metric.infDist d (Icc a m) = 0 := Metric.infDist_zero_of_mem ⟨had, hdm⟩
      have hh : v ≤ 0 := by dsimp [v, gridDistance]; rw [hd0]; exact min_le_right _ _
      linarith
    · have hh := gridDistance_le (Or.inr (Eq.refl d)) (show a ∈ Icc a m from ⟨le_rfl, ham⟩) (c := c)
      rw [abs_of_nonpos (by linarith : d - a ≤ 0)] at hh
      have hzsm : m - d < -s := by dsimp [s]; linarith
      linarith [neg_le_abs s]
  have hvleft : v ≤ a - c := by
    have hh := gridDistance_le (Or.inl (Eq.refl c)) (show a ∈ Icc a m from ⟨le_rfl, ham⟩) (d := d)
    simpa only [abs_of_nonpos (sub_nonpos.mpr hca.le), neg_sub] using hh
  have hvright : v ≤ d - m := by
    simpa only [abs_of_nonneg (sub_nonneg.mpr hmd.le)] using
      gridDistance_le (Or.inr (Eq.refl d)) him (c := c)
  have hcinner : c ≤ m - 2 * v - s := by
    have haa : a ≤ (c + t) / 2 := by dsimp [a]; linarith [hlow.1]
    rw [htform] at haa
    linarith
  have hs := abs_lt.mp hsv
  have hinner := secant_contract hc hcd hcinner
    (by linarith : m - 2 * v - s < m + v) (by linarith : m + v ≤ d)
    (z := z) (θ := θ) (by rw [hzform]; constructor <;> linarith) ⟨hθ.1.le, hθ.2.le⟩ (Eq.refl z)
  have hfrac : (z - (m - 2 * v - s)) / (m + v - (m - 2 * v - s)) =
      2 * (v + s) / (3 * v + s) := by rw [hzform]; congr 1 <;> ring
  rw [hfrac] at hinner
  have hh := inner_secant_bound hv hsv (hc.trans_le hcinner)
  dsimp only at hh
  rw [← htform] at hh
  have hrad : Real.sqrt ((v ^ 2 + e ^ 2) / 2) < v := by
    apply (Real.sqrt_lt' hv).mpr
    nlinarith [sq_abs s]
  have hvm : v < m := by linarith
  exact ((add_le_add hinner (le_refl (logValue t))).trans hh).trans_lt
    (pair_value_spread_strict (Real.sqrt_nonneg _) hrad hvm)

theorem pair_bound_strict {x y V : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hV0 : 0 ≤ V) (hV : V < (x - y) ^ 2 / 2) :
    logValue x + logValue y < psiTwo ((x + y) / 2) V := by
  let m := (x + y) / 2
  let R := |(x - y) / 2|
  have hR : 0 ≤ R := abs_nonneg _
  have hRm : R < m := by
    dsimp [R, m]
    rw [abs_lt]
    constructor <;> linarith
  have hRpos : 0 < R := by
    have hsquare : 0 < R ^ 2 := by
      dsimp [R]
      rw [sq_abs]
      nlinarith
    nlinarith
  have hs : Real.sqrt (V / 2) < R := by
    apply (Real.sqrt_lt' hRpos).mpr
    dsimp [R]
    rw [sq_abs]
    nlinarith
  have hp := pair_value_spread_strict (Real.sqrt_nonneg (V / 2)) hs hRm
  change _ < psiTwo m V at hp
  have he : logValue (m - R) + logValue (m + R) = logValue x + logValue y := by
    dsimp [m, R]
    rcases le_total y x with h | h
    · rw [abs_of_nonneg (by linarith : 0 ≤ (x - y) / 2)]
      have h₁ : (x + y) / 2 - (x - y) / 2 = y := by ring
      have h₂ : (x + y) / 2 + (x - y) / 2 = x := by ring
      rw [h₁, h₂, add_comm]
    · rw [abs_of_nonpos (by linarith : (x - y) / 2 ≤ 0)]
      have h₁ : (x + y) / 2 - -((x - y) / 2) = x := by ring
      have h₂ : (x + y) / 2 + -((x - y) / 2) = y := by ring
      rw [h₁, h₂]
  rw [he] at hp
  exact hp

/-- A point below the upper interval endpoint is strictly closer to the interval. -/
theorem gridDistance_lt_upper {a m c d x : ℝ}
    (hx : x = c ∨ x = d) (ham : a < m) (hxm : x < m) :
    gridDistance a m c d < m - x := by
  have hz : max a x ∈ Icc a m := ⟨le_max_left _ _, max_le ham.le hxm.le⟩
  have hd := gridDistance_le hx hz
  rw [abs_of_nonpos (sub_nonpos.mpr (le_max_right a x)), neg_sub] at hd
  exact hd.trans_lt (sub_lt_sub_right (max_lt ham hxm) x)

/-- Every actual positive pair other than the upper-budget diagonal has a strict gap. -/
theorem actual_pair_bound_strict {c d t u x y M₀ M₁ : ℝ}
    (hx : x = c ∨ x = d) (hy : y = t ∨ y = u)
    (hxpos : 0 < x) (hypos : 0 < y) (hM : M₀ < M₁)
    (hlo : M₀ ≤ x + y) (hhi : x + y ≤ M₁)
    (hne : ¬(x = M₁ / 2 ∧ y = M₁ / 2)) :
    logValue x + logValue y < psiTwo (M₁ / 2)
      (gridDistance (M₀ / 2) (M₁ / 2) c d ^ 2 +
        gridDistance (M₀ / 2) (M₁ / 2) t u ^ 2) := by
  let m := (x + y) / 2
  let V := gridDistance (M₀ / 2) (M₁ / 2) c d ^ 2 +
    gridDistance (M₀ / 2) (M₁ / 2) t u ^ 2
  have hm : m ∈ Icc (M₀ / 2) (M₁ / 2) :=
    ⟨by dsimp [m]; linarith, by dsimp [m]; linarith⟩
  have hxD := gridDistance_le hx hm
  have hyD := gridDistance_le hy hm
  have hxD0 := gridDistance_nonneg (M₀ / 2) (M₁ / 2) c d
  have hyD0 := gridDistance_nonneg (M₀ / 2) (M₁ / 2) t u
  have hx2 : gridDistance (M₀ / 2) (M₁ / 2) c d ^ 2 ≤ (x - m) ^ 2 := by
    nlinarith [sq_abs (x - m)]
  have hy2 : gridDistance (M₀ / 2) (M₁ / 2) t u ^ 2 ≤ (y - m) ^ 2 := by
    nlinarith [sq_abs (y - m)]
  have hV0 : 0 ≤ V := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hV : V ≤ (x - y) ^ 2 / 2 := by dsimp [V, m] at *; nlinarith
  change _ < psiTwo (M₁ / 2) V
  rcases lt_or_eq_of_le hm.2 with hlt | heq
  · have hL : Real.sqrt (V / 2) < m := by
      apply (Real.sqrt_lt' (by dsimp [m]; linarith : 0 < m)).mpr
      dsimp [m]
      nlinarith [mul_pos hxpos hypos]
    exact (pair_bound hxpos hypos hV).trans_lt (psiTwo_strictMono_mean hlt hL)
  · have hxy : x ≠ y := by
      intro h
      apply hne
      dsimp [m] at heq
      constructor <;> linarith
    have ham : M₀ / 2 < M₁ / 2 := by linarith
    have hVlt : V < (x - y) ^ 2 / 2 := by
      rcases lt_or_gt_of_ne hxy with hlt | hgt
      · have hxm : x < M₁ / 2 := by dsimp [m] at heq; linarith
        have hd := gridDistance_lt_upper hx ham hxm
        have hd' : gridDistance (M₀ / 2) (M₁ / 2) c d < m - x := by
          simpa only [heq] using hd
        have hsq : gridDistance (M₀ / 2) (M₁ / 2) c d ^ 2 < (x - m) ^ 2 := by
          nlinarith [mul_pos (sub_pos.mpr hd')
            (show 0 < m - x + gridDistance (M₀ / 2) (M₁ / 2) c d by linarith)]
        dsimp [V, m] at *
        nlinarith
      · have hym : y < M₁ / 2 := by dsimp [m] at heq; linarith
        have hd := gridDistance_lt_upper hy ham hym
        have hd' : gridDistance (M₀ / 2) (M₁ / 2) t u < m - y := by
          simpa only [heq] using hd
        have hsq : gridDistance (M₀ / 2) (M₁ / 2) t u ^ 2 < (y - m) ^ 2 := by
          nlinarith [mul_pos (sub_pos.mpr hd')
            (show 0 < m - y + gridDistance (M₀ / 2) (M₁ / 2) t u by linarith)]
        dsimp [V, m] at *
        nlinarith
    have hp := pair_bound_strict hxpos hypos hV0 hVlt
    change _ < psiTwo m V at hp
    rwa [heq] at hp

#print axioms psiTwo_strictMono_mean
#print axioms pair_value_spread_strict
#print axioms fractional_row_bound_strict

#print axioms pair_bound_strict
#print axioms gridDistance_lt_upper
#print axioms actual_pair_bound_strict

end D5.S3.Analytic.Interpolation.TwoPointGridDominanceFinal
