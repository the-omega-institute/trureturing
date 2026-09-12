/- GID: D5/S3/Analytic/Interpolation/TwoPointGridDominanceBound
   generality: G
   mirror-B: D5/B/S3/Analytic/Interpolation/TwoPointGridDominanceBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fractional grid prices lie below the two-coordinate distance envelope. -/

import D5.S3.Analytic.Interpolation.TwoPointGridDominance

open Set
open scoped BigOperators

noncomputable section

namespace D5.S3.Analytic.Interpolation.TwoPointGridDominanceBound

open TwoPointGridDominance

private theorem gridDistance_nonneg (a b c d : ℝ) : 0 ≤ gridDistance a b c d :=
  le_min Metric.infDist_nonneg Metric.infDist_nonneg

private theorem gridDistance_le {a b c d x m : ℝ}
    (hx : x = c ∨ x = d) (hm : m ∈ Icc a b) :
    gridDistance a b c d ≤ |x - m| := by
  rcases hx with rfl | rfl
  · exact (min_le_left _ _).trans (by
      simpa only [Real.dist_eq] using Metric.infDist_le_dist_of_mem hm (x := x))
  · exact (min_le_right _ _).trans (by
      simpa only [Real.dist_eq] using Metric.infDist_le_dist_of_mem hm (x := x))

private theorem logValue_strictMono : StrictMonoOn logValue (Ioi 0) := by
  intro x hx y hy hxy
  apply Real.log_lt_log
  · exact sub_pos.mpr (by simpa using Real.exp_lt_exp.mpr (neg_neg_of_pos hx))
  · exact sub_lt_sub_left (Real.exp_lt_exp.mpr (neg_lt_neg hxy)) 1

theorem psiTwo_mono_mean {m n V : ℝ} (hmn : m ≤ n)
    (hL : Real.sqrt (V / 2) < m) : psiTwo m V ≤ psiTwo n V := by
  unfold psiTwo
  apply add_le_add
  · exact logValue_strictMono.monotoneOn (sub_pos.mpr hL)
      (sub_pos.mpr (hL.trans_le hmn)) (by linarith)
  · have hm : 0 < m + Real.sqrt (V / 2) := by linarith [Real.sqrt_nonneg (V / 2)]
    have hn : 0 < n + Real.sqrt (V / 2) := by linarith [Real.sqrt_nonneg (V / 2)]
    exact logValue_strictMono.monotoneOn hm hn (by linarith)

private theorem logValue_strictConcave : StrictConcaveOn ℝ (Ioi 0) logValue := by
  have hlog := LogOneSubExpDerivatives.log_one_sub_exp_derivatives
  apply strictConcaveOn_of_deriv2_neg (convex_Ioi 0) hlog.1.continuousOn
  intro x hx
  have hxpos : 0 < x := interior_subset hx
  have hsecond := (hlog.2 x hxpos).2.1
  have he : 0 < Real.exp x - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr hxpos)
  have hneg : -Real.exp x / (Real.exp x - 1) ^ 2 < 0 :=
    div_neg_of_neg_of_pos (neg_neg_of_pos (Real.exp_pos x)) (sq_pos_of_pos he)
  simpa only [logValue, iteratedDeriv_succ, iteratedDeriv_zero,
    Function.iterate_succ_apply, Function.iterate_zero, id_eq] using hsecond.trans_lt hneg

private theorem gridDualValue_translate (c d : Fin 2 → ℝ) (M price : ℝ) :
    gridDualValue c d M price = (∑ i, logValue (c i)) +
      Knapsack.FractionalKnapsackDual.dualValue (fun i => d i - c i)
        (fun i => logValue (d i) - logValue (c i)) (M - ∑ i, c i) price := by
  have hmax (i : Fin 2) :
      max (logValue (c i) - price * c i) (logValue (d i) - price * d i) =
        logValue (c i) - price * c i +
          max 0 (logValue (d i) - logValue (c i) - price * (d i - c i)) := by
    rw [add_max]
    congr 1 <;> ring
  simp only [gridDualValue, hmax, Knapsack.FractionalKnapsackDual.dualValue,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

/-- Subtracting the lower endpoints identifies the grid dual with fractional knapsack. -/
theorem grid_dual_eq_fractional_sup (c d : Fin 2 → ℝ) (M : ℝ)
    (hc : ∀ i, 0 < c i) (hcd : ∀ i, c i < d i) (hM : ∑ i, c i ≤ M) :
    gridDual c d M = (∑ i, logValue (c i)) +
      sSup (Knapsack.FractionalKnapsackDual.objective
        (fun i => logValue (d i) - logValue (c i)) ''
        {a | Knapsack.FractionalKnapsackDual.Feasible (fun i => d i - c i)
          (M - ∑ i, c i) a}) := by
  haveI : Nonempty {p : ℝ // 0 ≤ p} := ⟨⟨0, le_rfl⟩⟩
  have hw (i : Fin 2) : 0 < d i - c i := sub_pos.mpr (hcd i)
  have hv (i : Fin 2) : 0 ≤ logValue (d i) - logValue (c i) :=
    sub_nonneg.mpr (logValue_strictMono (hc i) ((hc i).trans (hcd i)) (hcd i)).le
  have hb : 0 ≤ M - ∑ i, c i := sub_nonneg.mpr hM
  have hbounded : BddBelow (range (fun p : {p : ℝ // 0 ≤ p} =>
      Knapsack.FractionalKnapsackDual.dualValue (fun i => d i - c i)
        (fun i => logValue (d i) - logValue (c i)) (M - ∑ i, c i) p)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨p, rfl⟩
    exact add_nonneg (mul_nonneg p.property hb)
      (Finset.sum_nonneg (fun i _ => le_max_left _ _))
  simp only [gridDual, gridDualValue_translate]
  rw [← add_ciInf hbounded]
  rw [Knapsack.FractionalKnapsackDual.fractional_knapsack_strong_duality
    (fun i => d i - c i) (fun i => logValue (d i) - logValue (c i))
    (M - ∑ i, c i) hw hv hb]

open private hermite_strict_majorant quadratic_derivatives
  from D5.S3.Analytic.Interpolation.HermiteEnvelopeEquality

theorem pair_value_spread {m r R : ℝ} (hr : 0 ≤ r) (hrR : r ≤ R) (hRm : R < m) :
    logValue (m - R) + logValue (m + R) ≤ logValue (m - r) + logValue (m + r) := by
  rcases hrR.eq_or_lt with h | h
  · rw [h]
  have hR : 0 < R := hr.trans_lt h
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
  exact hsum.le

/-- The inner secant and the fixed coordinate have exactly the two-node quadratic moments. -/
theorem inner_secant_quadratic_moments (m v s A B C : ℝ) (hv : 0 < v) (hs : |s| < v) :
    let θ := 2 * (v + s) / (3 * v + s)
    let P := fun x => A + B * (x - (m - v)) + C * (x - (m - v)) ^ 2
    (1 - θ) * P (m - 2 * v - s) + θ * P (m + v) + P (m - s) =
      P (m - v) + P (m + v) := by
  have hs' := abs_lt.mp hs
  have hden : 3 * v + s ≠ 0 := by linarith
  have hden' : v * 3 + s ≠ 0 := by linarith
  dsimp only
  ring_nf
  field_simp [hden, hden']
  <;> ring

theorem inner_secant_bound {m v s : ℝ} (hv : 0 < v) (hs : |s| < v)
    (hc : 0 < m - 2 * v - s) :
    let θ := 2 * (v + s) / (3 * v + s)
    (1 - θ) * logValue (m - 2 * v - s) + θ * logValue (m + v) + logValue (m - s) ≤
      logValue (m - v) + logValue (m + v) := by
  have hs' := abs_lt.mp hs
  let L := m - v
  let H := m + v
  have hL : 0 < L := by dsimp [L]; linarith
  have hLH : L < H := by dsimp [L, H]; linarith
  let C := (logValue H - logValue L - deriv logValue L * (H - L)) / (H - L) ^ 2
  let P := fun x => logValue L + deriv logValue L * (x - L) + C * (x - L) ^ 2
  have hPL : P L = logValue L := by dsimp [P]; ring
  have hPH : P H = logValue H := by
    dsimp [P, C]
    rw [div_mul_cancel₀ _ (pow_ne_zero 2 (sub_ne_zero.mpr hLH.ne'))]
    ring
  have hder := quadratic_derivatives (logValue L) (deriv logValue L) C L
  have hP : ContDiff ℝ 3 P := by dsimp [P]; fun_prop
  have hlog := LogOneSubExpDerivatives.log_one_sub_exp_derivatives
  have hmajor (x : ℝ) (hx : 0 < x) (hxH : x ≤ H) : logValue x ≤ P x := by
    by_cases hxL : x = L
    · simpa [hxL, hPL]
    by_cases hxH' : x = H
    · simpa [hxH', hPH]
    exact (hermite_strict_majorant L H x logValue P hL hLH hx hxH hxL hxH'
      hlog.1 hP hder.2 hPL hder.1 hPH (fun t ht => (hlog.2 t ht).2.2.2)).le
  let θ := 2 * (v + s) / (3 * v + s)
  have hden : 0 < 3 * v + s := by linarith
  have ht0 : 0 ≤ θ := (div_pos (by linarith) hden).le
  have ht1 : θ ≤ 1 := (div_le_one hden).mpr (by linarith)
  have h1 := mul_le_mul_of_nonneg_left
    (hmajor (m - 2 * v - s) hc (by dsimp [H]; linarith)) (sub_nonneg.mpr ht1)
  have h2 := mul_le_mul_of_nonneg_left
    (hmajor (m + v) (by linarith) (by exact le_rfl)) ht0
  have h3 := hmajor (m - s) (by linarith) (by dsimp [H]; linarith)
  have hmoment := inner_secant_quadratic_moments m v s
    (logValue L) (deriv logValue L) C hv hs
  change (1 - θ) * P (m - 2 * v - s) + θ * P (m + v) + P (m - s) = P L + P H at hmoment
  rw [hPL, hPH] at hmoment
  dsimp only
  change (1 - θ) * logValue (m - 2 * v - s) + θ * logValue (m + v) + logValue (m - s) ≤ _
  linarith

theorem pair_bound {x y V : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hV : V ≤ (x - y) ^ 2 / 2) :
    logValue x + logValue y ≤ psiTwo ((x + y) / 2) V := by
  let m := (x + y) / 2
  let R := |(x - y) / 2|
  have hR : 0 ≤ R := abs_nonneg _
  have hRm : R < m := by
    dsimp [R, m]
    rw [abs_lt]
    constructor <;> linarith
  have hs : Real.sqrt (V / 2) ≤ R := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨hR, ?_⟩
    dsimp [R]
    rw [sq_abs]
    nlinarith
  have hp := pair_value_spread (Real.sqrt_nonneg (V / 2)) hs hRm
  change _ ≤ psiTwo m V at hp
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

theorem secant_contract {c d C D z θ : ℝ}
    (hc : 0 < c) (hcd : c < d) (hcC : c ≤ C) (hCD : C < D) (hDd : D ≤ d)
    (hz : z ∈ Icc C D) (hθ : θ ∈ Icc 0 1) (hmean : (1 - θ) * c + θ * d = z) :
    (1 - θ) * logValue c + θ * logValue d ≤
      (1 - (z - C) / (D - C)) * logValue C + (z - C) / (D - C) * logValue D := by
  have hdc : d - c ≠ 0 := sub_ne_zero.mpr hcd.ne'
  have hDC : D - C ≠ 0 := sub_ne_zero.mpr hCD.ne'
  let A := fun x => (1 - (x - c) / (d - c)) * logValue c +
    (x - c) / (d - c) * logValue d
  have hA (x : ℝ) (hx : x ∈ Icc c d) : A x ≤ logValue x := by
    have ht0 : 0 ≤ (x - c) / (d - c) := div_nonneg (by linarith [hx.1]) (by linarith)
    have ht1 : (x - c) / (d - c) ≤ 1 := (div_le_one (sub_pos.mpr hcd)).mpr (by linarith [hx.2])
    have he : (1 - (x - c) / (d - c)) * c + (x - c) / (d - c) * d = x := by
      field_simp [hdc, hDC]
      <;> ring
    have hh := logValue_strictConcave.concaveOn.2 hc (hc.trans hcd)
      (sub_nonneg.mpr ht1) ht0 (by ring)
    simpa only [smul_eq_mul, he] using hh
  have hden : 0 < D - C := sub_pos.mpr hCD
  have ht0 : 0 ≤ (z - C) / (D - C) := div_nonneg (by linarith [hz.1]) hden.le
  have ht1 : (z - C) / (D - C) ≤ 1 := (div_le_one hden).mpr (by linarith [hz.2])
  have h₁ := mul_le_mul_of_nonneg_left (hA C ⟨hcC, hCD.le.trans hDd⟩) (sub_nonneg.mpr ht1)
  have h₂ := mul_le_mul_of_nonneg_left (hA D ⟨hcC.trans hCD.le, hDd⟩) ht0
  have he : (1 - (z - C) / (D - C)) * A C + (z - C) / (D - C) * A D =
      (1 - θ) * logValue c + θ * logValue d := by
    dsimp [A]
    rw [← hmean]
    field_simp [hdc, hDC]
    <;> ring
  linarith

theorem fractional_row_bound {c d t u M₀ M₁ θ : ℝ}
    (hc : 0 < c) (hcd : c < d) (ht : 0 < t)
    (hM : M₀ < M₁)
    (htwo : {p : ℝ × ℝ | (p.1 = c ∨ p.1 = d) ∧ (p.2 = t ∨ p.2 = u) ∧
      M₀ ≤ p.1 + p.2 ∧ p.1 + p.2 ≤ M₁}.Nontrivial)
    (hθ : θ ∈ Ioo 0 1) (hbudget : (1 - θ) * c + θ * d + t = M₁) :
    (1 - θ) * logValue c + θ * logValue d + logValue t ≤
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
  change _ ≤ psiTwo m (v ^ 2 + e ^ 2)
  by_cases hsmall : v ^ 2 + e ^ 2 ≤ 2 * s ^ 2
  · have hj := logValue_strictConcave.concaveOn.2 hc (hc.trans hcd)
      (by linarith [hθ.2] : 0 ≤ 1 - θ) hθ.1.le (by ring)
    simp only [smul_eq_mul] at hj
    have hp := pair_bound hzpos ht (V := v ^ 2 + e ^ 2) (by rw [htform, hzform]; nlinarith)
    rw [hsum] at hp
    exact (add_le_add hj (le_refl (logValue t))).trans hp
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
  have hrad : Real.sqrt ((v ^ 2 + e ^ 2) / 2) ≤ v := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨hv.le, by nlinarith [sq_abs s]⟩
  have hvm : v < m := by linarith
  exact ((add_le_add hinner (le_refl (logValue t))).trans hh).trans
    (pair_value_spread (Real.sqrt_nonneg _) hrad hvm)

theorem actual_pair_bound {c d t u x y M₀ M₁ : ℝ}
    (hx : x = c ∨ x = d) (hy : y = t ∨ y = u)
    (hxpos : 0 < x) (hypos : 0 < y) (hlo : M₀ ≤ x + y) (hhi : x + y ≤ M₁) :
    logValue x + logValue y ≤ psiTwo (M₁ / 2)
      (gridDistance (M₀ / 2) (M₁ / 2) c d ^ 2 +
        gridDistance (M₀ / 2) (M₁ / 2) t u ^ 2) := by
  let m := (x + y) / 2
  let V := gridDistance (M₀ / 2) (M₁ / 2) c d ^ 2 +
    gridDistance (M₀ / 2) (M₁ / 2) t u ^ 2
  have hm : m ∈ Icc (M₀ / 2) (M₁ / 2) :=
    ⟨by dsimp [m]; linarith, by dsimp [m]; linarith⟩
  have hxD := gridDistance_le hx hm
  have hyD := gridDistance_le hy hm
  have hx2 : gridDistance (M₀ / 2) (M₁ / 2) c d ^ 2 ≤ (x - m) ^ 2 := by
    nlinarith [sq_abs (x - m), gridDistance_nonneg (M₀ / 2) (M₁ / 2) c d]
  have hy2 : gridDistance (M₀ / 2) (M₁ / 2) t u ^ 2 ≤ (y - m) ^ 2 := by
    nlinarith [sq_abs (y - m), gridDistance_nonneg (M₀ / 2) (M₁ / 2) t u]
  have hV : V ≤ (x - y) ^ 2 / 2 := by dsimp [V, m] at *; nlinarith
  have hL : Real.sqrt (V / 2) < m := by
    apply (Real.sqrt_lt' (by dsimp [m]; linarith : 0 < m)).mpr
    dsimp [m]
    nlinarith [mul_pos hxpos hypos]
  exact (pair_bound hxpos hypos hV).trans (psiTwo_mono_mean hm.2 hL)

private theorem closed_row_bound {c d t u M₀ M₁ θ : ℝ}
    (hc : 0 < c) (hcd : c < d) (ht : 0 < t) (hM : M₀ < M₁)
    (htwo : {p : ℝ × ℝ | (p.1 = c ∨ p.1 = d) ∧ (p.2 = t ∨ p.2 = u) ∧
      M₀ ≤ p.1 + p.2 ∧ p.1 + p.2 ≤ M₁}.Nontrivial)
    (hθ : θ ∈ Icc 0 1) (hbudget : (1 - θ) * c + θ * d + t = M₁) :
    (1 - θ) * logValue c + θ * logValue d + logValue t ≤
      psiTwo (M₁ / 2) (gridDistance (M₀ / 2) (M₁ / 2) c d ^ 2 +
        gridDistance (M₀ / 2) (M₁ / 2) t u ^ 2) := by
  rcases hθ.1.eq_or_lt with hzero | hpos
  · have hz : θ = 0 := hzero.symm
    simp only [hz, sub_zero, one_mul, zero_mul, add_zero] at hbudget ⊢
    exact actual_pair_bound (Or.inl (Eq.refl c)) (Or.inl (Eq.refl t)) hc ht
      (by linarith) hbudget.le
  rcases hθ.2.eq_or_lt with hone | hlt
  · simp only [hone, sub_self, zero_mul, one_mul, zero_add] at hbudget ⊢
    exact actual_pair_bound (Or.inr (Eq.refl d)) (Or.inl (Eq.refl t)) (hc.trans hcd) ht
      (by linarith) hbudget.le
  exact fractional_row_bound hc hcd ht hM htwo ⟨hpos, hlt⟩ hbudget

theorem ordered_fill_bound {c d t u M₀ M₁ : ℝ}
    (hc : 0 < c) (hcd : c < d) (ht : 0 < t) (htu : t < u) (hM : M₀ < M₁)
    (hbase : c + t ≤ M₁)
    (htwo : {p : ℝ × ℝ | (p.1 = c ∨ p.1 = d) ∧ (p.2 = t ∨ p.2 = u) ∧
      M₀ ≤ p.1 + p.2 ∧ p.1 + p.2 ≤ M₁}.Nontrivial) :
    logValue c + logValue t + Knapsack.FractionalKnapsackDual.objective
      ![logValue d - logValue c, logValue u - logValue t]
      (Knapsack.FractionalKnapsackDual.greedyFill ![d - c, u - t] [0, 1]
        (M₁ - c - t)) ≤ psiTwo (M₁ / 2)
          (gridDistance (M₀ / 2) (M₁ / 2) c d ^ 2 +
            gridDistance (M₀ / 2) (M₁ / 2) t u ^ 2) := by
  have hswap : {p : ℝ × ℝ | (p.1 = t ∨ p.1 = u) ∧ (p.2 = d ∨ p.2 = c) ∧
      M₀ ≤ p.1 + p.2 ∧ p.1 + p.2 ≤ M₁}.Nontrivial := by
    obtain ⟨⟨x, y⟩, hx, ⟨z, w⟩, hz, hne⟩ := htwo
    refine ⟨(y, x), ?_, (w, z), ?_, ?_⟩
    · exact ⟨hx.2.1, hx.1.symm, by linarith [hx.2.2.1], by linarith [hx.2.2.2]⟩
    · exact ⟨hz.2.1, hz.1.symm, by linarith [hz.2.2.1], by linarith [hz.2.2.2]⟩
    · intro he
      apply hne
      have hp := Prod.mk.inj he
      exact Prod.ext hp.2 hp.1
  by_cases hfirst : d - c ≤ M₁ - c - t
  · by_cases hsecond : u - t ≤ M₁ - c - t - (d - c)
    · obtain ⟨⟨x, y⟩, hx, _, _, _⟩ := htwo
      have hxle : x ≤ d := hx.1.elim (fun h => h.le.trans hcd.le) (fun h => h.le)
      have hyle : y ≤ u := hx.2.1.elim (fun h => h.le.trans htu.le) (fun h => h.le)
      have hh := actual_pair_bound (c := c) (d := d) (t := t) (u := u)
        (Or.inr (Eq.refl d)) (Or.inr (Eq.refl u))
        (hc.trans hcd) (ht.trans htu) (M₀ := M₀) (M₁ := M₁)
        (by linarith [hx.2.2.1]) (by linarith)
      convert hh using 1 <;>
        simp [Knapsack.FractionalKnapsackDual.objective,
          Knapsack.FractionalKnapsackDual.greedyFill, Fin.sum_univ_two, hfirst, hsecond] <;> ring
    · have hθ : (M₁ - c - t - (d - c)) / (u - t) ∈ Icc (0 : ℝ) 1 := by
        exact ⟨div_nonneg (by linarith) (sub_pos.mpr htu).le,
          (div_le_one (sub_pos.mpr htu)).mpr (by linarith)⟩
      have hb : (1 - (M₁ - c - t - (d - c)) / (u - t)) * t +
          (M₁ - c - t - (d - c)) / (u - t) * u + d = M₁ := by
        field_simp [sub_ne_zero.mpr htu.ne']
        <;> ring
      have hh := closed_row_bound ht htu (hc.trans hcd) hM hswap hθ hb
      have hdist : gridDistance (M₀ / 2) (M₁ / 2) d c =
          gridDistance (M₀ / 2) (M₁ / 2) c d := min_comm _ _
      rw [hdist, add_comm (_ ^ 2) (_ ^ 2)] at hh
      convert hh using 1 <;>
        simp [Knapsack.FractionalKnapsackDual.objective,
          Knapsack.FractionalKnapsackDual.greedyFill, Fin.sum_univ_two, hfirst, hsecond] <;> ring
  · have hθ : (M₁ - c - t) / (d - c) ∈ Icc (0 : ℝ) 1 := by
      exact ⟨div_nonneg (by linarith) (sub_pos.mpr hcd).le,
        (div_le_one (sub_pos.mpr hcd)).mpr (by linarith)⟩
    have hb : (1 - (M₁ - c - t) / (d - c)) * c + (M₁ - c - t) / (d - c) * d + t = M₁ := by
      field_simp [sub_ne_zero.mpr hcd.ne']
      <;> ring
    have hh := closed_row_bound hc hcd ht hM htwo hθ hb
    convert hh using 1 <;>
      simp [Knapsack.FractionalKnapsackDual.objective,
        Knapsack.FractionalKnapsackDual.greedyFill, Fin.sum_univ_two, hfirst] <;> ring

/-- The fractional price optimum is bounded by the envelope of the grid distances. -/
theorem two_point_grid_dominance (c d : Fin 2 → ℝ) (M₀ M₁ : ℝ)
    (hc : ∀ i, 0 < c i) (hcd : ∀ i, c i < d i) (hM : M₀ < M₁)
    (htwo : (corners c d M₀ M₁).Nontrivial) :
    gridDual c d M₁ ≤ psiTwo (M₁ / 2) (varianceFloor c d M₀ M₁) := by
  have hbase : (∑ i, c i) ≤ M₁ := by
    obtain ⟨⟨x, y⟩, hx, _, _, _⟩ := htwo
    have hcx : c 0 ≤ x := hx.1.elim (fun h => h.ge) (fun h => (hcd 0).le.trans h.ge)
    have hcy : c 1 ≤ y := hx.2.1.elim (fun h => h.ge) (fun h => (hcd 1).le.trans h.ge)
    simp only [Fin.sum_univ_two]
    linarith [hx.2.2.2]
  let w := fun i => d i - c i
  let v := fun i => logValue (d i) - logValue (c i)
  let B := M₁ - ∑ i, c i
  obtain ⟨l, p, hn, hcover, _, _, _, _, _, _, hsup, _⟩ :=
    Knapsack.FractionalKnapsackDual.greedy_attains_duality w v B
      (fun i => sub_pos.mpr (hcd i))
      (fun i => sub_nonneg.mpr
        (logValue_strictMono (hc i) ((hc i).trans (hcd i)) (hcd i)).le)
      (sub_nonneg.mpr hbase)
  rw [grid_dual_eq_fractional_sup c d M₁ hc hcd hbase, hsup]
  have hlen : l.length = 2 := by
    rw [← List.toFinset_card_of_nodup hn, hcover]
    simp
  obtain ⟨i, j, rfl⟩ := List.length_eq_two.mp hlen
  have hne : i ≠ j := by simpa using hn
  have hh := ordered_fill_bound (hc 0) (hcd 0) (hc 1) (hcd 1) hM
    (by simpa only [Fin.sum_univ_two] using hbase) htwo
  have hswap : {p : ℝ × ℝ | (p.1 = c 1 ∨ p.1 = d 1) ∧ (p.2 = c 0 ∨ p.2 = d 0) ∧
      M₀ ≤ p.1 + p.2 ∧ p.1 + p.2 ≤ M₁}.Nontrivial := by
    obtain ⟨⟨x, y⟩, hx, ⟨z, q⟩, hz, hne⟩ := htwo
    refine ⟨(y, x), ?_, (q, z), ?_, ?_⟩
    · exact ⟨hx.2.1, hx.1, by linarith [hx.2.2.1], by linarith [hx.2.2.2]⟩
    · exact ⟨hz.2.1, hz.1, by linarith [hz.2.2.1], by linarith [hz.2.2.2]⟩
    · intro he
      apply hne
      have hp := Prod.mk.inj he
      exact Prod.ext hp.2 hp.1
  have hh' := ordered_fill_bound (hc 1) (hcd 1) (hc 0) (hcd 0) hM
    (by simpa only [Fin.sum_univ_two, add_comm] using hbase) hswap
  have hB₀ : B = M₁ - c 0 - c 1 := by dsimp [B]; rw [Fin.sum_univ_two]; ring
  have hB₁ : M₁ - c 1 - c 0 = B := by rw [hB₀]; ring
  fin_cases i <;> fin_cases j
  · exact (hne (Eq.refl _)).elim
  · have hw : w = ![d 0 - c 0, d 1 - c 1] := by funext i; fin_cases i <;> simp [w]
    have hv : v = ![logValue (d 0) - logValue (c 0), logValue (d 1) - logValue (c 1)] := by
      funext i; fin_cases i <;> simp [v]
    convert hh using 1 <;>
      simp [hw, hv, hB₀, varianceFloor, Fin.sum_univ_two,
        Knapsack.FractionalKnapsackDual.objective,
        Knapsack.FractionalKnapsackDual.greedyFill, sub_le_iff_le_add]
    have hguard : (d 0 ≤ M₁ - c 0 - c 1 + c 0) ↔
        (d 0 - c 0 ≤ M₁ - c 0 - c 1) := by
      constructor <;> intro <;> linarith
    simp only [hguard]
  · rw [hB₁] at hh'
    by_cases hfirst : d 1 - c 1 ≤ B <;>
      by_cases hsecond : d 0 - c 0 ≤ B - (d 1 - c 1) <;>
      convert hh' using 1 <;>
      simp [Knapsack.FractionalKnapsackDual.objective,
        Knapsack.FractionalKnapsackDual.greedyFill, Fin.sum_univ_two,
        w, v, varianceFloor, hfirst, hsecond, add_comm] <;> ring
  · exact (hne (Eq.refl _)).elim

#print axioms psiTwo_mono_mean
#print axioms pair_value_spread
#print axioms inner_secant_quadratic_moments
#print axioms inner_secant_bound
#print axioms pair_bound
#print axioms secant_contract
#print axioms fractional_row_bound
#print axioms actual_pair_bound
#print axioms ordered_fill_bound
#print axioms two_point_grid_dominance

end D5.S3.Analytic.Interpolation.TwoPointGridDominanceBound
