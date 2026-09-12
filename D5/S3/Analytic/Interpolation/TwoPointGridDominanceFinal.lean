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

/-- A decreasing-density pair bounds the exact grid dual. -/
theorem grid_dual_le_greedy_pair (c d : Fin 2 → ℝ) (M : ℝ)
    (hc : ∀ i, 0 < c i) (hcd : ∀ i, c i < d i) (hbase : c 0 + c 1 ≤ M)
    (hratio : (logValue (d 1) - logValue (c 1)) / (d 1 - c 1) ≤
      (logValue (d 0) - logValue (c 0)) / (d 0 - c 0)) :
    gridDual c d M ≤ logValue (c 0) + logValue (c 1) +
      objective (fun i => logValue (d i) - logValue (c i))
        (greedyFill (fun i => d i - c i) [0, 1] (M - c 0 - c 1)) := by
  let w := fun i => d i - c i
  let v := fun i => logValue (d i) - logValue (c i)
  let B := M - c 0 - c 1
  have hw (i : Fin 2) : 0 < w i := sub_pos.mpr (hcd i)
  have hv (i : Fin 2) : 0 ≤ v i :=
    sub_nonneg.mpr (logValue_strictMono (hc i) ((hc i).trans (hcd i)) (hcd i)).le
  have hB : 0 ≤ B := by dsimp [B]; linarith
  obtain ⟨l, price, hnodup, hcover, _, _, _, _, _, _, hsup, _⟩ :=
    greedy_attains_duality w v B hw hv hB
  have hl : l = [0, 1] ∨ l = [1, 0] := by
    apply List.perm_pair.mp
    apply List.perm_of_nodup_nodup_toFinset_eq hnodup (by simp)
    rw [hcover]
    ext i
    fin_cases i <;> simp
  have heq := grid_dual_eq_fractional_sup c d M hc hcd
    (by simpa only [Fin.sum_univ_two] using hbase)
  have hbudget : M - ∑ i, c i = B := by simp [B, Fin.sum_univ_two]; ring
  rw [hbudget] at heq
  change gridDual c d M = (∑ i, logValue (c i)) +
    sSup (objective v '' {a | Feasible w B a}) at heq
  rw [hsup, Fin.sum_univ_two] at heq
  rw [heq]
  suffices ho : objective v (greedyFill w l B) ≤ objective v (greedyFill w [0, 1] B) by
    exact add_le_add le_rfl ho
  rcases hl with hl | hl
  · rw [hl]
  · rw [hl]
    exact greedyFill_pair_swap w v 0 1 (by decide) B (hw 0) (hw 1) hB hratio

/-- The actual-corner condition is preserved when the two coordinates are exchanged. -/
theorem corners_swap_nontrivial (c d : Fin 2 → ℝ) (M₀ M₁ : ℝ)
    (htwo : (corners c d M₀ M₁).Nontrivial) :
    (corners ![c 1, c 0] ![d 1, d 0] M₀ M₁).Nontrivial := by
  obtain ⟨⟨x, y⟩, hx, ⟨z, w⟩, hz, hne⟩ := htwo
  refine ⟨(y, x), ?_, (w, z), ?_, ?_⟩
  · exact ⟨hx.2.1, hx.1, by linarith [hx.2.2.1], by linarith [hx.2.2.2]⟩
  · exact ⟨hz.2.1, hz.1, by linarith [hz.2.2.1], by linarith [hz.2.2.2]⟩
  · intro he
    apply hne
    have hp := Prod.mk.inj he
    exact Prod.ext hp.2 hp.1

/-- Exchanging the two coordinate labels leaves the grid dual unchanged. -/
theorem grid_dual_swap (c d : Fin 2 → ℝ) (M : ℝ) :
    gridDual ![c 1, c 0] ![d 1, d 0] M = gridDual c d M := by
  apply congrArg sInf
  congr 1
  funext p
  simp only [gridDualValue, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  ring

/-- Every positive two-point grid with two actual slab corners obeys the distance envelope. -/
theorem two_point_grid_dominance (c d : Fin 2 → ℝ) (M₀ M₁ : ℝ)
    (hc : ∀ i, 0 < c i) (hcd : ∀ i, c i < d i) (hM : M₀ < M₁)
    (htwo : (corners c d M₀ M₁).Nontrivial) :
    gridDual c d M₁ ≤ psiTwo (M₁ / 2) (varianceFloor c d M₀ M₁) := by
  have hbase : c 0 + c 1 ≤ M₁ := by
    obtain ⟨⟨x, y⟩, hx⟩ := htwo.nonempty
    have hx0 : c 0 ≤ x := hx.1.elim (fun h => h.ge) (fun h => (hcd 0).le.trans h.ge)
    have hy0 : c 1 ≤ y := hx.2.1.elim (fun h => h.ge) (fun h => (hcd 1).le.trans h.ge)
    linarith [hx.2.2.2]
  have hordered (c d : Fin 2 → ℝ) (hc : ∀ i, 0 < c i) (hcd : ∀ i, c i < d i)
      (hb : c 0 + c 1 ≤ M₁) (ht : (corners c d M₀ M₁).Nontrivial)
      (hr : (logValue (d 1) - logValue (c 1)) / (d 1 - c 1) ≤
        (logValue (d 0) - logValue (c 0)) / (d 0 - c 0)) :
      gridDual c d M₁ ≤ psiTwo (M₁ / 2) (varianceFloor c d M₀ M₁) := by
    have hg := grid_dual_le_greedy_pair c d M₁ hc hcd hb hr
    have ha := ordered_fill_bound (hc 0) (hcd 0) (hc 1) (hcd 1) hM hb ht
    have hw : (fun i => d i - c i) = ![d 0 - c 0, d 1 - c 1] := by
      funext i; fin_cases i <;> simp
    have hv : (fun i => logValue (d i) - logValue (c i)) =
        ![logValue (d 0) - logValue (c 0), logValue (d 1) - logValue (c 1)] := by
      funext i; fin_cases i <;> simp
    rw [hw, hv] at hg
    exact hg.trans (by simpa only [varianceFloor, Fin.sum_univ_two] using ha)
  rcases le_total
      ((logValue (d 1) - logValue (c 1)) / (d 1 - c 1))
      ((logValue (d 0) - logValue (c 0)) / (d 0 - c 0)) with hr | hr
  · exact hordered c d hc hcd hbase htwo hr
  · have hs := hordered ![c 1, c 0] ![d 1, d 0]
      (by intro i; fin_cases i <;> simp [hc])
      (by intro i; fin_cases i <;> simp [hcd])
      (by simpa [add_comm] using hbase) (corners_swap_nontrivial c d M₀ M₁ htwo) hr
    rw [grid_dual_swap] at hs
    simpa [varianceFloor, Fin.sum_univ_two, add_comm] using hs

theorem closed_row_bound_strict {c d t u M₀ M₁ θ : ℝ}
    (hc : 0 < c) (hcd : c < d) (ht : 0 < t) (hM : M₀ < M₁)
    (htwo : {p : ℝ × ℝ | (p.1 = c ∨ p.1 = d) ∧ (p.2 = t ∨ p.2 = u) ∧
      M₀ ≤ p.1 + p.2 ∧ p.1 + p.2 ≤ M₁}.Nontrivial)
    (hθ : θ ∈ Icc 0 1) (hbudget : (1 - θ) * c + θ * d + t = M₁)
    (hdiag : ¬((M₁ / 2 = c ∨ M₁ / 2 = d) ∧ (M₁ / 2 = t ∨ M₁ / 2 = u))) :
    (1 - θ) * logValue c + θ * logValue d + logValue t <
      psiTwo (M₁ / 2) (gridDistance (M₀ / 2) (M₁ / 2) c d ^ 2 +
        gridDistance (M₀ / 2) (M₁ / 2) t u ^ 2) := by
  rcases hθ.1.eq_or_lt with hzero | hpos
  · have hz : θ = 0 := hzero.symm
    simp only [hz, sub_zero, one_mul, zero_mul, add_zero] at hbudget ⊢
    apply actual_pair_bound_strict (Or.inl (Eq.refl c)) (Or.inl (Eq.refl t)) hc ht hM
      (by linarith) hbudget.le
    rintro ⟨h1, h2⟩
    exact hdiag ⟨Or.inl h1.symm, Or.inl h2.symm⟩
  rcases hθ.2.eq_or_lt with hone | hlt
  · simp only [hone, sub_self, zero_mul, one_mul, zero_add] at hbudget ⊢
    apply actual_pair_bound_strict (Or.inr (Eq.refl d)) (Or.inl (Eq.refl t)) (hc.trans hcd) ht hM
      (by linarith) hbudget.le
    rintro ⟨h1, h2⟩
    exact hdiag ⟨Or.inr h1.symm, Or.inl h2.symm⟩
  exact fractional_row_bound_strict hc hcd ht hM htwo ⟨hpos, hlt⟩ hbudget

theorem ordered_fill_bound_strict {c d t u M₀ M₁ : ℝ}
    (hc : 0 < c) (hcd : c < d) (ht : 0 < t) (htu : t < u) (hM : M₀ < M₁)
    (hbase : c + t ≤ M₁)
    (htwo : {p : ℝ × ℝ | (p.1 = c ∨ p.1 = d) ∧ (p.2 = t ∨ p.2 = u) ∧
      M₀ ≤ p.1 + p.2 ∧ p.1 + p.2 ≤ M₁}.Nontrivial)
    (hdiag : ¬((M₁ / 2 = c ∨ M₁ / 2 = d) ∧ (M₁ / 2 = t ∨ M₁ / 2 = u))) :
    logValue c + logValue t + Knapsack.FractionalKnapsackDual.objective
      ![logValue d - logValue c, logValue u - logValue t]
      (Knapsack.FractionalKnapsackDual.greedyFill ![d - c, u - t] [0, 1]
        (M₁ - c - t)) < psiTwo (M₁ / 2)
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
  rw [objective_greedyFill_pair _ _ 0 1 (by decide)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  by_cases hfirst : d - c ≤ M₁ - c - t
  · by_cases hsecond : u - t ≤ M₁ - c - t - (d - c)
    · obtain ⟨⟨x, y⟩, hx, _, _, _⟩ := htwo
      have hxle : x ≤ d := hx.1.elim (fun h => h.le.trans hcd.le) (fun h => h.le)
      have hyle : y ≤ u := hx.2.1.elim (fun h => h.le.trans htu.le) (fun h => h.le)
      have hh := actual_pair_bound_strict (c := c) (d := d) (t := t) (u := u)
        (Or.inr (Eq.refl d)) (Or.inr (Eq.refl u))
        (hc.trans hcd) (ht.trans htu) (M₀ := M₀) (M₁ := M₁) hM
        (by linarith [hx.2.2.1]) (by linarith)
        (by rintro ⟨hd, hu⟩; exact hdiag ⟨Or.inr hd.symm, Or.inr hu.symm⟩)
      convert hh using 1 <;>
        simp only [if_pos hfirst, if_pos hsecond] <;> ring
    · have hθ : (M₁ - c - t - (d - c)) / (u - t) ∈ Icc (0 : ℝ) 1 := by
        exact ⟨div_nonneg (by linarith) (sub_pos.mpr htu).le,
          (div_le_one (sub_pos.mpr htu)).mpr (by linarith)⟩
      have hb : (1 - (M₁ - c - t - (d - c)) / (u - t)) * t +
          (M₁ - c - t - (d - c)) / (u - t) * u + d = M₁ := by
        field_simp [sub_ne_zero.mpr htu.ne']
        <;> ring
      have hh := closed_row_bound_strict ht htu (hc.trans hcd) hM hswap hθ hb
        (by rintro ⟨ht, hc⟩; exact hdiag ⟨hc.symm, ht⟩)
      have hdist : gridDistance (M₀ / 2) (M₁ / 2) d c =
          gridDistance (M₀ / 2) (M₁ / 2) c d := min_comm _ _
      rw [hdist, add_comm (_ ^ 2) (_ ^ 2)] at hh
      convert hh using 1 <;>
        simp only [if_pos hfirst, if_neg hsecond] <;> ring
  · have hθ : (M₁ - c - t) / (d - c) ∈ Icc (0 : ℝ) 1 := by
      exact ⟨div_nonneg (by linarith) (sub_pos.mpr hcd).le,
        (div_le_one (sub_pos.mpr hcd)).mpr (by linarith)⟩
    have hb : (1 - (M₁ - c - t) / (d - c)) * c + (M₁ - c - t) / (d - c) * d + t = M₁ := by
      field_simp [sub_ne_zero.mpr hcd.ne']
      <;> ring
    have hh := closed_row_bound_strict hc hcd ht hM htwo hθ hb hdiag
    convert hh using 1 <;>
      simp only [if_neg hfirst] <;> ring

#print axioms psiTwo_strictMono_mean
#print axioms pair_value_spread_strict
#print axioms fractional_row_bound_strict

#print axioms pair_bound_strict
#print axioms gridDistance_lt_upper
#print axioms actual_pair_bound_strict

#print axioms grid_dual_le_greedy_pair

#print axioms corners_swap_nontrivial

#print axioms grid_dual_swap

#print axioms two_point_grid_dominance

#print axioms closed_row_bound_strict

#print axioms ordered_fill_bound_strict

end D5.S3.Analytic.Interpolation.TwoPointGridDominanceFinal
