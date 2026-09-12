/- GID: D5/S3/Analytic/Interpolation/FractionalBranchGeometry
   generality: G
   mirror-B: D5/B/S3/Analytic/Interpolation/FractionalBranchGeometry
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A fractional row has a strict mean envelope and nested positive residual support. -/

import D5.S3.Analytic.Interpolation.EnvelopeKMonotone

open Set
open scoped Topology

noncomputable section

namespace D5.S3.Analytic.Interpolation.FractionalBranchGeometry

open TwoPointGridDominance EnvelopeKMonotone

/-- The logarithmic objective is strictly concave on the positive half-line. -/
theorem logValue_strictConcaveOn : StrictConcaveOn ℝ (Ioi 0) logValue := by
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

/-- A genuinely fractional row lies strictly below its mean vector and its variance envelope. -/
theorem fractional_mean_branch {k : ℕ} (hk : 2 ≤ k) (j : Fin k) (t : Fin k → ℝ)
    {c d θ μ V₀ : ℝ} (hc : 0 < c) (hcd : c < d) (ht : ∀ i, i ≠ j → 0 < t i)
    (hθ : θ ∈ Ioo 0 1)
    (hbudget : (1 - θ) * c + θ * d + ∑ i ∈ Finset.univ.erase j, t i = (k : ℝ) * μ)
    (hV₀ : 0 ≤ V₀)
    (hfloor : V₀ ≤ ((1 - θ) * c + θ * d - μ) ^ 2 +
      ∑ i ∈ Finset.univ.erase j, (t i - μ) ^ 2) :
    let z := (1 - θ) * c + θ * d
    let y := Function.update t j z
    let V := (z - μ) ^ 2 + ∑ i ∈ Finset.univ.erase j, (t i - μ) ^ 2
    (1 - θ) * logValue c + θ * logValue d +
        ∑ i ∈ Finset.univ.erase j, logValue (t i) < ∑ i, logValue (y i) ∧
      ∑ i, logValue (y i) ≤ psiK k μ V ∧ psiK k μ V ≤ psiK k μ V₀ := by
  dsimp only
  let z := (1 - θ) * c + θ * d
  let y := Function.update t j z
  have hcz : c < z := by dsimp [z]; nlinarith [hθ.1]
  have hy : ∀ i, 0 < y i := by
    intro i
    by_cases hij : i = j
    · subst i
      simpa [y] using hc.trans hcz
    · simpa [y, hij] using ht i hij
  have hsplit (g : ℝ → ℝ) :
      ∑ i, g (y i) = g z + ∑ i ∈ Finset.univ.erase j, g (t i) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
    simp only [y, Function.update_self]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  have hsum : ∑ i, y i = (k : ℝ) * μ := by
    simpa only [id_eq] using (hsplit id).trans hbudget
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by linarith
  have hmean : (∑ i, y i) / (k : ℝ) = μ := by
    rw [hsum, mul_div_cancel_left₀ _ (ne_of_gt hkpos)]
  have hμ : 0 < μ := by
    rw [← hmean]
    exact div_pos (Finset.sum_pos (fun i _ => hy i) ⟨j, Finset.mem_univ j⟩) hkpos
  have hvariance := hsplit (fun x => (x - μ) ^ 2)
  have hdomain := coordinate_variance_domain hk y hy
  dsimp only at hdomain
  rw [hmean, hvariance] at hdomain
  have hstrict := logValue_strictConcaveOn.2 hc (hc.trans hcd) hcd.ne
    (show 0 < 1 - θ by linarith [hθ.2]) hθ.1 (by ring)
  simp only [smul_eq_mul] at hstrict
  change _ < ∑ i, logValue (y i) ∧ _
  refine ⟨?_, ?_, ?_⟩
  · rw [hsplit logValue]
    exact add_lt_add_of_lt_of_le hstrict le_rfl
  · apply sum_logValue_le_psiK hk y hy hμ hmean.le
    · rw [hmean, hvariance]
    · exact hdomain.2
  · rcases lt_or_eq_of_le hfloor with hlt | heq
    · exact (psiK_strictAnti_variance hk hμ hV₀ hlt hdomain.2).le
    · rw [heq]

/-- A residual variance gap forces the two endpoints to straddle the whole mean interval. -/
theorem residual_distance_geometry {μ₀ μ c d z W V₀ : ℝ} (hμ : μ₀ < μ)
    (hz : z ∈ Ioo c d) (hsmall : (z - μ) ^ 2 + W < V₀)
    (hlarge : V₀ ≤ gridDistance μ₀ μ c d ^ 2 + W) :
    let v := gridDistance μ₀ μ c d
    |z - μ| < v ∧ c < μ₀ ∧ μ < d ∧ v = min (μ₀ - c) (d - μ) ∧ 0 < v := by
  dsimp only
  let v := gridDistance μ₀ μ c d
  have hv0 : 0 ≤ v := le_min Metric.infDist_nonneg Metric.infDist_nonneg
  have hsv : |z - μ| < v := by nlinarith [sq_abs (z - μ), abs_nonneg (z - μ)]
  have hv : 0 < v := (abs_nonneg _).trans_lt hsv
  have hleft {u : ℝ} (hu : u ∈ Icc μ₀ μ) : v ≤ |c - u| :=
    (min_le_left _ _).trans (by simpa [Real.dist_eq] using
      (Metric.infDist_le_dist_of_mem hu : Metric.infDist c (Icc μ₀ μ) ≤ dist c u))
  have hright {u : ℝ} (hu : u ∈ Icc μ₀ μ) : v ≤ |d - u| :=
    (min_le_right _ _).trans (by simpa [Real.dist_eq] using
      (Metric.infDist_le_dist_of_mem hu : Metric.infDist d (Icc μ₀ μ) ≤ dist d u))
  have hca : c < μ₀ := by
    by_contra hn
    have hac : μ₀ ≤ c := le_of_not_gt hn
    by_cases hcm : c ≤ μ
    · have hd0 := Metric.infDist_zero_of_mem (show c ∈ Icc μ₀ μ from ⟨hac, hcm⟩)
      have hh : v ≤ 0 := by
        dsimp [v, gridDistance]
        rw [hd0]
        exact min_le_left _ _
      linarith
    · have hh := hleft (show μ ∈ Icc μ₀ μ from ⟨hμ.le, le_rfl⟩)
      rw [abs_of_nonneg (by linarith : 0 ≤ c - μ)] at hh
      linarith [le_abs_self (z - μ), hz.1]
  have hmd : μ < d := by
    by_contra hn
    have hdm : d ≤ μ := le_of_not_gt hn
    by_cases had : μ₀ ≤ d
    · have hd0 := Metric.infDist_zero_of_mem (show d ∈ Icc μ₀ μ from ⟨had, hdm⟩)
      have hh : v ≤ 0 := by
        dsimp [v, gridDistance]
        rw [hd0]
        exact min_le_right _ _
      linarith
    · have hh := hright (show μ₀ ∈ Icc μ₀ μ from ⟨le_rfl, hμ.le⟩)
      rw [abs_of_nonpos (by linarith : d - μ₀ ≤ 0)] at hh
      linarith [neg_le_abs (z - μ), hz.2]
  have hdistc : Metric.infDist c (Icc μ₀ μ) = μ₀ - c := by
    apply le_antisymm
    · simpa [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hca.le)] using
        (Metric.infDist_le_dist_of_mem (show μ₀ ∈ Icc μ₀ μ from ⟨le_rfl, hμ.le⟩) :
          Metric.infDist c (Icc μ₀ μ) ≤ dist c μ₀)
    · apply (Metric.le_infDist (show (Icc μ₀ μ).Nonempty from ⟨μ₀, le_rfl, hμ.le⟩)).mpr
      intro u hu
      rw [Real.dist_eq, abs_of_nonpos (by linarith [hu.1] : c - u ≤ 0)]
      linarith [hu.1]
  have hdistd : Metric.infDist d (Icc μ₀ μ) = d - μ := by
    apply le_antisymm
    · simpa [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hmd.le)] using
        (Metric.infDist_le_dist_of_mem (show μ ∈ Icc μ₀ μ from ⟨hμ.le, le_rfl⟩) :
          Metric.infDist d (Icc μ₀ μ) ≤ dist d μ)
    · apply (Metric.le_infDist (show (Icc μ₀ μ).Nonempty from ⟨μ, hμ.le, le_rfl⟩)).mpr
      intro u hu
      rw [Real.dist_eq, abs_of_nonneg (by linarith [hu.2] : 0 ≤ d - u)]
      linarith [hu.2]
  exact ⟨hsv, hca, hmd, by simp only [gridDistance, hdistc, hdistd], hv⟩

/-- The actual lower-corner budget yields a positive nested pair of analytic support points. -/
theorem fractional_residual_support {k : ℕ} (hk : 2 ≤ k) (j : Fin k) (t : Fin k → ℝ)
    {c d θ μ₀ μ V₀ : ℝ} (hc : 0 < c) (hcd : c < d) (hθ : θ ∈ Ioo 0 1)
    (hμ : μ₀ < μ)
    (hbudget : (1 - θ) * c + θ * d + ∑ i ∈ Finset.univ.erase j, t i = (k : ℝ) * μ)
    (hlower : (k : ℝ) * μ₀ ≤ c + ∑ i ∈ Finset.univ.erase j, t i)
    (hsmall : ((1 - θ) * c + θ * d - μ) ^ 2 +
      ∑ i ∈ Finset.univ.erase j, (t i - μ) ^ 2 < V₀)
    (hlarge : V₀ ≤ gridDistance μ₀ μ c d ^ 2 +
      ∑ i ∈ Finset.univ.erase j, (t i - μ) ^ 2) :
    let z := (1 - θ) * c + θ * d
    let s := z - μ
    let v := gridDistance μ₀ μ c d
    let n := (k : ℝ) - 1
    let A := ((k : ℝ) * v + s) / n
    let c' := μ - A
    let d' := μ + v
    |s| < v ∧ c < μ₀ ∧ μ < d ∧ v = min (μ₀ - c) (d - μ) ∧
      (k : ℝ) * v ≤ ((k : ℝ) - 1) * (μ - c) - s ∧
      (0 < c ∧ c ≤ c' ∧ c' < μ - v ∧ μ - v < z ∧ z < μ + v ∧ μ + v = d' ∧ d' ≤ d) := by
  dsimp only
  let z := (1 - θ) * c + θ * d
  let s := z - μ
  let v := gridDistance μ₀ μ c d
  have hz : z ∈ Ioo c d := by
    dsimp [z]
    constructor <;> nlinarith [hθ.1, hθ.2]
  obtain ⟨hsv, hca, hmd, hvform, hv⟩ := residual_distance_geometry hμ hz hsmall hlarge
  have hvl : v ≤ μ₀ - c := by rw [show v = min (μ₀ - c) (d - μ) from hvform]; exact min_le_left _ _
  have hvr : v ≤ d - μ := by rw [show v = min (μ₀ - c) (d - μ) from hvform]; exact min_le_right _ _
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hn : (0 : ℝ) < (k : ℝ) - 1 := by linarith
  have hkv : (k : ℝ) * v ≤ ((k : ℝ) - 1) * (μ - c) - s := by
    have hmul := mul_le_mul_of_nonneg_left hvl (show (0 : ℝ) ≤ k by linarith)
    dsimp [s, z]
    nlinarith [hbudget, hlower]
  have hs := abs_lt.mp hsv
  have hAupper : ((k : ℝ) * v + s) / ((k : ℝ) - 1) ≤ μ - c :=
    (div_le_iff₀ hn).mpr (by nlinarith [hkv])
  have hAlower : v < ((k : ℝ) * v + s) / ((k : ℝ) - 1) :=
    (lt_div_iff₀ hn).mpr (by dsimp [s]; nlinarith [hs.1])
  refine ⟨hsv, hca, hmd, hvform, hkv, hc, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change c ≤ μ - ((k : ℝ) * v + s) / ((k : ℝ) - 1)
    linarith
  · change μ - ((k : ℝ) * v + s) / ((k : ℝ) - 1) < μ - v
    linarith
  · change μ - v < z
    linarith [hs.1]
  · change z < μ + v
    linarith [hs.2]
  · exact Eq.refl _
  · change μ + v ≤ d
    linarith

/-- A fractional row enters the strict mean-envelope branch or the nested-support branch. -/
theorem fractional_branch_alternative {k : ℕ} (hk : 2 ≤ k) (j : Fin k) (t : Fin k → ℝ)
    {c d θ μ₀ μ V₀ : ℝ} (hc : 0 < c) (hcd : c < d) (ht : ∀ i, i ≠ j → 0 < t i)
    (hθ : θ ∈ Ioo 0 1) (hμ : μ₀ < μ)
    (hbudget : (1 - θ) * c + θ * d + ∑ i ∈ Finset.univ.erase j, t i = (k : ℝ) * μ)
    (hlower : (k : ℝ) * μ₀ ≤ c + ∑ i ∈ Finset.univ.erase j, t i)
    (hV₀ : 0 ≤ V₀)
    (hlarge : V₀ ≤ gridDistance μ₀ μ c d ^ 2 +
      ∑ i ∈ Finset.univ.erase j, (t i - μ) ^ 2) :
    let z := (1 - θ) * c + θ * d
    let y := Function.update t j z
    let s := z - μ
    let V := s ^ 2 + ∑ i ∈ Finset.univ.erase j, (t i - μ) ^ 2
    let v := gridDistance μ₀ μ c d
    let c' := μ - ((k : ℝ) * v + s) / ((k : ℝ) - 1)
    let d' := μ + v
    (V₀ ≤ V ∧
      (1 - θ) * logValue c + θ * logValue d +
          ∑ i ∈ Finset.univ.erase j, logValue (t i) < ∑ i, logValue (y i) ∧
        ∑ i, logValue (y i) ≤ psiK k μ V ∧ psiK k μ V ≤ psiK k μ V₀) ∨
    (V < V₀ ∧ |s| < v ∧ c < μ₀ ∧ μ < d ∧ v = min (μ₀ - c) (d - μ) ∧
      (k : ℝ) * v ≤ ((k : ℝ) - 1) * (μ - c) - s ∧
      (0 < c ∧ c ≤ c' ∧ c' < μ - v ∧ μ - v < z ∧ z < μ + v ∧ μ + v = d' ∧ d' ≤ d)) := by
  dsimp only
  by_cases hfloor : V₀ ≤ ((1 - θ) * c + θ * d - μ) ^ 2 +
      ∑ i ∈ Finset.univ.erase j, (t i - μ) ^ 2
  · exact Or.inl ⟨hfloor, fractional_mean_branch hk j t hc hcd ht hθ hbudget hV₀ hfloor⟩
  · exact Or.inr ⟨lt_of_not_ge hfloor,
      fractional_residual_support hk j t hc hcd hθ hμ hbudget hlower
        (lt_of_not_ge hfloor) hlarge⟩

#print axioms logValue_strictConcaveOn
#print axioms fractional_mean_branch
#print axioms residual_distance_geometry
#print axioms fractional_residual_support
#print axioms fractional_branch_alternative

end D5.S3.Analytic.Interpolation.FractionalBranchGeometry
