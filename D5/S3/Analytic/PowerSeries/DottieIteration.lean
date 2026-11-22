/- GID: D5/S3/Analytic/PowerSeries/DottieIteration
   generality: I
   mirror-B: D5/B/S3/Analytic/PowerSeries/DottieIteration
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The cosine iteration converges from every real start to the unique real fixed point. -/

import D5.S3.Analytic.PowerSeries.DottieInverseSeries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Real.Pi.Bounds

/-! Global convergence of the cosine iteration.

The fixed point `θ ∈ (0, 1)` of the cosine and its uniqueness among positive reals come from
`DottieInverseSeries.rational_inverse_endpoint`. A real solution of `cos t = t` lies in
`[-1, 1]` and cannot be `≤ 0` because the cosine is positive on `[-1, 0]`, so `θ` is the only real
solution. Two cosine steps map every real number into `[cos 1, 1]`, the cosine maps this interval
into itself, and on `[0, 1]` it is Lipschitz with constant `sin 1 < 1` by
`cos u - cos v = -2 sin ((u + v) / 2) sin ((u - v) / 2)`. This gives the geometric error bound and
convergence. Since `θ < 3 / 4` and `cos 1 ≥ 1 / 2`, every point of `[cos 1, 1]` lies within
`1 - θ` of `θ`, which is the constant of the bound; it is attained at `n = 0` for `x = π / 2`,
whose second iterate is `1`. The derivative of the cosine at `θ` is `-sin θ`, which is the limit
of the ratio of consecutive errors along an orbit avoiding `θ`. -/

open Filter Topology

noncomputable section

namespace D5.S3.Analytic.PowerSeries.DottieIteration

/-- The cosine maps `[-1, 1]` into `[cos 1, 1]`. -/
private lemma cos_mem_Icc {y : ℝ} (hy : y ∈ Set.Icc (-1 : ℝ) 1) :
    Real.cos y ∈ Set.Icc (Real.cos 1) 1 := by
  refine ⟨?_, Real.cos_le_one y⟩
  rw [← Real.cos_abs y]
  exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg y)
    (by linarith [Real.pi_gt_three]) (abs_le.mpr hy)

/-- On `[0, 1]` the cosine is Lipschitz with constant `sin 1`. -/
private lemma abs_cos_sub_cos_le {u v : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1)
    (hv : v ∈ Set.Icc (0 : ℝ) 1) :
    |Real.cos u - Real.cos v| ≤ Real.sin 1 * |u - v| := by
  have hm0 : 0 ≤ (u + v) / 2 := by linarith [hu.1, hv.1]
  have hm1 : (u + v) / 2 ≤ 1 := by linarith [hu.2, hv.2]
  have hs0 : 0 ≤ Real.sin ((u + v) / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hm0 (by linarith [Real.pi_gt_three])
  have hs1 : Real.sin ((u + v) / 2) ≤ Real.sin 1 :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_gt_three])
      (by linarith [Real.pi_gt_three]) hm1
  have hd : |Real.sin ((u - v) / 2)| ≤ |u - v| / 2 := by
    calc |Real.sin ((u - v) / 2)| ≤ |(u - v) / 2| := Real.abs_sin_le_abs
      _ = |u - v| / 2 := by rw [abs_div, abs_two]
  rw [Real.cos_sub_cos, abs_mul, abs_mul, abs_of_nonneg hs0]
  calc |(-2 : ℝ)| * Real.sin ((u + v) / 2) * |Real.sin ((u - v) / 2)|
      ≤ 2 * Real.sin 1 * (|u - v| / 2) := by
        rw [abs_neg, abs_two]
        have : 0 ≤ Real.sin 1 := hs0.trans hs1
        gcongr
    _ = Real.sin 1 * |u - v| := by ring

/-- Iterates starting in `[cos 1, 1]` stay there and approach a fixed point `θ` there
geometrically with ratio `sin 1`. -/
private lemma iterate_mem_and_le {θ y : ℝ} (hθ : θ ∈ Set.Icc (Real.cos 1) 1)
    (hc : Real.cos θ = θ) (hy : y ∈ Set.Icc (Real.cos 1) 1) (n : ℕ) :
    Real.cos^[n] y ∈ Set.Icc (Real.cos 1) 1 ∧
      |Real.cos^[n] y - θ| ≤ Real.sin 1 ^ n * |y - θ| := by
  induction n with
  | zero => simp [hy]
  | succ n ih =>
    have h1 := Real.cos_one_pos
    have hmem : Real.cos^[n] y ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith [ih.1.1], ih.1.2⟩
    rw [Function.iterate_succ_apply']
    refine ⟨cos_mem_Icc hmem, ?_⟩
    calc |Real.cos (Real.cos^[n] y) - θ|
        = |Real.cos (Real.cos^[n] y) - Real.cos θ| := by rw [hc]
      _ ≤ Real.sin 1 * |Real.cos^[n] y - θ| :=
        abs_cos_sub_cos_le ⟨by linarith [ih.1.1], ih.1.2⟩ ⟨by linarith [hθ.1], hθ.2⟩
      _ ≤ Real.sin 1 * (Real.sin 1 ^ n * |y - θ|) := by
        gcongr
        · exact Real.sin_nonneg_of_nonneg_of_le_pi zero_le_one
            (by linarith [Real.pi_gt_three])
        · exact ih.2
      _ = Real.sin 1 ^ (n + 1) * |y - θ| := by ring

/-- A fixed point `θ ≤ 1` of the cosine satisfies `θ < 3 / 4`. -/
private lemma fixed_lt {θ : ℝ} (hθ : θ ∈ Set.Icc (Real.cos 1) 1) (hc : Real.cos θ = θ) :
    θ < 3 / 4 := by
  by_contra h
  have hb := Real.cos_bound (x := 3 / 4) (by norm_num [abs_of_pos])
  have hle : Real.cos θ ≤ Real.cos (3 / 4) :=
    Real.cos_le_cos_of_nonneg_of_le_pi (by norm_num) (by linarith [hθ.2, Real.pi_gt_three])
      (not_lt.mp h)
  rw [abs_le] at hb
  norm_num [abs_of_pos] at hb
  linarith [hb.2]

/-- `cos 1 ≥ 1 / 2`. -/
private lemma half_le_cos_one : (1 / 2 : ℝ) ≤ Real.cos 1 := by
  have := Real.one_sub_sq_div_two_le_cos (x := 1)
  norm_num at this
  linarith

/-- The conclusions of `cos_iterate_tendsto` for any fixed point `θ` of the cosine that is the
only positive one. -/
private lemma iterate_of_fixed (θ : ℝ) (hc : Real.cos θ = θ)
    (hu : ∀ t : ℝ, 0 < t → Real.cos t = t → t = θ) :
    (∀ t : ℝ, Real.cos t = t ↔ t = θ) ∧
      ∀ x : ℝ, Tendsto (fun n : ℕ => Real.cos^[n] x) atTop (𝓝 θ) ∧
        (∀ n : ℕ, |Real.cos^[n + 2] x - θ| ≤ Real.sin 1 ^ n * (1 - θ)) ∧
        ((∀ n : ℕ, Real.cos^[n] x ≠ θ) →
          Tendsto (fun n : ℕ => (Real.cos^[n + 1] x - θ) / (Real.cos^[n] x - θ)) atTop
            (𝓝 (-Real.sin θ))) := by
  have hθ : θ ∈ Set.Icc (Real.cos 1) 1 := by
    rw [← hc]
    exact cos_mem_Icc ⟨by rw [← hc]; exact Real.neg_one_le_cos θ, by
      rw [← hc]; exact Real.cos_le_one θ⟩
  refine ⟨fun t => ⟨fun ht => hu t ?_ ht, fun ht => ht ▸ hc⟩, fun x => ?_⟩
  · by_contra hneg
    have hle : t ≤ 0 := not_lt.mp hneg
    have hge : -1 ≤ t := ht ▸ Real.neg_one_le_cos t
    have hpos : 0 < Real.cos t :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_gt_three], by linarith [Real.pi_gt_three]⟩
    linarith
  have hx2 : Real.cos^[2] x ∈ Set.Icc (Real.cos 1) 1 := by
    rw [Function.iterate_succ_apply', Function.iterate_one]
    exact cos_mem_Icc ⟨Real.neg_one_le_cos x, Real.cos_le_one x⟩
  have hrate : ∀ n : ℕ, |Real.cos^[n + 2] x - θ| ≤ Real.sin 1 ^ n * (1 - θ) := by
    intro n
    rw [Function.iterate_add_apply]
    refine (iterate_mem_and_le hθ hc hx2 n).2.trans ?_
    gcongr
    · exact pow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi zero_le_one
        (by linarith [Real.pi_gt_three])) n
    · rw [abs_sub_le_iff]
      constructor <;> linarith [hx2.1, hx2.2, hθ.1, hθ.2, fixed_lt hθ hc, half_le_cos_one]
  have hconv : Tendsto (fun n : ℕ => Real.cos^[n] x) atTop (𝓝 θ) := by
    refine (tendsto_add_atTop_iff_nat 2).mp ?_
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hs : Tendsto (fun n : ℕ => Real.sin 1 ^ n * (1 - θ)) atTop (𝓝 0) := by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one
        (Real.sin_nonneg_of_nonneg_of_le_pi zero_le_one (by linarith [Real.pi_gt_three]))
        (by simpa using Real.sin_lt one_pos)).mul_const (1 - θ)
      simpa using this
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => by
      rw [Real.norm_eq_abs]; exact hrate n) hs
  refine ⟨hconv, hrate, fun hne => ?_⟩
  have hslope := hasDerivAt_iff_tendsto_slope.mp (Real.hasDerivAt_cos θ)
  have hwithin : Tendsto (fun n : ℕ => Real.cos^[n] x) atTop (𝓝[≠] θ) :=
    tendsto_nhdsWithin_iff.mpr ⟨hconv, Eventually.of_forall fun n => hne n⟩
  refine (hslope.comp hwithin).congr fun n => ?_
  rw [Function.comp_apply, slope_def_field, Function.iterate_succ_apply', hc]

/-- The equation `cos t = t` has exactly one real solution `θ`, which lies in `(0, 1)`; the cosine
iteration converges to `θ` from every real starting point, from the second iterate on at the
uniform geometric rate `sin 1` with constant `1 - θ`; and if the orbit never hits `θ`, the ratio
of consecutive errors tends to `-sin θ`. -/
theorem cos_iterate_tendsto :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ (∀ t : ℝ, Real.cos t = t ↔ t = θ) ∧
      ∀ x : ℝ, Tendsto (fun n : ℕ => Real.cos^[n] x) atTop (𝓝 θ) ∧
        (∀ n : ℕ, |Real.cos^[n + 2] x - θ| ≤ Real.sin 1 ^ n * (1 - θ)) ∧
        ((∀ n : ℕ, Real.cos^[n] x ≠ θ) →
          Tendsto (fun n : ℕ => (Real.cos^[n + 1] x - θ) / (Real.cos^[n] x - θ)) atTop
            (𝓝 (-Real.sin θ))) := by
  obtain ⟨θ, h0, h1, hc, hu, -⟩ := DottieInverseSeries.rational_inverse_endpoint
  exact ⟨θ, h0, h1, iterate_of_fixed θ hc hu⟩

end D5.S3.Analytic.PowerSeries.DottieIteration
