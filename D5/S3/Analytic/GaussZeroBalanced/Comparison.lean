/- GID: D5/S3/Analytic/GaussZeroBalanced/Comparison
   generality: G
   mirror-B: D5/B/S3/Analytic/GaussZeroBalanced/Comparison
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Calculus.LocalExtr.Basic, mathlib/module/Mathlib.Topology.Order.Compact]
   utility: none
   digest: Singular endpoint comparison and the positive Riccati certificate for the zero-balanced quotient. -/

import D5.S3.Analytic.GaussZeroBalanced.Series
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

noncomputable section
open Set
open scoped Topology
open D5.S3.Analytic.GaussZeroBalanced.Defs

namespace D5.S3.Analytic.GaussZeroBalanced.Comparison

/-! A minimum argument gives the singular endpoint comparison principle. -/
theorem singular_comparison {R : ℝ} (hR : 0 < R) {u P : ℝ → ℝ}
    (hu0 : u 0 = 0)
    (hucont : ContinuousOn u (Icc 0 R))
    (huderiv : ∀ x ∈ Ioo (0 : ℝ) R, HasDerivAt u (deriv u x) x)
    (hP : ∀ x ∈ Ioo (0 : ℝ) R, 0 < P x)
    (hineq : ∀ x ∈ Ioo (0 : ℝ) R,
      0 < x * deriv u x + P x * u x) :
    ∀ x ∈ Ioo (0 : ℝ) R, 0 < u x := by
  intro x hx
  by_contra hux
  have hux' : u x ≤ 0 := le_of_not_gt hux
  have hxi : x ∈ Icc (0 : ℝ) x := ⟨le_of_lt hx.1, le_rfl⟩
  obtain ⟨y, hy, hymin⟩ :=
    isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hxi.1)
      (hucont.mono (by
        intro z hz
        exact ⟨hz.1, hz.2.trans hx.2.le⟩))
  have hmin_neg_contra : u y < 0 → False := by
    intro hyneg
    have hy0 : y ≠ 0 := by
      intro hy0
      subst y
      rw [hu0] at hyneg
      exact (lt_irrefl 0 hyneg)
    have hypos : 0 < y := lt_of_le_of_ne hy.1 (Ne.symm hy0)
    have hyR : y ∈ Ioo (0 : ℝ) R :=
      ⟨hypos, lt_of_le_of_lt hy.2 hx.2⟩
    have hdy := huderiv y hyR
    have hdy_nonpos : deriv u y ≤ 0 := by
      rcases hy.2.eq_or_lt' with (rfl | hyx)
      · have ht : (0 : ℝ) - x ∈ posTangentConeAt (Icc (0 : ℝ) x) x := by
          apply sub_mem_posTangentConeAt_of_segment_subset
          rw [segment_symm, segment_eq_Icc hxi.1]
        have hlocal : IsLocalMinOn u (Icc (0 : ℝ) x) x :=
          IsMinOn.isLocalMinOn hymin
        have hnon := IsLocalMinOn.hasFDerivWithinAt_nonneg hlocal
          hdy.hasFDerivAt.hasFDerivWithinAt ht
        have hnon' : 0 ≤ deriv u x * (0 - x) := by
          simpa [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, mul_comm] using hnon
        have hneg : (0 : ℝ) - x < 0 := sub_neg.mpr hx.1
        nlinarith
      · have htR : x - y ∈ posTangentConeAt (Icc (0 : ℝ) x) y := by
          apply sub_mem_posTangentConeAt_of_segment_subset
          rw [segment_eq_Icc hy.2]
          intro z hz
          exact ⟨hy.1.trans hz.1, hz.2⟩
        have htL : (0 : ℝ) - y ∈ posTangentConeAt (Icc (0 : ℝ) x) y := by
          apply sub_mem_posTangentConeAt_of_segment_subset
          rw [segment_symm, segment_eq_Icc hy.1]
          intro z hz
          exact ⟨hz.1, hz.2.trans hy.2⟩
        have hlocal : IsLocalMinOn u (Icc (0 : ℝ) x) y :=
          IsMinOn.isLocalMinOn hymin
        have hR' := IsLocalMinOn.hasFDerivWithinAt_nonneg hlocal
          hdy.hasFDerivAt.hasFDerivWithinAt htR
        have hL' := IsLocalMinOn.hasFDerivWithinAt_nonneg hlocal
          hdy.hasFDerivAt.hasFDerivWithinAt htL
        have hR'' : 0 ≤ deriv u y * (x - y) := by
          simpa [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, mul_comm] using hR'
        have hL'' : 0 ≤ deriv u y * (0 - y) := by
          simpa [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, mul_comm] using hL'
        have hxy : 0 < x - y := sub_pos.mpr hyx
        have hyneg' : 0 - y < 0 := sub_neg.mpr hypos
        nlinarith
    have hbad := hineq y hyR
    have hnonneg : P y * u y ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt (hP y hyR)) hyneg.le
    nlinarith
  by_cases huxlt : u x < 0
  · exact hmin_neg_contra (lt_of_le_of_lt (hymin hxi) huxlt)
  have huxeq : u x = 0 := le_antisymm hux' (le_of_not_gt huxlt)
  by_cases hylt : u y < 0
  · exact hmin_neg_contra hylt
  have hy_le0 : u y ≤ 0 := by simpa [huxeq] using (hymin hxi)
  have hyzero : u y = 0 := le_antisymm hy_le0
    (le_of_not_gt hylt)
  have hnonneg : ∀ z ∈ Icc (0 : ℝ) x, 0 ≤ u z := by
    intro z hz
    have h := hymin hz
    rw [hyzero] at h
    exact h
  have hminx : IsMinOn u (Icc (0 : ℝ) x) x := by
    intro z hz
    rw [huxeq]
    exact hnonneg z hz
  have ht : (0 : ℝ) - x ∈ posTangentConeAt (Icc (0 : ℝ) x) x := by
    apply sub_mem_posTangentConeAt_of_segment_subset
    rw [segment_symm, segment_eq_Icc hxi.1]
  have hnon := IsLocalMinOn.hasFDerivWithinAt_nonneg hminx.isLocalMinOn
    (huderiv x hx).hasFDerivAt.hasFDerivWithinAt ht
  have hnon' : 0 ≤ deriv u x * (0 - x) := by
    simpa [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, mul_comm] using hnon
  have hbad := hineq x hx
  rw [huxeq] at hbad
  nlinarith

/-! The Riccati equation implies the linear certificate identity. -/
theorem certificate_identity {R c q : ℝ} {f : ℝ → ℝ}
    (hfderiv : ∀ x ∈ Ioo (0 : ℝ) R, HasDerivAt f (deriv f x) x)
    (hfic : ∀ x ∈ Ioo (0 : ℝ) R,
      x * deriv f x = c * (1 - f x) - (c + 1) * q * (x / (1 - x)) * (f x) ^ 2)
    (hxf : ∀ x ∈ Ioo (0 : ℝ) R, x < 1) :
    ∀ x ∈ Ioo (0 : ℝ) R,
      let t := x / (1 - x)
      let E := q * t * (f x) ^ 2 + f x - 1
      x * deriv (fun z => q * (z / (1 - z)) * (f z) ^ 2 + f z - 1) x +
          c * (1 + 2 * q * t * f x) * E =
        q * t ^ 2 * (f x) ^ 2 * (1 - 2 * q * f x) := by
  intro x hx
  have hx1 : 1 - x ≠ 0 := by linarith [hxf x hx]
  have ht0 := (hasDerivAt_id x).div
    ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)) hx1
  have ht : HasDerivAt (fun z : ℝ => z / (1 - z))
      (1 / (1 - x) ^ 2) x := by
    convert ht0 using 1 <;> try rfl
    · dsimp
      field_simp [hx1]
      ring
  have hfx := hfderiv x hx
  have hE := (((ht.const_mul q).mul (hfx.pow 2)).add hfx).sub_const 1
  dsimp
  have hder := hE.deriv
  have hder' : deriv (fun z => q * (z / (1 - z)) * (f z) ^ 2 + f z - 1) x =
      q * (1 / (1 - x) ^ 2) * (f x) ^ 2 +
        q * (x / (1 - x)) * (2 * f x * deriv f x) + deriv f x := by
    convert hder using 1 <;> simp [Pi.pow_apply]
  rw [hder']
  have hr := hfic x hx
  field_simp [hx1] at hr ⊢
  linear_combination (1 - x + 2 * q * x * f x) * hr

private lemma hasDerivAt_certificate {q : ℝ} {f : ℝ → ℝ}
    {x : ℝ} (hx1 : x < 1)
    {f' : ℝ} (hfx : HasDerivAt f f' x) :
    HasDerivAt (fun z => q * (z / (1 - z)) * (f z) ^ 2 + f z - 1)
      (q * (1 / (1 - x) ^ 2) * (f x) ^ 2 +
        q * (x / (1 - x)) * (2 * f x * f') + f') x := by
  have hx1' : 1 - x ≠ 0 := by linarith
  have ht0 := (hasDerivAt_id x).div
    ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)) hx1'
  have ht : HasDerivAt (fun z : ℝ => z / (1 - z))
      (1 / (1 - x) ^ 2) x := by
    convert ht0 using 1 <;> try rfl
    · dsimp
      field_simp [hx1']
      ring
  have hE := (((ht.const_mul q).mul (hfx.pow 2)).add hfx).sub_const 1
  convert hE using 1 <;> simp [Pi.pow_apply]

theorem certificate {a b x : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hx : x ∈ Ioo (0 : ℝ) 1) :
    (1 - f a b x) / ((x / (1 - x)) * (f a b x) ^ 2) <
      a * b / ((a + b) * (a + b + 1)) := by
  let c : ℝ := a + b
  let q : ℝ := a * b / (c * (c + 1))
  let R : ℝ := (x + 1) / 2
  let E : ℝ → ℝ := fun z => q * (z / (1 - z)) * (f a b z) ^ 2 + f a b z - 1
  have hc : 0 < c := by dsimp [c]; linarith
  have hq : 0 < q := by
    dsimp [q]
    positivity
  have hRx : x ∈ Ioo (0 : ℝ) R := by
    constructor
    · exact hx.1
    · dsimp [R]
      linarith [hx.2]
  have hR1 : R < 1 := by
    dsimp [R]
    linarith [hx.2]
  have hcontf : ContinuousOn (f a b) (Icc (0 : ℝ) R) := by
    apply (Series.continuousOn_f ha hb).mono
    intro z hz
    exact ⟨hz.1, lt_of_le_of_lt hz.2 hR1⟩
  have hcontt : ContinuousOn (fun z : ℝ => z / (1 - z)) (Icc (0 : ℝ) R) := by
    apply ContinuousOn.div continuousOn_id (continuousOn_const.sub continuousOn_id)
    intro z hz
    have hz1 : z < 1 := lt_of_le_of_lt hz.2 hR1
    dsimp
    linarith
  have hcontE : ContinuousOn E (Icc (0 : ℝ) R) := by
    have hqcont : ContinuousOn (fun _ : ℝ => q) (Icc (0 : ℝ) R) := continuousOn_const
    have honecont : ContinuousOn (fun _ : ℝ => (1 : ℝ)) (Icc (0 : ℝ) R) := continuousOn_const
    convert ((hqcont.mul (hcontt.mul (hcontf.pow 2))).add hcontf).sub honecont using 1
    · funext z
      simp [E, Pi.pow_apply]
      ring
  have hE0 : E 0 = 0 := by
    dsimp [E]
    rw [Series.f_zero]
    norm_num
  have hEderiv : ∀ z ∈ Ioo (0 : ℝ) R, HasDerivAt E (deriv E z) z := by
    intro z hz
    have hz1 : z < 1 := lt_of_lt_of_le hz.2 hR1.le
    have hfz := Series.hasDerivAt_f ha hb hz.1.le hz1
    have h := hasDerivAt_certificate (q := q) hz1 hfz
    exact h.congr_deriv (by
      dsimp [E]
      symm
      exact h.deriv)
  have hEq : ∀ z ∈ Ioo (0 : ℝ) R,
      z * deriv (f a b) z = c * (1 - f a b z) - (c + 1) * q *
        (z / (1 - z)) * (f a b z) ^ 2 := by
    intro z hz
    have h := Series.riccati ha hb hz.1 (lt_of_lt_of_le hz.2 hR1.le)
    have hab : a * b / (a + b) = (c + 1) * q := by
      dsimp [c, q]
      field_simp
    simpa [c, hab] using h
  have hP : ∀ z ∈ Ioo (0 : ℝ) R,
      0 < c * (1 + 2 * q * (z / (1 - z)) * f a b z) := by
    intro z hz
    have hz1 : z < 1 := lt_of_lt_of_le hz.2 hR1.le
    have htz : 0 < z / (1 - z) := div_pos hz.1 (by linarith)
    have hfz : 0 < f a b z := Series.f_pos ha hb hz.1.le hz1
    positivity
  have hq_lt : q < (1 : ℝ) / 4 := by
    change a * b / (c * (c + 1)) < (1 : ℝ) / 4
    apply (div_lt_iff₀ (mul_pos hc (by linarith))).2
    dsimp [c] at hc ⊢
    have hcp : 0 < a + b := hc
    have hcpp : 0 < (a + b) * (a + b + 1) := mul_pos hcp (by linarith)
    nlinarith [sq_nonneg (a - b)]
  have hineq : ∀ z ∈ Ioo (0 : ℝ) R,
      0 < z * deriv E z + c * (1 + 2 * q * (z / (1 - z)) * f a b z) * E z := by
    intro z hz
    have hz1 : z < 1 := lt_of_lt_of_le hz.2 hR1.le
    have hfz : 0 < f a b z := Series.f_pos ha hb hz.1.le hz1
    have htz : 0 < z / (1 - z) := div_pos hz.1 (by linarith)
    have hsmall : 0 < 1 - 2 * q * f a b z := by
      have hf1 := Series.f_lt_one ha hb hz.1 hz1
      nlinarith
    have hfd : ∀ w ∈ Ioo (0 : ℝ) R,
        HasDerivAt (f a b) (deriv (f a b) w) w := by
      intro w hw
      have hfw := Series.hasDerivAt_f ha hb hw.1.le (lt_of_lt_of_le hw.2 hR1.le)
      exact hfw.congr_deriv (by symm; exact hfw.deriv)
    have hid := certificate_identity (f := f a b) (c := c) (q := q)
      hfd hEq (fun _ hz => lt_of_lt_of_le hz.2 hR1.le)
    have hp : 0 < q * (z / (1 - z)) ^ 2 * (f a b z) ^ 2 *
        (1 - 2 * q * f a b z) := by positivity
    have hid' : z * deriv E z + c * (1 + 2 * q * (z / (1 - z)) * f a b z) * E z =
        q * (z / (1 - z)) ^ 2 * (f a b z) ^ 2 * (1 - 2 * q * f a b z) := by
      simpa [E] using hid z hz
    nlinarith [hid', hp]
  have hEpos := singular_comparison (R := R) (u := E)
    (P := fun z => c * (1 + 2 * q * (z / (1 - z)) * f a b z))
    (by dsimp [R]; linarith [hx.1]) hE0 hcontE hEderiv hP hineq
  have hEx := hEpos x hRx
  have hden : 0 < (x / (1 - x)) * (f a b x) ^ 2 := by
    have : 0 < x / (1 - x) := div_pos hx.1 (by linarith [hx.2])
    have hf : 0 < f a b x := Series.f_pos ha hb hx.1.le hx.2
    positivity
  have hq_eq : q = a * b / ((a + b) * (a + b + 1)) := by rfl
  dsimp [E] at hEx
  rw [← hq_eq]
  apply (div_lt_iff₀ hden).2
  nlinarith [hEx]

end D5.S3.Analytic.GaussZeroBalanced.Comparison


namespace D5.S3.Analytic.GaussZeroBalanced.Comparison

lemma slope_neg_local {a b₁ b₂ : ℝ} (ha : 0 < a) (h1 : 0 < b₁) (h2 : 0 < b₂)
    (hder : deriv (fun y : ℝ => f a b₁ y - f a b₂ y) 0 < 0) :
    ∃ x ∈ Ioo (0:ℝ) 1, f a b₁ x < f a b₂ x := by
  have hw : HasDerivAt (fun y : ℝ => f a b₁ y - f a b₂ y)
      (deriv (f a b₁) 0 - deriv (f a b₂) 0) 0 := by
    have h1' := Series.hasDerivAt_f ha h1 (by positivity : (0:ℝ) ≤ 0) (by norm_num : (0:ℝ) < 1)
    have h2' := Series.hasDerivAt_f ha h2 (by positivity : (0:ℝ) ≤ 0) (by norm_num : (0:ℝ) < 1)
    have h1'' : HasDerivAt (f a b₁) (deriv (f a b₁) 0) 0 :=
      h1'.congr_deriv (by symm; exact h1'.deriv)
    have h2'' : HasDerivAt (f a b₂) (deriv (f a b₂) 0) 0 :=
      h2'.congr_deriv (by symm; exact h2'.deriv)
    convert h1''.sub h2'' using 1 <;> rfl
  have hlim := hw.tendsto_slope
  have hder' : deriv (fun y : ℝ => f a b₁ y - f a b₂ y) 0 =
      deriv (f a b₁) 0 - deriv (f a b₂) 0 := by
    exact (hw.deriv)
  have hder'' : deriv (f a b₁) 0 - deriv (f a b₂) 0 < 0 := by
    rw [← hder']
    exact hder
  have hev0 : ∀ᶠ y in 𝓝 (deriv (f a b₁) 0 - deriv (f a b₂) 0), y < 0 :=
    eventually_lt_nhds hder''
  have hev : ∀ᶠ y in 𝓝[≠] (0:ℝ),
      slope (fun y : ℝ => f a b₁ y - f a b₂ y) 0 y < 0 := hlim.eventually hev0
  have hlimpos := hev.filter_mono (nhdsWithin_mono (0:ℝ) (show Ioo (0:ℝ) 1 ⊆ ({0} : Set ℝ)ᶜ by
    intro y hy hzero
    have hyzero : y = 0 := by simpa [Set.mem_singleton_iff] using hzero
    exact (ne_of_gt hy.1) hyzero))
  have hnebot : (𝓝[Ioo (0:ℝ) 1] (0:ℝ)).NeBot := by
    rw [nhdsWithin_neBot]
    intro t ht
    rcases Metric.mem_nhds_iff.mp ht with ⟨ε, hε, hball⟩
    let y : ℝ := min (ε / 2) (1 / 2)
    refine ⟨y, hball ?_, ?_⟩
    · rw [Metric.mem_ball]
      have hyabs : |y| < ε := by
        rw [abs_of_pos (by
          have hhalf : 0 < (1 / 2 : ℝ) := by norm_num
          exact lt_min (by linarith [hε]) hhalf)]
        have hle : y ≤ ε / 2 := min_le_left _ _
        linarith
      simpa [Real.dist_eq] using hyabs
    · constructor
      · have hhalf : 0 < (1 / 2 : ℝ) := by norm_num
        exact lt_min (by linarith [hε]) hhalf
      · exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  letI : (𝓝[Ioo (0:ℝ) 1] (0:ℝ)).NeBot := hnebot
  have hmem : ∀ᶠ y in 𝓝[Ioo (0:ℝ) 1] (0:ℝ), y ∈ Ioo (0:ℝ) 1 := self_mem_nhdsWithin
  obtain ⟨y, hy, hys⟩ := (hmem.and hlimpos).exists
  refine ⟨y, hy, ?_⟩
  have hwy0 : f a b₁ 0 - f a b₂ 0 = 0 := by simp [Series.f_zero]
  have hypos : 0 < y := hy.1
  have hys' : y⁻¹ * (f a b₁ y - f a b₂ y) < 0 := by
    simpa [slope, hwy0, smul_eq_mul, vsub_eq_sub] using hys
  have hyinv : 0 < y⁻¹ := inv_pos.mpr hypos
  rcases (mul_neg_iff.mp hys') with ⟨_, hneg⟩ | ⟨hinv, _⟩
  · linarith
  · linarith


theorem comparison_iff {a b₁ b₂ : ℝ} (ha : 0 < a) (h1 : 0 < b₁) (h12 : b₁ < b₂) :
    (∀ x ∈ Ioo (0:ℝ) 1, f a b₂ x < f a b₁ x) ↔ b₁ * b₂ ≤ a * (a + 1) := by
  constructor
  · intro hall
    by_contra hnot
    have hprod : a * (a + 1) < b₁ * b₂ := lt_of_not_ge hnot
    obtain ⟨x, hx, hbad⟩ := slope_neg_local ha h1 (lt_trans h1 h12) (by
      have hw0 : deriv (fun y : ℝ => f a b₁ y - f a b₂ y) 0 =
          deriv (f a b₁) 0 - deriv (f a b₂) 0 := by
        have h1' := Series.hasDerivAt_f ha h1 (by norm_num : (0:ℝ) ≤ 0) (by norm_num : (0:ℝ) < 1)
        have h2' := Series.hasDerivAt_f ha (lt_trans h1 h12) (by norm_num : (0:ℝ) ≤ 0) (by norm_num : (0:ℝ) < 1)
        have h1'' : HasDerivAt (f a b₁) (deriv (f a b₁) 0) 0 :=
          h1'.congr_deriv (by symm; exact h1'.deriv)
        have h2'' : HasDerivAt (f a b₂) (deriv (f a b₂) 0) 0 :=
          h2'.congr_deriv (by symm; exact h2'.deriv)
        convert (h1''.sub h2'').deriv using 1 <;> rfl
      rw [hw0, Series.deriv_f_zero ha h1, Series.deriv_f_zero ha (lt_trans h1 h12)]
      have hb2 : 0 < b₂ := lt_trans h1 h12
      have hden : 0 < (a + b₁) * (a + b₁ + 1) * (a + b₂) * (a + b₂ + 1) := by positivity
      have hnum : a * (b₂ - b₁) * (a * (a + 1) - b₁ * b₂) < 0 := by
        have hpos : 0 < a * (b₂ - b₁) := mul_pos ha (sub_pos.mpr h12)
        exact mul_neg_of_pos_of_neg hpos (sub_neg.mpr hprod)
      have hfrac :
          -(a * b₁ / ((a + b₁) * (a + b₁ + 1))) -
              -(a * b₂ / ((a + b₂) * (a + b₂ + 1))) =
            (a * (b₂ - b₁) * (a * (a + 1) - b₁ * b₂)) /
              ((a + b₁) * (a + b₁ + 1) * (a + b₂) * (a + b₂ + 1)) := by
        field_simp [ne_of_gt (show 0 < a + b₁ by linarith),
          ne_of_gt (show 0 < a + b₁ + 1 by linarith),
          ne_of_gt (show 0 < a + b₂ by linarith),
          ne_of_gt (show 0 < a + b₂ + 1 by linarith)]
        ring
      rw [hfrac]
      exact (div_neg_iff).2 (Or.inr ⟨hnum, hden⟩))
    have hgood := hall x hx
    linarith
  · intro hprod x hx
    let R : ℝ := (x + 1) / 2
    let w : ℝ → ℝ := fun z => f a b₁ z - f a b₂ z
    have hRx : x ∈ Ioo (0:ℝ) R := by
      constructor
      · exact hx.1
      · dsimp [R]
        linarith [hx.2]
    have hR1 : R < 1 := by
      dsimp [R]
      linarith [hx.2]
    have hcont : ContinuousOn w (Icc (0:ℝ) R) := by
      have hc1 : ContinuousOn (f a b₁) (Icc (0:ℝ) R) :=
        (Series.continuousOn_f ha h1).mono (by
          intro z hz
          exact ⟨hz.1, lt_of_le_of_lt hz.2 hR1⟩)
      have hc2 : ContinuousOn (f a b₂) (Icc (0:ℝ) R) :=
        (Series.continuousOn_f ha (lt_trans h1 h12)).mono (by
          intro z hz
          exact ⟨hz.1, lt_of_le_of_lt hz.2 hR1⟩)
      convert hc1.sub hc2 using 1 <;> rfl
    have hw0 : w 0 = 0 := by simp [w, Series.f_zero]
    have hwd : ∀ z ∈ Ioo (0:ℝ) R, HasDerivAt w (deriv w z) z := by
      intro z hz
      have h1' := Series.hasDerivAt_f ha h1 hz.1.le (lt_of_lt_of_le hz.2 hR1.le)
      have h2' := Series.hasDerivAt_f ha (lt_trans h1 h12) hz.1.le (lt_of_lt_of_le hz.2 hR1.le)
      have h1'' : HasDerivAt (f a b₁) (deriv (f a b₁) z) z :=
        h1'.congr_deriv (by symm; exact h1'.deriv)
      have h2'' : HasDerivAt (f a b₂) (deriv (f a b₂) z) z :=
        h2'.congr_deriv (by symm; exact h2'.deriv)
      have hh := h1''.sub h2''
      convert hh.congr_deriv (by symm; exact hh.deriv) using 1 <;> rfl
    have hqcomp : b₁ * a / ((a + b₁) * (a + b₁ + 1)) ≤
        a ^ 2 / ((a + b₁) * (a + b₂)) := by
      have hc1 : 0 < a + b₁ := by linarith
      have hc2 : 0 < a + b₂ := by linarith
      have hcp : 0 < a + b₁ + 1 := by linarith
      have hdiff :
          a ^ 2 / ((a + b₁) * (a + b₂)) -
              b₁ * a / ((a + b₁) * (a + b₁ + 1)) =
            a * (a * (a + 1) - b₁ * b₂) /
              ((a + b₁) * (a + b₂) * (a + b₁ + 1)) := by
        field_simp
        ring
      have hnum : 0 ≤ a * (a * (a + 1) - b₁ * b₂) :=
        mul_nonneg ha.le (sub_nonneg.mpr hprod)
      have hden : 0 < (a + b₁) * (a + b₂) * (a + b₁ + 1) := by positivity
      have hnon : 0 ≤ a ^ 2 / ((a + b₁) * (a + b₂)) -
          b₁ * a / ((a + b₁) * (a + b₁ + 1)) := by
        rw [hdiff]
        exact div_nonneg hnum hden.le
      linarith
    have hEq : ∀ z ∈ Ioo (0:ℝ) R,
        z * deriv w z + ((a + b₂) + (a * b₂ / (a + b₂)) *
          (z / (1-z)) * (f a b₁ z + f a b₂ z)) * w z =
          (b₂ - b₁) * ((a^2 / ((a+b₁)*(a+b₂))) *
            (z/(1-z)) * (f a b₁ z)^2 - (1 - f a b₁ z)) := by
      intro z hz
      have hr1 := Series.riccati ha h1 hz.1 (lt_of_lt_of_le hz.2 hR1.le)
      have hr2 := Series.riccati ha (lt_trans h1 h12) hz.1 (lt_of_lt_of_le hz.2 hR1.le)
      have hwder : deriv w z = deriv (f a b₁) z - deriv (f a b₂) z := by
        have h1' := Series.hasDerivAt_f ha h1 hz.1.le (lt_of_lt_of_le hz.2 hR1.le)
        have h2' := Series.hasDerivAt_f ha (lt_trans h1 h12) hz.1.le
          (lt_of_lt_of_le hz.2 hR1.le)
        have h1'' : HasDerivAt (f a b₁) (deriv (f a b₁) z) z :=
          h1'.congr_deriv (by symm; exact h1'.deriv)
        have h2'' : HasDerivAt (f a b₂) (deriv (f a b₂) z) z :=
          h2'.congr_deriv (by symm; exact h2'.deriv)
        convert (h1''.sub h2'').deriv using 1 <;> rfl
      rw [hwder]
      dsimp [w]
      have hca1 : a + b₁ ≠ 0 := by linarith
      have hca2 : a + b₂ ≠ 0 := by linarith
      have hk : a * b₂ / (a + b₂) - a * b₁ / (a + b₁) =
          (b₂ - b₁) * a^2 / ((a+b₁)*(a+b₂)) := by
        field_simp [hca1, hca2]
        ring
      have hcalc :
          z * (deriv (f a b₁) z - deriv (f a b₂) z) +
              ((a + b₂) + (a * b₂ / (a + b₂)) *
                (z / (1-z)) * (f a b₁ z + f a b₂ z)) *
                (f a b₁ z - f a b₂ z) =
            (a * b₂ / (a + b₂) - a * b₁ / (a + b₁)) *
                (z / (1-z)) * (f a b₁ z)^2 -
              (b₂ - b₁) * (1 - f a b₁ z) := by
        linear_combination hr1 - hr2
      rw [hcalc, hk]
      ring
    have hP : ∀ z ∈ Ioo (0:ℝ) R, 0 <
        (a + b₂) + (a * b₂ / (a + b₂)) * (z/(1-z)) *
          (f a b₁ z + f a b₂ z) := by
      intro z hz
      have hz1 : z < 1 := lt_of_lt_of_le hz.2 hR1.le
      have ht : 0 < z/(1-z) := div_pos hz.1 (by linarith)
      have hf1 := Series.f_pos ha h1 hz.1.le hz1
      have hf2 := Series.f_pos ha (lt_trans h1 h12) hz.1.le hz1
      have hc2 : 0 < a + b₂ := by linarith
      have hk2 : 0 < a * b₂ / (a + b₂) :=
        div_pos (mul_pos ha (lt_trans h1 h12)) hc2
      positivity
    have hineq : ∀ z ∈ Ioo (0:ℝ) R, 0 <
        z * deriv w z + ((a + b₂) + (a * b₂ / (a + b₂)) *
          (z/(1-z)) * (f a b₁ z + f a b₂ z)) * w z := by
      intro z hz
      rw [hEq z hz]
      have hz1 : z < 1 := lt_of_lt_of_le hz.2 hR1.le
      have htden : 0 < (z/(1-z)) * (f a b₁ z)^2 := by
        have ht : 0 < z/(1-z) := div_pos hz.1 (by linarith)
        have hf := Series.f_pos ha h1 hz.1.le hz1
        positivity
      have hc : 0 ≤ a^2 / ((a+b₁)*(a+b₂)) -
          b₁*a / ((a+b₁)*(a+b₁+1)) := by linarith [hqcomp]
      have hmul := mul_nonneg hc htden.le
      have hcert := certificate ha h1 ⟨hz.1, hz1⟩
      have hcert' : 1 - f a b₁ z <
          (b₁*a / ((a+b₁)*(a+b₁+1))) * ((z/(1-z)) * (f a b₁ z)^2) := by
        have hc' := (div_lt_iff₀ htden).mp hcert
        convert hc' using 1 <;> ring
      have hstrict : 0 <
          (a^2 / ((a+b₁)*(a+b₂))) * ((z/(1-z)) * (f a b₁ z)^2) -
            (1 - f a b₁ z) := by nlinarith [hcert', hmul]
      have hdel : 0 < b₂ - b₁ := sub_pos.mpr h12
      have hstrict' : 0 <
          a^2 / ((a+b₁)*(a+b₂)) * (z/(1-z)) * (f a b₁ z)^2 -
            (1 - f a b₁ z) := by simpa [mul_assoc] using hstrict
      exact mul_pos hdel hstrict'
    have hwpos := singular_comparison (R := R) (u := w)
      (P := fun z => (a + b₂) + (a * b₂ / (a + b₂)) *
          (z/(1-z)) * (f a b₁ z + f a b₂ z))
      (by dsimp [R]; linarith [hx.1]) hw0 hcont hwd hP hineq
    have := hwpos x hRx
    dsimp [w] at this
    linarith

end D5.S3.Analytic.GaussZeroBalanced.Comparison


namespace D5.S3.Analytic.GaussZeroBalanced.Comparison

/-- The same parameter comparison after the contiguous quotient transformation. -/
theorem comparison_iff_quot {a b₁ b₂ : ℝ} (ha : 0 < a) (h1 : 0 < b₁) (h12 : b₁ < b₂) :
    (∀ x ∈ Ioo (0 : ℝ) 1, quot a b₂ x < quot a b₁ x) ↔
      b₁ * b₂ ≤ a * (a + 1) := by
  constructor
  · intro hall
    apply (comparison_iff ha h1 h12).mp
    intro x hx
    have h := hall x hx
    rw [Series.quot_eq ha (lt_trans h1 h12) hx.1.le hx.2,
      Series.quot_eq ha h1 hx.1.le hx.2] at h
    have hpos : 0 < 1 - x := by linarith [hx.2]
    have hh := (div_lt_iff₀ hpos).mp h
    simpa [hpos.ne'] using hh
  · intro hbound x hx
    have h := (comparison_iff ha h1 h12).mpr hbound x hx
    rw [Series.quot_eq ha (lt_trans h1 h12) hx.1.le hx.2,
      Series.quot_eq ha h1 hx.1.le hx.2]
    have hpos : 0 < 1 - x := by linarith [hx.2]
    apply (div_lt_iff₀ hpos).mpr
    simpa [hpos.ne'] using h

/-- The second Qiu--Ma--Xiang classification. -/
theorem clause2 : ∀ a : ℝ, 0 < a → a < 1 →
    ((∀ r ∈ Ioo (0 : ℝ) 1, ineq17 a r) ↔ 3 / 7 ≤ a) := by
  intro a ha ha1
  have hb1 : 0 < 1 - a := by linarith
  have hb12 : 1 - a < (3 / 2 : ℝ) - a := by norm_num
  have hcomp := comparison_iff_quot ha hb1 hb12
  have hshape : ∀ r, ineq17 a r ↔
      quot a (3 / 2 - a) r < quot a (1 - a) r := by
    intro r
    unfold ineq17 quot
    norm_num
    ring_nf
  have hthreshold :
      ((1 - a) * ((3 / 2 : ℝ) - a) ≤ a * (a + 1)) ↔
        3 / 7 ≤ a := by
    constructor
    · intro h
      norm_num at h ⊢
      nlinarith
    · intro h
      norm_num at h ⊢
      nlinarith
  constructor
  · intro hall
    have hq : (1 - a) * ((3 / 2 : ℝ) - a) ≤ a * (a + 1) := by
      apply hcomp.mp
      intro r hr
      exact (hshape r).mp (hall r hr)
    exact hthreshold.mp hq
  · intro ha37 r hr
    apply (hshape r).mpr
    have hq := hthreshold.mpr ha37
    exact (hcomp.mpr hq) r hr

end D5.S3.Analytic.GaussZeroBalanced.Comparison
