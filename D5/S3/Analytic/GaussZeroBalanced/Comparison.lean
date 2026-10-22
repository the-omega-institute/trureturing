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
