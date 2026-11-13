/- GID: D5/S3/Analytic/Fourier/PositiveDefinite/UniformFourPointPrecision
   generality: I
   mirror-B: D5/B/S3/Analytic/Fourier/PositiveDefinite/UniformFourPointPrecision
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Convex.Deriv, mathlib/module/Mathlib.LinearAlgebra.Matrix.PosDef, mathlib/module/Mathlib.LinearAlgebra.Matrix.SchurComplement]
   utility: none
   digest: One uniform window for six strict precision signs with arbitrary four-node gap ratios. -/
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Analysis.Complex.Order
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic

/-! Uniform four-point precision signs from scalar logarithmic cusp controls. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Set Filter MeasureTheory Matrix intervalIntegral
open scoped Topology BigOperators ComplexOrder Interval
namespace D5.S3.Analytic.Fourier.PositiveDefinite.UniformFourPointPrecision

/-- The logarithmic cusp envelope. -/
def L (t : ℝ) : ℝ := Real.log (Real.exp 1 / t)

/-- The strict-concavity deficit. -/
def psi (v : ℝ → ℝ) (a b : ℝ) : ℝ := v a + v b - v (a + b)

/-- The mixed increment away from the singular corner. -/
def interaction (v : ℝ → ℝ) (p q r : ℝ) : ℝ := v (p + q) + v (q + r) - v q - v (p + q + r)

/-- Both positive terms are retained, including the extreme-ratio correction. -/
def weight (v : ℝ → ℝ) (p q r : ℝ) : ℝ := interaction v p q r + psi v p q * psi v q r / v q

/-- Raw local differential estimates, with no cofactor or inverse-sign premise. -/
structure CuspControl (v h g : ℝ → ℝ) (δ : ℝ) : Prop where
  delta_pos : 0 < δ
  delta_small : δ ≤ Real.exp (-1)
  zero : v 0 = 0
  continuous : Continuous v
  deriv_v : ∀ t ∈ Ioc 0 δ, HasDerivAt v (h t) t
  deriv_h : ∀ t ∈ Ioc 0 δ, HasDerivAt h (-g t) t
  continuous_g : ContinuousOn g (Ioc 0 δ)
  h_pos : ∀ t ∈ Ioc 0 δ, 0 < h t
  h_upper : ∀ t ∈ Ioc 0 δ, h t ≤ Real.log (1 / t)
  g_lower : ∀ t ∈ Ioc 0 δ, 1 / (4 * t) ≤ g t
  g_upper : ∀ t ∈ Ioc 0 δ, g t ≤ 1 / t
private lemma L_eq {t : ℝ} (ht : 0 < t) : L t = 1 + Real.log (1/t) := by
  rw [L, Real.log_div (Real.exp_pos 1).ne' ht.ne', Real.log_exp, one_div, Real.log_inv]
  ring
private lemma L_ge_one {t δ : ℝ} (ht : 0 < t) (htδ : t ≤ δ) (hδ : δ ≤ Real.exp (-1)) : 1 ≤ L t := by
  have hl := Real.log_le_log ht (htδ.trans hδ)
  rw [Real.log_exp] at hl
  rw [L_eq ht, one_div, Real.log_inv]
  linarith
private lemma L_split {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : L a = L b + Real.log (b/a) := by
  rw [L_eq ha, L_eq hb, Real.log_div hb.ne' ha.ne', one_div, one_div, Real.log_inv, Real.log_inv]
  ring
private lemma log_one_add_half {z : ℝ} (hz : 1 ≤ z) : (1 + Real.log z) / 2 ≤ Real.log (1+z) := by
  let f : ℝ → ℝ := fun x => Real.log (1+x) - (1 + Real.log x)/2
  have hd (x : ℝ) (hx : 1 ≤ x) : HasDerivAt f ((x-1)/(2*x*(1+x))) x := by
    have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
    have hpos : 0 < 1 + x := by linarith
    convert (((hasDerivAt_id x).const_add 1).log hpos.ne').sub (((Real.hasDerivAt_log hx0.ne').const_add 1).div_const 2) using 1
    · rfl
    · simp only [id_eq]
      field_simp [hx0.ne', hpos.ne']
      ring_nf
  have hm : MonotoneOn f (Ici 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 1) (fun x hx => (hd x hx).continuousAt.continuousWithinAt) (fun x hx => (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt)
    intro x hx
    rw [(hd x (interior_subset hx)).deriv]
    exact div_nonneg (sub_nonneg.mpr (interior_subset hx)) (by
      have : 0 < x := lt_of_lt_of_le zero_lt_one (interior_subset hx)
      positivity)
  have hbase := Real.le_log_one_add_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)
  have h := hm (show (1 : ℝ) ∈ Ici 1 from by simp) hz hz
  dsimp [f] at h
  norm_num at hbase h
  linarith
private lemma log_one_add_exp_half {y : ℝ} (hy : 0 ≤ y) : (1+y)/3 ≤ Real.log (1 + Real.exp y/2) := by
  let f : ℝ → ℝ := fun x => Real.log (1 + Real.exp x/2) - (1+x)/3
  have hd (x : ℝ) : HasDerivAt f (Real.exp x / (2 + Real.exp x) - 1/3) x := by
    convert ((((Real.hasDerivAt_exp x).div_const 2).const_add 1).log (by positivity)).sub (((hasDerivAt_id x).const_add 1).div_const 3) using 1
    · rfl
    · field_simp <;> ring
  have hm : MonotoneOn f (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (fun x _ => (hd x).continuousAt.continuousWithinAt) (fun x _ => (hd x).differentiableAt.differentiableWithinAt)
    intro x hx
    rw [(hd x).deriv]
    have hx0 : 0 ≤ x := interior_subset hx
    have he : 1 ≤ Real.exp x := Real.one_le_exp hx0
    apply sub_nonneg.mpr
    apply (le_div_iff₀ (by positivity : 0 < 2 + Real.exp x)).mpr
    linarith
  have hbase := Real.le_log_one_add_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/2)
  have hh := hm (show (0 : ℝ) ∈ Ici 0 from by simp) hy hy
  dsimp [f] at hh
  norm_num at hbase hh
  linarith
private lemma v_strictMono {v h g : ℝ → ℝ} {δ : ℝ} (H : CuspControl v h g δ) : StrictMonoOn v (Icc 0 δ) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 δ) H.continuous.continuousOn
  intro t ht
  have ht' : t ∈ Ioc 0 δ := by
    rw [interior_Icc] at ht
    exact ⟨ht.1, ht.2.le⟩
  rw [(H.deriv_v t ht').deriv]
  exact H.h_pos t ht'
private lemma v_pos {v h g : ℝ → ℝ} {δ t : ℝ} (H : CuspControl v h g δ) (ht : 0 < t) (htδ : t ≤ δ) : 0 < v t := by simpa [H.zero] using v_strictMono H ⟨le_rfl, H.delta_pos.le⟩ ⟨ht.le, htδ⟩ ht
private lemma h_integrable {v h g : ℝ → ℝ} {δ t : ℝ} (H : CuspControl v h g δ) (ht : 0 < t) (htδ : t ≤ δ) : IntervalIntegrable h volume 0 t := by
  have hg : IntervalIntegrable (fun u : ℝ => -Real.log u) volume 0 t := intervalIntegrable_log'.neg
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le).mpr
  apply ((intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le).mp hg).mono'
  · exact (show ContinuousOn h (Ioc 0 t) from fun u hu =>
      (H.deriv_h u ⟨hu.1, hu.2.trans htδ⟩).continuousAt.continuousWithinAt
      ).aestronglyMeasurable measurableSet_Ioc
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    rw [Real.norm_eq_abs, abs_of_pos (H.h_pos u ⟨hu.1, hu.2.trans htδ⟩)]
    simpa [one_div, Real.log_inv] using H.h_upper u ⟨hu.1, hu.2.trans htδ⟩
private lemma v_integral {v h g : ℝ → ℝ} {δ t : ℝ} (H : CuspControl v h g δ) (ht : 0 < t) (htδ : t ≤ δ) : (∫ u in (0 : ℝ)..t, h u) = v t := by
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto ht (fun u hu => H.deriv_v u ⟨hu.1, hu.2.le.trans htδ⟩) (h_integrable H ht htδ) (H.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) (H.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  simpa [H.zero] using hi
private lemma v_upper {v h g : ℝ → ℝ} {δ t : ℝ} (H : CuspControl v h g δ) (ht : 0 < t) (htδ : t ≤ δ) : v t ≤ t * L t := by
  have hm := intervalIntegral.integral_mono_on_of_le_Ioo ht.le (h_integrable H ht htδ) (intervalIntegrable_log'.neg) (fun u hu => by simpa [one_div, Real.log_inv] using H.h_upper u ⟨hu.1, hu.2.le.trans htδ⟩)
  rw [v_integral H ht htδ] at hm
  have hm' : v t ≤ -(∫ u in (0 : ℝ)..t, Real.log u) := by
    calc
      v t ≤ (∫ u in (0 : ℝ)..t, (-Real.log) u) := hm
      _ = -(∫ u in (0 : ℝ)..t, Real.log u) := by exact intervalIntegral.integral_neg
  rw [integral_log_from_zero_of_pos ht] at hm'
  have hm := hm'
  rw [L_eq ht, one_div, Real.log_inv]
  nlinarith
private lemma h_diff_lower {v h g : ℝ → ℝ} {δ a b : ℝ} (H : CuspControl v h g δ) (ha : 0 < a) (hb : 0 < b) (hab : a+b ≤ δ) : Real.log (1+b/a)/4 ≤ h a - h (a+b) := by
  let f : ℝ → ℝ := fun t => h t + Real.log t / 4
  have hd (t : ℝ) (ht : t ∈ Icc a (a+b)) : HasDerivAt f (-g t + 1/(4*t)) t := by
    have ht0 : 0 < t := ha.trans_le ht.1
    convert (H.deriv_h t ⟨ht0, ht.2.trans hab⟩).add ((Real.hasDerivAt_log ht0.ne').div_const 4) using 1
    · simp [div_eq_mul_inv]
  have hm : AntitoneOn f (Icc a (a+b)) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc a (a+b)) (fun t ht => (hd t ht).continuousAt.continuousWithinAt) (fun t ht => (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt)
    intro t ht
    rw [(hd t (interior_subset ht)).deriv]
    have ht' : t ∈ Icc a (a+b) := interior_subset ht
    linarith [H.g_lower t ⟨ha.trans_le ht'.1, ht'.2.trans hab⟩]
  have hh := hm ⟨le_rfl, by linarith⟩ ⟨by linarith, le_rfl⟩ (by linarith : a ≤ a+b)
  have he : Real.log (1+b/a) = Real.log (a+b) - Real.log a := by
    rw [← Real.log_div (by positivity : a+b ≠ 0) ha.ne']
    congr 1
    field_simp
  dsimp [f] at hh
  rw [he]
  linarith
private lemma psi_lower {v h g : ℝ → ℝ} {δ a b : ℝ} (H : CuspControl v h g δ) (ha : 0 < a) (hb : 0 < b) (hab : a+b ≤ δ) : a/4 * Real.log (1+b/a) ≤ psi v a b := by
  let c := Real.log (1+b/a)/4
  let f : ℝ → ℝ := fun u => psi v u b - u*c
  have hc : Continuous f := by
    dsimp [f, psi]
    exact (H.continuous.add continuous_const).sub (H.continuous.comp (continuous_id.add continuous_const)) |>.sub (continuous_id.mul continuous_const)
  have hd (u : ℝ) (hu : u ∈ Ioo 0 a) : HasDerivAt f (h u - h (u+b) - c) u := by
    have h₁ := H.deriv_v u ⟨hu.1, hu.2.le.trans (by linarith [hab, hb.le])⟩
    have h₂ := (H.deriv_v (u+b) ⟨by linarith [hu.1, hb], by linarith [hu.2, hab]⟩).comp u ((hasDerivAt_id u).add_const b)
    convert ((h₁.add_const (v b)).sub h₂).sub ((hasDerivAt_id u).mul_const c) using 1
    · ext z
      simp [f, psi, Function.comp_def, id_eq]
    · simp [f, psi, Function.comp_def, id_eq]
  have hm : MonotoneOn f (Icc 0 a) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 a) hc.continuousOn
    · intro u hu
      rw [interior_Icc] at hu
      exact (hd u hu).differentiableAt.differentiableWithinAt
    · intro u hu
      rw [interior_Icc] at hu
      rw [(hd u hu).deriv]
      have hr : b/a ≤ b/u := div_le_div_of_nonneg_left hb.le hu.1 hu.2.le
      have harg : 1 + b/a ≤ 1 + b/u := by linarith
      have hl := Real.log_le_log (by positivity : 0 < 1+b/a) harg
      have hh := h_diff_lower H hu.1 hb (by linarith [hu.2, hab] : u+b ≤ δ)
      dsimp [c]
      linarith
  have hh := hm ⟨le_rfl, ha.le⟩ ⟨ha.le, le_rfl⟩ ha.le
  dsimp [f, c, psi] at hh ⊢
  rw [H.zero, zero_add] at hh
  simpa [H.zero, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hh
private lemma psi_lower_log {v h g : ℝ → ℝ} {δ a b : ℝ} (H : CuspControl v h g δ) (ha : 0 < a) (hb : 0 < b) (hab : a+b ≤ δ) (hle : a ≤ b) : a/8 * (1 + Real.log (b/a)) ≤ psi v a b := by
  have hr : 1 ≤ b/a := (one_le_div ha).mpr hle
  have hh := mul_le_mul_of_nonneg_left (log_one_add_half hr) (show 0 ≤ a/4 by positivity)
  have hl := psi_lower H ha hb hab
  nlinarith
private lemma interaction_lower {v h g : ℝ → ℝ} {δ p q r : ℝ} (H : CuspControl v h g δ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (hs : p+q+r ≤ δ) : p/4 * Real.log (1+r/(p+q)) ≤ interaction v p q r := by
  let c := Real.log (1+r/(p+q))/4
  let f : ℝ → ℝ := fun u => v (q+u) - v (q+u+r) - u*c
  have hd (u : ℝ) (hu : u ∈ Icc 0 p) : HasDerivAt f (h (q+u) - h (q+u+r) - c) u := by
    have h₁ := (H.deriv_v (q+u) ⟨by linarith [hu.1, hq], by linarith [hu.2, hs]⟩).comp u ((hasDerivAt_id u).const_add q)
    have h₂ := (H.deriv_v (q+u+r) ⟨by linarith [hu.1, hq, hr], by linarith [hu.2, hs]⟩).comp u (((hasDerivAt_id u).const_add q).add_const r)
    convert (h₁.sub h₂).sub ((hasDerivAt_id u).mul_const c) using 1
    · ext z
      simp [f, Function.comp_def, id_eq]
    · simp [f, Function.comp_def, id_eq]
  have hm : MonotoneOn f (Icc 0 p) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 p) (fun u hu => (hd u hu).continuousAt.continuousWithinAt) (fun u hu => (hd u (interior_subset hu)).differentiableAt.differentiableWithinAt)
    intro u hu
    have hu' : u ∈ Icc 0 p := interior_subset hu
    rw [(hd u hu').deriv]
    have hqu : 0 < q+u := by linarith [hu'.1]
    have hh := h_diff_lower H hqu hr (by linarith [hu'.2] : q+u+r ≤ δ)
    have harg : 1 + r/(p+q) ≤ 1 + r/(q+u) := by
      have hden : q+u ≤ p+q := by linarith [hu'.2]
      have hdiv := div_le_div_of_nonneg_left hr.le (by positivity : 0 < q+u) hden
      linarith
    have hl := Real.log_le_log (by positivity : 0 < 1+r/(p+q)) harg
    dsimp [c]
    linarith
  have hh := hm ⟨le_rfl, hp.le⟩ ⟨hp.le, le_rfl⟩ hp.le
  dsimp [f, c, interaction] at hh ⊢
  rw [add_zero] at hh
  have he₁ : q + p = p + q := by ring
  have he₂ : q + p + r = p + q + r := by ring
  rw [he₁] at hh
  linarith
private lemma interaction_crude {v h g : ℝ → ℝ} {δ p q r : ℝ} (H : CuspControl v h g δ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (hs : p+q+r ≤ δ) : p*r/(4*(p+q+r)) ≤ interaction v p q r := by
  have hl := Real.one_sub_inv_le_log_of_pos (show 0 < 1+r/(p+q) by positivity)
  have he : 1 - (1+r/(p+q))⁻¹ = r/(p+q+r) := by field_simp; ring
  rw [he] at hl
  have hm := mul_le_mul_of_nonneg_left hl (show 0 ≤ p/4 by positivity)
  have hh := interaction_lower H hp hq hr hs
  convert hm.trans hh using 1 <;> field_simp <;> ring
private lemma interaction_long {v h g : ℝ → ℝ} {δ p q r : ℝ} (H : CuspControl v h g δ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (hs : p+q+r ≤ δ) (hmax : p ≤ max p q) (hqr : max p q ≤ r) : p/12 * (1 + Real.log (r / max p q)) ≤ interaction v p q r := by
  have hm : 0 < max p q := hp.trans_le (le_max_left _ _)
  have hsum : p+q ≤ 2 * max p q := by
    have h₁ := le_max_left p q
    have h₂ := le_max_right p q
    linarith
  let y := Real.log (r / max p q)
  have hy : 0 ≤ y := Real.log_nonneg ((one_le_div hm).mpr hqr)
  have he : Real.exp y / 2 = r/(2 * max p q) := by
    dsimp [y]
    rw [Real.exp_log (div_pos hr hm)]
    ring
  have hl := log_one_add_exp_half hy
  rw [he] at hl
  have harg : 1 + r/(2*max p q) ≤ 1 + r/(p+q) := by
    have hdiv := div_le_div_of_nonneg_left hr.le (by positivity : 0 < p+q) hsum
    linarith
  have hlog := Real.log_le_log (by positivity : 0 < 1+r/(2*max p q)) harg
  have hi := interaction_lower H hp hq hr hs
  dsimp [y] at hl
  nlinarith
private lemma psi_symm (v : ℝ → ℝ) (a b : ℝ) : psi v a b = psi v b a := by simp [psi, add_comm]
private lemma interaction_symm (v : ℝ → ℝ) (p q r : ℝ) : interaction v p q r = interaction v r q p := by simp [interaction, add_comm, add_left_comm, add_assoc]
private lemma weight_symm (v : ℝ → ℝ) (p q r : ℝ) : weight v p q r = weight v r q p := by
  rw [weight, weight, interaction_symm v p q r, psi_symm v p q, psi_symm v q r]
  ring
private lemma psi_pos {v h g : ℝ → ℝ} {δ a b : ℝ} (H : CuspControl v h g δ) (ha : 0 < a) (hb : 0 < b) (hab : a+b ≤ δ) : 0 < psi v a b := by
  have hratio : 0 < b/a := div_pos hb ha
  have hlog : 0 < Real.log (1+b/a) := Real.log_pos (by linarith)
  exact (mul_pos (by positivity : 0 < a/4) hlog).trans_le (psi_lower H ha hb hab)
private lemma weight_pos {v h g : ℝ → ℝ} {δ p q r : ℝ} (H : CuspControl v h g δ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (hs : p+q+r ≤ δ) : 0 < weight v p q r := by
  have hI : 0 < interaction v p q r := (div_pos (mul_pos hp hr) (by positivity)).trans_le (interaction_crude H hp hq hr hs)
  have ha := psi_pos H hp hq (by linarith : p+q ≤ δ)
  have hb := psi_pos H hq hr (by linarith : q+r ≤ δ)
  have hv := v_pos H hq (by linarith : q ≤ δ)
  exact add_pos hI (div_pos (mul_pos ha hb) hv)
private lemma two_term_lower {a b A B Q T : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hA : a ≤ A) (hB : b ≤ B) (hQ : 0 < Q) (hT : Q ≤ T) : a*b/T ≤ A*B/Q := by
  have hT0 : 0 < T := hQ.trans_le hT
  exact (div_le_div_of_nonneg_left (mul_nonneg ha hb) hQ hT).trans (div_le_div_of_nonneg_right (mul_le_mul hA hB hb (ha.trans hA)) hQ.le)
private lemma regime_one {v h g : ℝ → ℝ} {δ p q r : ℝ} (H : CuspControl v h g δ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (hs : p+q+r ≤ δ) (hpr : p ≤ r) (hrq : r ≤ q) : v p * v r ≤ 64*q*(L q)^2 * weight v p q r := by
  let x := Real.log (q/p)
  let y := Real.log (q/r)
  let l := L q
  let U := (1+x)*(1+y)
  have hx : 0 ≤ x := Real.log_nonneg ((one_le_div hp).mpr (hpr.trans hrq))
  have hy : 0 ≤ y := Real.log_nonneg ((one_le_div hr).mpr hrq)
  have hl : 1 ≤ l := L_ge_one hq (by linarith : q ≤ δ) H.delta_small
  have ha := psi_lower_log H hp hq (by linarith) (hpr.trans hrq)
  have hb := psi_lower_log H hr hq (by linarith) hrq
  rw [psi_symm v r q] at hb
  have hQ := v_pos H hq (by linarith)
  have hQu := v_upper H hq (by linarith)
  have hprod := two_term_lower (by positivity : 0 ≤ p/8*(1+x)) (by positivity : 0 ≤ r/8*(1+y)) ha hb hQ hQu
  have hI := interaction_crude H hp hq hr hs
  have hI' : p*r/(64*q) ≤ interaction v p q r := by
    apply le_trans _ hI
    apply div_le_div_of_nonneg_left (mul_nonneg hp.le hr.le) (by positivity)
    linarith
  have hW : p*r/(64*q)*(1+U/l) ≤ weight v p q r := by
    have he : p*r/(64*q)*(U/l) = (p/8*(1+x))*(r/8*(1+y))/(q*l) := by dsimp [U]; ring
    rw [weight]
    calc
      p*r/(64*q)*(1+U/l) = p*r/(64*q) + p*r/(64*q)*(U/l) := by ring
      _ ≤ interaction v p q r + psi v p q * psi v q r / v q := by
        rw [he]
        exact add_le_add hI' hprod
  have hP := v_upper H hp (by linarith)
  have hR := v_upper H hr (by linarith)
  rw [L_split hp hq] at hP
  rw [L_split hr hq] at hR
  have hPR : v p * v r ≤ p*r*(l+x)*(l+y) := by
    have hsumpos : 0 ≤ L q + Real.log (q/p) := by
      rw [← L_split hp hq]
      linarith [L_ge_one hp (by linarith) H.delta_small]
    have hh := mul_le_mul hP hR (v_pos H hr (by linarith)).le (mul_nonneg hp.le hsumpos)
    convert hh using 1 <;> dsimp [l, x, y] <;> ring
  have hpoly : (l+x)*(l+y) ≤ l^2 + l*U := by
    dsimp [U]
    nlinarith [mul_nonneg hx hy, mul_nonneg (show 0 ≤ l-1 by linarith) (mul_nonneg hx hy)]
  have hm := mul_le_mul_of_nonneg_left hW (show 0 ≤ 64*q*l^2 by positivity)
  have he : 64*q*l^2*(p*r/(64*q)*(1+U/l)) = p*r*(l^2+l*U) := by
    have hl0 : l ≠ 0 := by linarith
    field_simp
  rw [he] at hm
  change v p * v r ≤ 64*q*l^2 * weight v p q r
  calc
    v p * v r ≤ p*r*(l+x)*(l+y) := hPR
    _ = p*r*((l+x)*(l+y)) := by ring
    _ ≤ p*r*(l^2+l*U) := mul_le_mul_of_nonneg_left hpoly (mul_nonneg hp.le hr.le)
    _ ≤ 64*q*l^2 * weight v p q r := hm
private lemma regime_two {v h g : ℝ → ℝ} {δ p q r : ℝ} (H : CuspControl v h g δ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (hs : p+q+r ≤ δ) (hqp : q ≤ p) (hpr : p ≤ r) : v p * v r ≤ 64*r*(L r)^2 * weight v p q r := by
  let y := Real.log (r/p)
  let l := L r
  have hy : 0 ≤ y := Real.log_nonneg ((one_le_div hp).mpr hpr)
  have hl : 1 ≤ l := L_ge_one hr (by linarith : r ≤ δ) H.delta_small
  have hi := interaction_long H hp hq hr hs (le_max_left _ _) (by simpa [max_eq_left hqp] using hpr)
  rw [max_eq_left hqp] at hi
  have hW : p/12*(1+y) ≤ weight v p q r := by
    dsimp [weight]
    apply hi.trans (le_add_of_nonneg_right _)
    exact (div_pos (mul_pos (psi_pos H hp hq (by linarith)) (psi_pos H hq hr (by linarith))) (v_pos H hq (by linarith))).le
  have hP := v_upper H hp (by linarith)
  have hR := v_upper H hr (by linarith)
  rw [L_split hp hr] at hP
  have hPR : v p * v r ≤ p*r*l*(l+y) := by
    have hsumpos : 0 ≤ L r + Real.log (r/p) := by
      rw [← L_split hp hr]
      linarith [L_ge_one hp (by linarith) H.delta_small]
    have hh := mul_le_mul hP hR (v_pos H hr (by linarith)).le (mul_nonneg hp.le hsumpos)
    convert hh using 1 <;> dsimp [l,y] <;> ring
  have hpoly : l+y ≤ l*(1+y) := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hW (show 0 ≤ 12*r*l^2 by positivity)
  have he : 12*r*l^2*(p/12*(1+y)) = p*r*l*(l*(1+y)) := by ring
  rw [he] at hm
  have h12 : v p * v r ≤ 12*r*l^2 * weight v p q r := (hPR.trans (mul_le_mul_of_nonneg_left hpoly (by positivity))).trans hm
  exact h12.trans (mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg l]) (weight_pos H hp hq hr hs).le)
private lemma regime_three {v h g : ℝ → ℝ} {δ p q r : ℝ} (H : CuspControl v h g δ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (hs : p+q+r ≤ δ) (hpq : p ≤ q) (hqr : q ≤ r) : v p * v r ≤ 64*r*(L r)^2 * weight v p q r := by
  let x := Real.log (q/p)
  let y := Real.log (r/q)
  let l := L r
  let Z := l+y
  have hx : 0 ≤ x := Real.log_nonneg ((one_le_div hp).mpr hpq)
  have hy : 0 ≤ y := Real.log_nonneg ((one_le_div hq).mpr hqr)
  have hl : 1 ≤ l := L_ge_one hr (by linarith : r ≤ δ) H.delta_small
  have hZ : 0 < Z := by dsimp [Z]; linarith
  have hLq : L q = Z := L_split hq hr
  have hLp : L p = Z+x := by rw [L_split hp hq, hLq]
  have ha := psi_lower_log H hp hq (by linarith) hpq
  have hb := psi_lower_log H hq hr (by linarith) hqr
  have hQu := v_upper H hq (by linarith)
  rw [hLq] at hQu
  have hprod := two_term_lower (by positivity : 0 ≤ p/8*(1+x)) (by positivity : 0 ≤ q/8*(1+y)) ha hb (v_pos H hq (by linarith)) hQu
  have hi := interaction_long H hp hq hr hs (le_max_left _ _) (by simpa [max_eq_right hpq] using hqr)
  rw [max_eq_right hpq] at hi
  have hW : p/64*(1+y)*(1+(1+x)/Z) ≤ weight v p q r := by
    have hi' : p/64*(1+y) ≤ interaction v p q r := by exact (by nlinarith : p/64*(1+y) ≤ p/12*(1+y)).trans hi
    have he : p/64*(1+y)*((1+x)/Z) = (p/8*(1+x))*(q/8*(1+y))/(q*Z) := by field_simp; ring
    calc
      p/64*(1+y)*(1+(1+x)/Z) = p/64*(1+y) + p/64*(1+y)*((1+x)/Z) := by ring
      _ ≤ weight v p q r := by
        rw [he, weight]
        exact add_le_add hi' hprod
  have hP := v_upper H hp (by linarith)
  have hR := v_upper H hr (by linarith)
  rw [hLp] at hP
  have hPR : v p * v r ≤ p*r*l*(Z+x) := by
    have hh := mul_le_mul hP hR (v_pos H hr (by linarith)).le (by positivity)
    convert hh using 1 <;> dsimp [l] <;> ring
  have hZle : Z ≤ l*(1+y) := by dsimp [Z]; nlinarith
  have hrat : Z+x ≤ Z*(1+(1+x)/Z) := by
    have he : Z*(1+(1+x)/Z) = Z+1+x := by field_simp; ring
    rw [he]; linarith
  have hm := mul_le_mul_of_nonneg_left hW (show 0 ≤ 64*r*l^2 by positivity)
  have he : 64*r*l^2*(p/64*(1+y)*(1+(1+x)/Z)) = p*r*l*(l*(1+y))*(1+(1+x)/Z) := by ring
  rw [he] at hm
  change v p * v r ≤ 64*r*l^2 * weight v p q r
  apply le_trans hPR
  apply le_trans _ hm
  have h1 := mul_le_mul_of_nonneg_left hrat (show 0 ≤ p*r*l by positivity)
  have h2 := mul_le_mul_of_nonneg_right hZle (show 0 ≤ 1+(1+x)/Z by positivity)
  have h3 := mul_le_mul_of_nonneg_left h2 (show 0 ≤ p*r*l by positivity)
  nlinarith
private lemma max_scale {m s : ℝ} (hm : 0 < m) (hs : 0 < s) (hms : m ≤ s) (hsm : s ≤ 3*m) (hs1 : 1 ≤ L s) : m*(L m)^2 ≤ (1+Real.log 3)^2*s*(L s)^2 := by
  have hlog3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hlog := Real.log_le_log (div_pos hs hm) ((div_le_iff₀ hm).mpr hsm)
  have hLm : L m ≤ (1+Real.log 3)*L s := by
    rw [L_split hm hs]
    nlinarith
  have hLm0 : 0 ≤ L m := by
    rw [L_split hm hs]
    have hh := Real.log_nonneg ((one_le_div hm).mpr hms)
    linarith
  have hsquare : (L m)^2 ≤ ((1+Real.log 3)*L s)^2 := by nlinarith
  calc
    m*(L m)^2 ≤ s*(L m)^2 := mul_le_mul_of_nonneg_right hms (sq_nonneg _)
    _ ≤ s*((1+Real.log 3)*L s)^2 := mul_le_mul_of_nonneg_left hsquare hs.le
    _ = (1+Real.log 3)^2*s*(L s)^2 := by ring

/-- The uniform endpoint error bound, with no restriction on any ratio of the three gaps.
This is the analytic lemma (11), not yet the four-point precision criterion. -/
theorem uniform_outer_deficit_bound {v h g : ℝ → ℝ} {δ : ℝ} (H : CuspControl v h g δ) {p q r : ℝ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (hs : p+q+r ≤ δ) : v p * v r ≤ (64*(1+Real.log 3)^2) * (p+q+r) * (L (p+q+r))^2 * weight v p q r := by
  have hs0 : 0 < p+q+r := by positivity
  have hLs : 1 ≤ L (p+q+r) := L_ge_one hs0 hs H.delta_small
  have ordered (p q r : ℝ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (hs : p+q+r ≤ δ) (hpr : p ≤ r) : v p * v r ≤ (64*(1+Real.log 3)^2)*(p+q+r)*(L (p+q+r))^2*weight v p q r := by
    have hs0 : 0 < p+q+r := by positivity
    have hLs : 1 ≤ L (p+q+r) := L_ge_one hs0 hs H.delta_small
    have lift (m : ℝ) (hm : 0 < m) (hms : m ≤ p+q+r) (hsm : p+q+r ≤ 3*m) (hlocal : v p*v r ≤ 64*m*(L m)^2*weight v p q r) : v p*v r ≤ (64*(1+Real.log 3)^2)*(p+q+r)*(L (p+q+r))^2*weight v p q r := by
      have hh := mul_le_mul_of_nonneg_right (max_scale hm hs0 hms hsm hLs) (show 0 ≤ 64*weight v p q r by
          have hw := weight_pos H hp hq hr hs
          positivity)
      apply hlocal.trans
      convert hh using 1 <;> ring
    by_cases hrq : r ≤ q
    · exact lift q hq (by linarith) (by linarith) (regime_one H hp hq hr hs hpr hrq)
    · have hqr : q ≤ r := le_of_not_ge hrq
      by_cases hqp : q ≤ p
      · exact lift r hr (by linarith) (by linarith) (regime_two H hp hq hr hs hqp hpr)
      · have hpq : p ≤ q := le_of_not_ge hqp
        exact lift r hr (by linarith) (by linarith) (regime_three H hp hq hr hs hpq hqr)
  by_cases hpr : p ≤ r
  · exact ordered p q r hp hq hr hs hpr
  · have h := ordered r q p hr hq hp (by linarith) (le_of_not_ge hpr)
    simpa only [weight_symm v r q p, show r+q+p = p+q+r by ring, mul_comm (v r) (v p)] using h
private lemma shifted_h_integrable {v h g : ℝ → ℝ} {δ a b : ℝ} (H : CuspControl v h g δ) (ha : 0 < a) (hb : 0 < b) (hab : a+b ≤ δ) : IntervalIntegrable (fun u => h (a+u)) volume 0 b := by
  apply ContinuousOn.intervalIntegrable_of_Icc hb.le
  intro u hu
  exact ((H.deriv_h (a+u) ⟨by linarith [hu.1, ha], by linarith [hu.2, hab]⟩).continuousAt.comp (show ContinuousAt (fun u : ℝ => a+u) u by fun_prop)).continuousWithinAt
private lemma shifted_v_integral {v h g : ℝ → ℝ} {δ a b : ℝ} (H : CuspControl v h g δ) (ha : 0 < a) (hb : 0 < b) (hab : a+b ≤ δ) : (∫ u in (0 : ℝ)..b, h (a+u)) = v (a+b) - v a := by
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun u => v (a+u)) (f' := fun u => h (a+u)) (fun u hu => by
      rw [uIcc_of_le hb.le] at hu
      convert! (H.deriv_v (a+u) ⟨by linarith [hu.1, ha], by linarith [hu.2, hab]⟩).comp u ((hasDerivAt_id u).const_add a) using 1 <;> simp [Function.comp_def])
    (shifted_h_integrable H ha hb hab)
  simpa only [add_zero] using hh
private lemma shifted_g_integral {v h g : ℝ → ℝ} {δ a b : ℝ} (H : CuspControl v h g δ) (ha : 0 < a) (hb : 0 < b) (hab : a+b ≤ δ) : IntervalIntegrable (fun u => g (a+u)) volume 0 b ∧ (∫ u in (0 : ℝ)..b, g (a+u)) = h a - h (a+b) := by
  have hc : ContinuousOn (fun u => g (a+u)) (Icc 0 b) := by
    apply H.continuous_g.comp (by fun_prop)
    intro u hu
    exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hi := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hb.le hc
  refine ⟨hi, ?_⟩
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun u => -h (a+u)) (f' := fun u => g (a+u)) (fun u hu => by
      rw [uIcc_of_le hb.le] at hu
      convert! ((H.deriv_h (a+u) ⟨by linarith [hu.1], by linarith [hu.2]⟩).neg).comp u ((hasDerivAt_id u).const_add a) using 1 <;> simp [Function.comp_def]) hi
  simpa [sub_eq_add_neg, add_comm] using hh

/-- The exact two iterated integrals, with the singular corner paid by integrability.
The inner integral at the single point u=0 is immaterial for the outer integral. -/
theorem deficit_integrals {v h g : ℝ → ℝ} {δ p q r : ℝ} (H : CuspControl v h g δ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (hs : p+q+r ≤ δ) : (IntervalIntegrable (fun u => ∫ w in (0 : ℝ)..q, g (u+w)) volume 0 p ∧ psi v p q = ∫ u in (0 : ℝ)..p, ∫ w in (0 : ℝ)..q, g (u+w)) ∧
    (IntervalIntegrable (fun u => ∫ w in (0 : ℝ)..r, g (q+u+w)) volume 0 p ∧ interaction v p q r = ∫ u in (0 : ℝ)..p, ∫ w in (0 : ℝ)..r, g (q+u+w)) := by
  have hhi := h_integrable H hp (by linarith : p ≤ δ)
  have hsi := shifted_h_integrable H hq hp (by linarith : q+p ≤ δ)
  have hshift : (fun u => h (u+q)) = (fun u => h (q+u)) := by funext u; rw [add_comm]
  have hpsi : IntervalIntegrable (fun u => h u-h (u+q)) volume 0 p := by exact hhi.sub (hshift ▸ hsi)
  have hinner : (fun u => h u-h (u+q)) =ᵐ[volume.restrict (Ι (0 : ℝ) p)] (fun u => ∫ w in (0 : ℝ)..q, g (u+w)) := by
    rw [uIoc_of_le hp.le]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    exact (shifted_g_integral H hu.1 hq (by linarith [hu.2])).2.symm
  have hmix1 := shifted_h_integrable H hq hp (by linarith : q+p ≤ δ)
  have hmix2 := shifted_h_integrable H (by positivity : 0 < q+r) hp (by linarith : q+r+p ≤ δ)
  have hmix : IntervalIntegrable (fun u => h (q+u)-h (q+u+r)) volume 0 p := by
    convert hmix1.sub hmix2 using 1
    funext u; congr 1; congr 1; ring
  have hinner' : (fun u => h (q+u)-h (q+u+r)) =ᵐ[volume.restrict (Ι (0 : ℝ) p)] (fun u => ∫ w in (0 : ℝ)..r, g (q+u+w)) := by
    rw [uIoc_of_le hp.le]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    exact (shifted_g_integral H (by linarith [hu.1] : 0 < q+u) hr (by linarith [hu.2] : q+u+r ≤ δ)).2.symm
  refine ⟨⟨hpsi.congr_ae hinner, ?_⟩, ⟨hmix.congr_ae hinner', ?_⟩⟩
  · rw [← intervalIntegral.integral_congr_ae_restrict hinner,
      intervalIntegral.integral_sub hhi (by rw [hshift]; exact hsi),
      v_integral H hp (by linarith)]
    have he := shifted_v_integral H hq hp (by linarith : q+p ≤ δ)
    rw [hshift, he]
    dsimp [psi]; rw [add_comm q p]; ring
  · rw [← intervalIntegral.integral_congr_ae_restrict hinner',
      intervalIntegral.integral_sub hmix1 (by convert hmix2 using 1; funext u; congr 1; ring),
      shifted_v_integral H hq hp (by linarith)]
    have he : (∫ u in (0 : ℝ)..p, h (q+u+r)) = v (q+r+p)-v (q+r) := by
      convert shifted_v_integral H (by positivity : 0 < q+r) hp (by linarith : q+r+p ≤ δ) using 1
      congr 1; funext u; congr 1; ring
    rw [he]
    dsimp [interaction]
    rw [show q+p = p+q by ring, show q+r+p = p+q+r by ring]
    ring

/-- Transfer a complex positive quadratic form to the real coefficient subspace. -/
theorem real_posDef_of_complex {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : Matrix.PosDef (fun i j => (A i j : ℂ))) : A.PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext i j
    have hh := congrArg Complex.re (congrFun (congrFun hA.isHermitian i) j)
    change (star (A j i : ℂ)).re = A i j at hh
    simpa using hh
  · intro c hc
    let z : Fin n → ℂ := fun i => (c i : ℂ)
    have hz : z ≠ 0 := by
      intro he
      apply hc
      funext i
      have hh := congrArg Complex.re (congrFun he i)
      simpa [z] using hh
    have hh := hA.dotProduct_mulVec_pos hz
    have he : star z ⬝ᵥ ((fun i j => (A i j : ℂ)) *ᵥ z) = ((star c ⬝ᵥ (A *ᵥ c) : ℝ) : ℂ) := by simp [z, dotProduct, mulVec, ← Complex.ofReal_mul, ← Complex.ofReal_sum]
    rw [he] at hh
    exact Complex.zero_lt_real.mp hh

/-- The off-diagonal entry after conditioning on a symmetric two-point covariance. -/
def schurCross (k d a b c e f : ℝ) : ℝ := f - (k*(a*c+b*e)-d*(a*e+b*c))/(k^2-d^2)

theorem schurCross_eq_matrix (k d a b c e f : ℝ) : schurCross k d a b c e f = f - ( (!![a,b] : Matrix (Fin 1) (Fin 2) ℝ) * (!![k,d;d,k])⁻¹ * (!![c;e] : Matrix (Fin 2) (Fin 1) ℝ)) 0 0 := by
  simp [schurCross, Matrix.inv_def, Ring.inverse_eq_inv, Matrix.adjugate_fin_two, Matrix.det_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  ring
private lemma distance_two_identity (k P Q V alpha beta U : ℝ) (hV : V ≠ 0) (hden : 2*k-V ≠ 0) : schurCross k (k-V) (k-P) (k-(P+V-U)) (k-Q) (k-(V-Q+beta)) (k-(P+Q-alpha)) = alpha - Q/V*U + (k*U/V-P)*beta/(2*k-V) := by
  have hd : k^2-(k-V)^2 ≠ 0 := by
    rw [show k^2-(k-V)^2 = V*(2*k-V) by ring]
    exact mul_ne_zero hV hden
  unfold schurCross
  rw [show k^2-(k-V)^2 = V*(2*k-V) by ring]
  have hden' : k*2-V ≠ 0 := by simpa only [mul_comm] using hden
  field_simp [hV, hden, hden'] <;> ring

/-- A symmetric four-point covariance, in the order of three positive consecutive gaps. -/
def gapGram (v : ℝ → ℝ) (k p q r : ℝ) : Matrix (Fin 4) (Fin 4) ℝ := !![k, k-v p, k-v (p+q), k-v (p+q+r); k-v p, k, k-v q, k-v (q+r); k-v (p+q), k-v q, k, k-v r; k-v (p+q+r), k-v (q+r), k-v r, k]
private lemma four_adjugate_crosses (k a b c d e f : ℝ) (ha : k^2-a^2 ≠ 0) (hb : k^2-b^2 ≠ 0) (hc : k^2-c^2 ≠ 0) (hd : k^2-d^2 ≠ 0) (he : k^2-e^2 ≠ 0) (hf : k^2-f^2 ≠ 0) : let A : Matrix (Fin 4) (Fin 4) ℝ := !![k,a,b,f; a,k,c,d; b,c,k,e; f,d,e,k]
    A.adjugate 0 1 = -(k^2-e^2)*schurCross k e b f c d a ∧
    A.adjugate 0 2 = -(k^2-d^2)*schurCross k d a f c e b ∧
    A.adjugate 0 3 = -(k^2-c^2)*schurCross k c a b d e f ∧
    A.adjugate 1 2 = -(k^2-f^2)*schurCross k f a d b e c ∧
    A.adjugate 1 3 = -(k^2-b^2)*schurCross k b a c f e d ∧
    A.adjugate 2 3 = -(k^2-a^2)*schurCross k a b c f d e := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals rw [Matrix.adjugate_fin_succ_eq_det_submatrix, Matrix.det_fin_three]
  all_goals rw [schurCross_eq_matrix]
  all_goals simp [Matrix.submatrix, Fin.succAbove, Fin.lt_def, Matrix.inv_def, Ring.inverse_eq_inv, Matrix.adjugate_fin_two, Matrix.det_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals field_simp
  all_goals ring
set_option maxHeartbeats 2000000 in
private lemma four_inverse_neg (k a b c d e f : ℝ) (hA : Matrix.PosDef (!![k,a,b,f; a,k,c,d; b,c,k,e; f,d,e,k] : Matrix (Fin 4) (Fin 4) ℝ)) (ha : 0 < k^2-a^2) (hb : 0 < k^2-b^2) (hc : 0 < k^2-c^2) (hd : 0 < k^2-d^2) (he : 0 < k^2-e^2) (hf : 0 < k^2-f^2)
    (h01 : 0 < schurCross k e b f c d a)
    (h02 : 0 < schurCross k d a f c e b)
    (h03 : 0 < schurCross k c a b d e f)
    (h12 : 0 < schurCross k f a d b e c)
    (h13 : 0 < schurCross k b a c f e d)
    (h23 : 0 < schurCross k a b c f d e) :
    ∀ i j : Fin 4, i ≠ j → ((!![k,a,b,f; a,k,c,d; b,c,k,e; f,d,e,k] : Matrix (Fin 4) (Fin 4) ℝ)⁻¹) i j < 0 := by
  let A : Matrix (Fin 4) (Fin 4) ℝ := !![k,a,b,f; a,k,c,d; b,c,k,e; f,d,e,k]
  obtain ⟨e01,e02,e03,e12,e13,e23⟩ := four_adjugate_crosses k a b c d e f ha.ne' hb.ne' hc.ne' hd.ne' he.ne' hf.ne'
  have hdet : 0 < A.det := hA.det_pos
  have neg_entry (i j : Fin 4) (hentry : A.adjugate i j < 0) : A⁻¹ i j < 0 := by
    rw [Matrix.inv_def, Ring.inverse_eq_inv]
    change A.det⁻¹*A.adjugate i j < 0
    exact mul_neg_of_pos_of_neg (inv_pos.mpr hdet) hentry
  have n01 : A⁻¹ 0 1 < 0 := neg_entry 0 1 (by rw [e01]; nlinarith [mul_pos he h01])
  have n02 : A⁻¹ 0 2 < 0 := neg_entry 0 2 (by rw [e02]; nlinarith [mul_pos hd h02])
  have n03 : A⁻¹ 0 3 < 0 := neg_entry 0 3 (by rw [e03]; nlinarith [mul_pos hc h03])
  have n12 : A⁻¹ 1 2 < 0 := neg_entry 1 2 (by rw [e12]; nlinarith [mul_pos hf h12])
  have n13 : A⁻¹ 1 3 < 0 := neg_entry 1 3 (by rw [e13]; nlinarith [mul_pos hb h13])
  have n23 : A⁻¹ 2 3 < 0 := neg_entry 2 3 (by rw [e23]; nlinarith [mul_pos ha h23])
  have hu (i j : Fin 4) (hij : i < j) : A⁻¹ i j < 0 := by fin_cases i <;> fin_cases j <;> norm_num at hij <;> assumption
  have hsym (i j : Fin 4) : A⁻¹ i j = A⁻¹ j i := by
    have hh := congrFun (congrFun hA.inv.isHermitian j) i
    change star (A⁻¹ i j) = A⁻¹ j i at hh
    simpa only [star_trivial] using hh
  intro i j hij
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact hu i j hlt
  · rw [show ( (!![k,a,b,f; a,k,c,d; b,c,k,e; f,d,e,k] : Matrix (Fin 4) (Fin 4) ℝ)⁻¹) i j = A⁻¹ j i from hsym i j]
    exact hu j i hgt
private lemma gapGram_nodes {v : ℝ → ℝ} {k p q r : ℝ} (hv : v 0 = 0) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) : gapGram v k p q r = (fun i j => k-v |(![0,p,p+q,p+q+r] : Fin 4 → ℝ) i - (![0,p,p+q,p+q+r] : Fin 4 → ℝ) j|) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gapGram, hv]
  all_goals congr 1
  all_goals congr 1
  all_goals first | rw [abs_of_nonneg (by linarith)] | rw [abs_of_nonpos (by linarith)]
  all_goals ring
private lemma sorted_gapGram {v : ℝ → ℝ} {k : ℝ} {x : Fin 4 → ℝ} (hv : v 0 = 0) (hx : StrictMono x) : (fun i j => k-v |x i-x j|) = gapGram v k (x 1-x 0) (x 2-x 1) (x 3-x 2) := by
  have h01 := hx (by norm_num : (0 : Fin 4) < 1)
  have h12 := hx (by norm_num : (1 : Fin 4) < 2)
  have h23 := hx (by norm_num : (2 : Fin 4) < 3)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gapGram, hv]
  all_goals congr 1
  all_goals congr 1
  all_goals first | rw [abs_of_nonneg (by linarith)] | rw [abs_of_nonpos (by linarith)]
  all_goals ring
private lemma endpoint_identity (k P Q R alpha beta I : ℝ) (hQ : Q ≠ 0) (hden : 2*k-Q ≠ 0) : (2*k-Q)*schurCross k (k-Q) (k-P) (k-(P+Q-alpha)) (k-(Q+R-beta)) (k-R) (k-(P+Q+R-alpha-beta-I)) = (2*k-Q)*I + k*alpha*beta/Q - (P*R+(P-alpha)*(R-beta)) := by
  have hd : k^2-(k-Q)^2 ≠ 0 := by
    rw [show k^2-(k-Q)^2 = Q*(2*k-Q) by ring]
    exact mul_ne_zero hQ hden
  unfold schurCross
  field_simp
  <;> ring
private lemma scale_limit : Tendsto (fun t : ℝ => t*(L t)^2) (𝓝[>] 0) (𝓝 0) := by
  have h2 := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero).comp tendsto_inv_nhdsGT_zero
  have h1 := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp tendsto_inv_nhdsGT_zero
  have ht : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have h := (h2.add (h1.const_mul 2)).add ht
  have heq : ((fun t : ℝ => Real.log (t⁻¹)^2/(1*t⁻¹+0) + 2*(Real.log (t⁻¹)^1/(1*t⁻¹+0)) + t)) =ᶠ[𝓝[>] 0] (fun t => t*(L t)^2) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    change 0 < t at ht
    rw [L_eq ht]
    simp [one_div, div_eq_mul_inv]
    ring
  simpa using h.congr' heq

/-- The uniform endpoint Schur sign follows from the cusp estimates in every gap regime.
This supplies the endpoint sign consumed by the six-sign criterion below. -/
theorem exists_uniform_endpoint_cross_pos {v h g : ℝ → ℝ} {δ₀ k : ℝ} (H : CuspControl v h g δ₀) (hk : 0 < k) : ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ₀ ∧ ∀ p q r : ℝ, 0 < p → 0 < q → 0 < r → p+q+r ≤ δ → 0 < schurCross k (k-v q) (k-v p) (k-v (p+q)) (k-v (q+r)) (k-v r) (k-v (p+q+r)) := by
  let B := 64*(1+Real.log 3)^2
  have hsmall : ∀ᶠ t : ℝ in 𝓝[>] 0, 2*B*t*(L t)^2 < k := by
    have hlim : Tendsto (fun t : ℝ => (2*B)*(t*(L t)^2)) (𝓝[>] 0) (𝓝 0) := by simpa using scale_limit.const_mul (2*B)
    have hh := hlim.eventually (Iio_mem_nhds hk)
    simpa only [mul_zero, mul_assoc] using hh
  have hv : ∀ᶠ t : ℝ in 𝓝[>] 0, v t < k := by
    have hlim : Tendsto v (𝓝[>] 0) (𝓝 0) := by
      simpa only [H.zero] using (H.continuous.continuousAt (x := 0)).tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
    exact hlim.eventually (Iio_mem_nhds hk)
  have hδ₀ : ∀ᶠ t : ℝ in 𝓝[>] 0, t < δ₀ := Filter.Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds H.delta_pos)
  obtain ⟨δ, hδ, hall⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp (hδ₀.and (hv.and hsmall))
  refine ⟨δ, hδ, (hall ⟨hδ, le_rfl⟩).1.le, ?_⟩
  intro p q r hp hq hr hs
  have hs₀ : p+q+r ≤ δ₀ := hs.trans (hall ⟨hδ, le_rfl⟩).1.le
  have hQ := v_pos H hq (by linarith : q ≤ δ₀)
  have hQk := (hall (show q ∈ Ioc 0 δ from ⟨hq, by linarith⟩)).2.1
  have hden : 0 < 2*k-v q := by linarith
  have hI := interaction_crude H hp hq hr hs₀
  have hI0 : 0 < interaction v p q r := (div_pos (mul_pos hp hr) (by positivity)).trans_le hI
  have hW := weight_pos H hp hq hr hs₀
  have hPR := uniform_outer_deficit_bound H hp hq hr hs₀
  change v p*v r ≤ B*(p+q+r)*(L (p+q+r))^2*weight v p q r at hPR
  have herror := (hall (show p+q+r ∈ Ioc 0 δ from ⟨by positivity, hs⟩)).2.2
  have hgood : 0 < k*weight v p q r - 2*(v p*v r) := by
    have hh := mul_pos (sub_pos.mpr herror) hW
    nlinarith
  have hD0 : 0 < v (p+q)-v q := by
    have hh := v_strictMono H (show q ∈ Icc 0 δ₀ from ⟨hq.le, by linarith⟩) (show p+q ∈ Icc 0 δ₀ from ⟨by positivity, by linarith⟩) (by linarith : q < p+q)
    linarith
  have hE0 : 0 < v (q+r)-v q := by
    have hh := v_strictMono H (show q ∈ Icc 0 δ₀ from ⟨hq.le, by linarith⟩) (show q+r ∈ Icc 0 δ₀ from ⟨by positivity, by linarith⟩) (by linarith : q < q+r)
    linarith
  have ha := psi_pos H hp hq (by linarith)
  have hb := psi_pos H hq hr (by linarith)
  have hD : v (p+q)-v q < v p := by dsimp [psi] at ha; linarith
  have hE : v (q+r)-v q < v r := by dsimp [psi] at hb; linarith
  have hDE : (v (p+q)-v q)*(v (q+r)-v q) < v p*v r := by
    have hR0 := v_pos H hr (by linarith : r ≤ δ₀)
    have h₁ := mul_pos (sub_pos.mpr hD) hR0
    have h₂ := mul_pos hD0 (sub_pos.mpr hE)
    nlinarith
  have hid := endpoint_identity k (v p) (v q) (v r) (psi v p q) (psi v q r) (interaction v p q r) hQ.ne' hden.ne'
  have he1 : v p+v q-psi v p q = v (p+q) := by dsimp [psi]; ring
  have he2 : v q+v r-psi v q r = v (q+r) := by dsimp [psi]; ring
  have he3 : v p+v q+v r-psi v p q-psi v q r-interaction v p q r = v (p+q+r) := by dsimp [psi, interaction]; ring
  rw [he1, he2, he3] at hid
  have hWexp : k*weight v p q r = k*interaction v p q r + k*psi v p q*psi v q r/v q := by dsimp [weight]; ring
  rw [hWexp] at hgood
  have hextra : 0 < (k-v q)*interaction v p q r := mul_pos (sub_pos.mpr hQk) hI0
  have hpositive : 0 < (2*k-v q)*schurCross k (k-v q) (k-v p) (k-v (p+q)) (k-v (q+r)) (k-v r) (k-v (p+q+r)) := by
    rw [hid]
    dsimp [psi]
    dsimp [psi] at hgood
    nlinarith
  exact (mul_pos_iff_of_pos_left hden).mp hpositive
private lemma h_ratio_strictMono {v h g : ℝ → ℝ} {δ p : ℝ} (H : CuspControl v h g δ) (hlog : StrictConvexOn ℝ (Ioo 0 δ) (fun u => Real.log (h u))) (hp : 0 < p) : StrictMonoOn (fun u => h (p+u)/h u) (Ioc 0 (δ-p)) := by
  have hdlog (u : ℝ) (hu : u ∈ Ioo 0 δ) : HasDerivAt (fun t => Real.log (h t)) (-g u/h u) u := (H.deriv_h u ⟨hu.1, hu.2.le⟩).log (H.h_pos u ⟨hu.1, hu.2.le⟩).ne'
  have hmono := hlog.strictMonoOn_deriv (fun u hu => (hdlog u hu).differentiableAt)
  have hd (u : ℝ) (hu : u ∈ Ioc 0 (δ-p)) : HasDerivAt (fun u => h (p+u)/h u) ((-g (p+u)*h u-h (p+u)*(-g u))/(h u)^2) u := by
    convert ((H.deriv_h (p+u) ⟨by linarith [hu.1], by linarith [hu.2]⟩).comp u ((hasDerivAt_id u).const_add p)).div (H.deriv_h u ⟨hu.1, by linarith [hu.2]⟩) (H.h_pos u ⟨hu.1, by linarith [hu.2]⟩).ne' using 1
    · ext t
      simp [Function.comp_def]
    · simp
  apply strictMonoOn_of_deriv_pos (convex_Ioc 0 (δ-p)) (fun u hu => (hd u hu).continuousAt.continuousWithinAt)
  intro u hu
  rw [interior_Ioc] at hu
  have huδ : u ∈ Ioo 0 δ := ⟨hu.1, by linarith [hu.2]⟩
  have hpuδ : p+u ∈ Ioo 0 δ := ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hh := hmono huδ hpuδ (by linarith : u < p+u)
  rw [(hdlog u huδ).deriv, (hdlog (p+u) hpuδ).deriv] at hh
  rw [(hd u ⟨hu.1, hu.2.le⟩).deriv]
  have hh' := (div_lt_div_iff₀ (H.h_pos u ⟨huδ.1, huδ.2.le⟩) (H.h_pos (p+u) ⟨hpuδ.1, hpuδ.2.le⟩)).mp hh
  apply div_pos _ (sq_pos_of_pos (H.h_pos u ⟨huδ.1, huδ.2.le⟩))
  nlinarith
private lemma weighted_ratio_integral_pos {v h g : ℝ → ℝ} {δ p t : ℝ} (H : CuspControl v h g δ) (hlog : StrictConvexOn ℝ (Ioo 0 δ) (fun u => Real.log (h u))) (hp : 0 < p) (ht : 0 < t) (hpt : p+t ≤ δ) : 0 < h (p+t)*v t-h t*(v (p+t)-v p) := by
  let f : ℝ → ℝ := fun u => h (p+t)*h u - h t*h (p+u)
  have hi : IntervalIntegrable f volume 0 t := ((h_integrable H ht (by linarith)).const_mul (h (p+t))).sub ((shifted_h_integrable H hp ht hpt).const_mul (h t))
  have hm := h_ratio_strictMono H hlog hp
  have hnonneg (u : ℝ) (hu : u ∈ Ioc 0 t) : 0 ≤ f u := by
    have hh := hm.monotoneOn ⟨hu.1, by linarith [hu.2]⟩ ⟨ht, by linarith⟩ hu.2
    have hh' := (div_le_div_iff₀ (H.h_pos u ⟨hu.1, by linarith [hu.2]⟩) (H.h_pos t ⟨ht, by linarith⟩)).mp hh
    dsimp [f]; nlinarith
  have hpos (u : ℝ) (hu : u ∈ Ioo 0 t) : 0 < f u := by
    have hh := hm ⟨hu.1, by linarith [hu.2]⟩ ⟨ht, by linarith⟩ hu.2
    have hh' := (div_lt_div_iff₀ (H.h_pos u ⟨hu.1, by linarith [hu.2]⟩) (H.h_pos t ⟨ht, by linarith⟩)).mp hh
    dsimp [f]; nlinarith
  have hae : 0 ≤ᵐ[volume.restrict (Ι (0 : ℝ) t)] f := by
    rw [uIoc_of_le ht.le]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu using hnonneg u hu
  have hsupp : Ioo (0 : ℝ) t ⊆ Function.support f ∩ Ioc 0 t := by
    intro u hu
    exact ⟨(hpos u hu).ne', hu.1, hu.2.le⟩
  have hmeasure : 0 < volume (Function.support f ∩ Ioc 0 t) := by
    apply lt_of_lt_of_le _ (measure_mono hsupp)
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_pos.mpr (by simpa using ht)
  have hh := (intervalIntegral.integral_pos_iff_support_of_nonneg_ae' hae hi).mpr ⟨ht, hmeasure⟩
  rw [intervalIntegral.integral_sub ((h_integrable H ht (by linarith)).const_mul (h (p+t))) ((shifted_h_integrable H hp ht hpt).const_mul (h t)), intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    v_integral H ht (by linarith), shifted_v_integral H hp ht hpt] at hh
  exact hh

/-- Strict log convexity of h implies the weighted deficit ratio is strictly decreasing.
Its denominator and improper integral are proved positive and integrable. -/
theorem strictAntiOn_deficit_ratio {v h g : ℝ → ℝ} {δ p : ℝ} (H : CuspControl v h g δ) (hlog : StrictConvexOn ℝ (Ioo 0 δ) (fun u => Real.log (h u))) (hp : 0 < p) : StrictAntiOn (fun t => psi v p t/v t) (Ioc 0 (δ-p)) := by
  have hd (t : ℝ) (ht : t ∈ Ioc 0 (δ-p)) : HasDerivAt (fun t => psi v p t/v t) (((h t-h (p+t))*v t-psi v p t*h t)/(v t)^2) t := by
    have h₁ := H.deriv_v t ⟨ht.1, by linarith [ht.2]⟩
    have h₂ := (H.deriv_v (p+t) ⟨by linarith [ht.1], by linarith [ht.2]⟩).comp t ((hasDerivAt_id t).const_add p)
    convert (((hasDerivAt_const t (v p)).add h₁).sub h₂).div h₁ (v_pos H ht.1 (by linarith [ht.2])).ne' using 1
    · rfl
    · simp [psi]
  apply strictAntiOn_of_deriv_neg (convex_Ioc 0 (δ-p)) (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
  intro t ht
  rw [interior_Ioc] at ht
  rw [(hd t ⟨ht.1, ht.2.le⟩).deriv]
  have hn := weighted_ratio_integral_pos H hlog hp ht.1 (by linarith [ht.2])
  apply div_neg_of_neg_of_pos _ (sq_pos_of_pos (v_pos H ht.1 (by linarith [ht.2])))
  dsimp [psi]
  nlinarith
private lemma three_point {v h g : ℝ → ℝ} {δ k a b : ℝ} (H : CuspControl v h g δ) (hk : 0 < k) (hpositive : ∀ t ∈ Icc 0 δ, 0 < k-v t) (hlog : StrictConvexOn ℝ (Icc 0 δ) (fun t => Real.log (k-v t))) (ha : 0 < a) (hb : 0 < b) (hab : a+b ≤ δ) : v a * v b < k*psi v a b := by
  let s := a+b
  have hs : 0 < s := by dsimp [s]; positivity
  have ha0 : 0 < a/s := div_pos ha hs
  have hb0 : 0 < b/s := div_pos hb hs
  have hsum : b/s+a/s = 1 := by dsimp [s]; field_simp; ring
  have hsum' : a/s+b/s = 1 := by linarith
  have h₀ : (0 : ℝ) ∈ Icc 0 δ := ⟨le_rfl, H.delta_pos.le⟩
  have hₛ : s ∈ Icc 0 δ := ⟨hs.le, hab⟩
  have h₁ := hlog.2 h₀ hₛ hs.ne hb0 ha0 hsum
  have h₂ := hlog.2 h₀ hₛ hs.ne ha0 hb0 hsum'
  have he₁ : b/s*(0 : ℝ)+a/s*s = a := by field_simp; ring
  have he₂ : a/s*(0 : ℝ)+b/s*s = b := by field_simp; ring
  simp only [smul_eq_mul, he₁, he₂, H.zero, sub_zero] at h₁ h₂
  have hh : Real.log (k-v a)+Real.log (k-v b) < Real.log k+Real.log (k-v s) := by
    have he : b/s*Real.log k+a/s*Real.log (k-v s) + (a/s*Real.log k+b/s*Real.log (k-v s)) = Real.log k+Real.log (k-v s) := by
      calc
        _ = (b/s+a/s)*Real.log k+(b/s+a/s)*Real.log (k-v s) := by ring
        _ = _ := by rw [hsum]; ring
    linarith
  rw [← Real.log_mul (hpositive a ⟨ha.le, by linarith⟩).ne' (hpositive b ⟨hb.le, by linarith⟩).ne', ← Real.log_mul hk.ne' (hpositive s hₛ).ne'] at hh
  have hh' := (Real.log_lt_log_iff (mul_pos (hpositive a ⟨ha.le, by linarith⟩) (hpositive b ⟨hb.le, by linarith⟩)) (mul_pos hk (hpositive s hₛ))).mp hh
  dsimp [s, psi] at hh' ⊢
  nlinarith
private lemma distance_two_cross_pos {v h g : ℝ → ℝ} {δ k p q r : ℝ} (H : CuspControl v h g δ) (hk : 0 < k) (hpositive : ∀ t ∈ Icc 0 δ, 0 < k-v t) (hlogK : StrictConvexOn ℝ (Icc 0 δ) (fun t => Real.log (k-v t))) (hlogh : StrictConvexOn ℝ (Ioo 0 δ) (fun t => Real.log (h t)))
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (hs : p+q+r ≤ δ) :
    0 < schurCross k (k-v (q+r)) (k-v p) (k-v (p+q+r)) (k-v q) (k-v r) (k-v (p+q)) := by
  have hQ := v_pos H hq (by linarith)
  have hV := v_pos H (by positivity : 0 < q+r) (by linarith)
  have hVk : v (q+r) < k := by linarith [hpositive (q+r) ⟨by positivity, by linarith⟩]
  have hden : 0 < 2*k-v (q+r) := by linarith
  have hratio := strictAntiOn_deficit_ratio H hlogh hp (show q ∈ Ioc 0 (δ-p) from ⟨hq, by linarith⟩) (show q+r ∈ Ioc 0 (δ-p) from ⟨by positivity, by linarith⟩) (by linarith : q < q+r)
  have hfirst : 0 < psi v p q - v q/v (q+r)*psi v p (q+r) := by
    have hh := (div_lt_div_iff₀ hV hQ).mp hratio
    have he : v (q+r)*(psi v p q-v q/v (q+r)*psi v p (q+r)) = psi v p q*v (q+r)-psi v p (q+r)*v q := by field_simp
    apply (mul_pos_iff_of_pos_left hV).mp
    rw [he]
    nlinarith
  have hthree := three_point H hk hpositive hlogK hp (by positivity : 0 < q+r) (by linarith)
  have hsecond : 0 < (k*psi v p (q+r)/v (q+r)-v p)*psi v q r/(2*k-v (q+r)) := by
    apply div_pos _ hden
    apply mul_pos _ (psi_pos H hq hr (by linarith))
    apply sub_pos.mpr
    apply (lt_div_iff₀ hV).mpr
    nlinarith
  have hid := distance_two_identity k (v p) (v q) (v (q+r)) (psi v p q) (psi v q r) (psi v p (q+r)) hV.ne' hden.ne'
  have he1 : v p+v (q+r)-psi v p (q+r) = v (p+q+r) := by
    dsimp [psi]
    rw [add_assoc]
    ring
  have he2 : v (q+r)-v q+psi v q r = v r := by dsimp [psi]; ring
  have he3 : v p+v q-psi v p q = v (p+q) := by dsimp [psi]; ring
  rw [he1, he2, he3] at hid
  rw [hid]
  linarith
private def G (v : ℝ → ℝ) (k x y : ℝ) : ℝ := (k-v (y-x)) - (k-v x)*(k-v y)/k
private lemma h_strictAnti {v h g : ℝ → ℝ} {δ : ℝ} (H : CuspControl v h g δ) : StrictAntiOn h (Ioc 0 δ) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioc 0 δ) (fun t ht => (H.deriv_h t ht).continuousAt.continuousWithinAt)
  intro t ht
  have ht' : t ∈ Ioc 0 δ := interior_subset ht
  rw [(H.deriv_h t ht').deriv]
  have ht0 := ht'.1
  have hg : 0 < g t := (by positivity : 0 < 1/(4*t)).trans_le (H.g_lower t ht')
  linarith
private lemma G_pos {v h g : ℝ → ℝ} {δ k x y : ℝ} (H : CuspControl v h g δ) (hk : 0 < k) (hpositive : ∀ t ∈ Icc 0 δ, 0 < k-v t) (hx : 0 < x) (hxy : x ≤ y) (hyδ : y ≤ δ) : 0 < G v k x y := by
  have hy : 0 < y := hx.trans_le hxy
  have hky := hpositive y ⟨hy.le, hyδ⟩
  have hxv := v_pos H hx (hxy.trans hyδ)
  have hv := v_strictMono H (show y-x ∈ Icc 0 δ from ⟨by linarith, by linarith⟩) (show y ∈ Icc 0 δ from ⟨hy.le, hyδ⟩) (by linarith : y-x < y)
  have hprod : (k-v x)*(k-v y)/k < k-v y := by
    apply (div_lt_iff₀ hk).mpr
    nlinarith [mul_pos hxv hky]
  dsimp [G]
  linarith
private lemma G_first {v h g : ℝ → ℝ} {δ k x y z : ℝ} (H : CuspControl v h g δ) (hk : 0 < k) (hpositive : ∀ t ∈ Icc 0 δ, 0 < k-v t) (hx : 0 < x) (hxy : x < y) (hyz : y ≤ z) (hzδ : z ≤ δ) : G v k x z < G v k y z := by
  have hvcont := H.continuous
  have hc : Continuous (fun u => G v k u z) := by dsimp [G]; fun_prop
  have hd (u : ℝ) (hu : u ∈ Ioo x z) : HasDerivAt (fun u => G v k u z) (h (z-u)+h u*(k-v z)/k) u := by
    have h₁ := (H.deriv_v (z-u) ⟨by linarith [hu.2], by linarith [hu.1]⟩).comp u ((hasDerivAt_id u).const_sub z)
    have h₂ := H.deriv_v u ⟨by linarith [hu.1], by linarith [hu.2]⟩
    convert ((hasDerivAt_const u k).sub h₁).sub ((((hasDerivAt_const u k).sub h₂).mul_const (k-v z)).div_const k) using 1
    · rfl
    · simp [Function.comp_def]
      ring
  have hm : StrictMonoOn (fun u => G v k u z) (Icc x z) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc x z) hc.continuousOn
    intro u hu
    rw [interior_Icc] at hu
    rw [(hd u hu).deriv]
    have h₁ := H.h_pos (z-u) ⟨by linarith [hu.2], by linarith [hu.1]⟩
    have h₂ := H.h_pos u ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have h₃ := hpositive z ⟨by linarith, hzδ⟩
    positivity
  exact hm ⟨le_rfl, hxy.le.trans hyz⟩ ⟨hxy.le, hyz⟩ hxy
private lemma G_second {v h g : ℝ → ℝ} {δ k x y z : ℝ} (H : CuspControl v h g δ) (hk : 0 < k) (hpositive : ∀ t ∈ Icc 0 δ, 0 < k-v t) (hx : 0 < x) (hxy : x ≤ y) (hyz : y < z) (hzδ : z ≤ δ) : G v k x z < G v k x y := by
  have hvcont := H.continuous
  have hc : Continuous (fun u => G v k x u) := by dsimp [G]; fun_prop
  have hd (u : ℝ) (hu : u ∈ Ioo x z) : HasDerivAt (fun u => G v k x u) (-h (u-x)+(k-v x)*h u/k) u := by
    have h₁ := (H.deriv_v (u-x) ⟨by linarith [hu.1], by linarith [hu.2]⟩).comp u ((hasDerivAt_id u).sub_const x)
    have h₂ := H.deriv_v u ⟨by linarith [hu.1], by linarith [hu.2]⟩
    convert ((hasDerivAt_const u k).sub h₁).sub ((((hasDerivAt_const u k).sub h₂).const_mul (k-v x)).div_const k) using 1
    · rfl
    · simp [Function.comp_def]
      ring
  have hm : StrictAntiOn (fun u => G v k x u) (Icc x z) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc x z) hc.continuousOn
    intro u hu
    rw [interior_Icc] at hu
    rw [(hd u hu).deriv]
    have huδ : u ∈ Ioc 0 δ := ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have hh := h_strictAnti H (show u-x ∈ Ioc 0 δ from ⟨by linarith [hu.1], by linarith [hu.2]⟩) huδ (by linarith : u-x < u)
    have hv := v_pos H hx (by linarith)
    have hprod : (k-v x)*h u/k < h u := by
      apply (div_lt_iff₀ hk).mpr
      nlinarith [mul_pos hv (H.h_pos u huδ)]
    linarith
  exact hm ⟨hxy, hyz.le⟩ ⟨hxy.trans hyz.le, le_rfl⟩ hyz
private lemma sequential_identity (k d a b c e f : ℝ) (hk : k ≠ 0) (hd : k^2-d^2 ≠ 0) : schurCross k d a b c e f = (f-a*c/k) - (b-d*a/k)*(e-d*c/k)/(k-d^2/k) := by
  have hs : k-d^2/k ≠ 0 := by
    intro he
    have hh : k*(k-d^2/k) = k^2-d^2 := by field_simp
    rw [he, mul_zero] at hh
    exact hd hh.symm
  unfold schurCross
  field_simp
  <;> ring
private lemma G_diag_det {v h g : ℝ → ℝ} {δ k x : ℝ} (H : CuspControl v h g δ) (hk : 0 < k) (hpositive : ∀ t ∈ Icc 0 δ, 0 < k-v t) (hx : 0 < x) (hxδ : x ≤ δ) : 0 < k^2-(k-v x)^2 := by
  have hv := v_pos H hx hxδ
  have hkx := hpositive x ⟨hx.le, hxδ⟩
  have hh := mul_pos hv (show 0 < k+(k-v x) by linarith)
  nlinarith
private lemma adjacent_right_cross_pos {v h g : ℝ → ℝ} {δ k p q r : ℝ} (H : CuspControl v h g δ) (hk : 0 < k) (hpositive : ∀ t ∈ Icc 0 δ, 0 < k-v t) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (hs : p+q+r ≤ δ) : 0 < schurCross k (k-v p) (k-v (p+q)) (k-v q)
      (k-v (p+q+r)) (k-v (q+r)) (k-v r) := by
  have hxx := G_pos H hk hpositive hp le_rfl (by linarith : p ≤ δ)
  have hxz := G_pos H hk hpositive hp (by linarith : p ≤ p+q+r) hs
  have hyz := G_pos H hk hpositive (by positivity : 0 < p+q) (by linarith : p+q ≤ p+q+r) hs
  have hxy := G_pos H hk hpositive hp (by linarith : p ≤ p+q) (by linarith : p+q ≤ δ)
  have hfirst := G_first H hk hpositive hp (by linarith : p < p+q) (by linarith : p+q ≤ p+q+r) hs
  have hsecond := G_second H hk hpositive hp le_rfl (by linarith : p < p+q) (by linarith : p+q ≤ δ)
  have hprod : G v k p (p+q)*G v k p (p+q+r) < G v k p p*G v k (p+q) (p+q+r) := by
    have h₁ := mul_pos (sub_pos.mpr hsecond) hxz
    have h₂ := mul_pos hxx (sub_pos.mpr hfirst)
    nlinarith
  have hcross : 0 < G v k (p+q) (p+q+r) - G v k p (p+q)*G v k p (p+q+r)/G v k p p := by
    apply sub_pos.mpr
    exact (div_lt_iff₀ hxx).mpr (by nlinarith)
  have hid := sequential_identity k (k-v p) (k-v (p+q)) (k-v q) (k-v (p+q+r)) (k-v (q+r)) (k-v r) hk.ne' (G_diag_det H hk hpositive hp (by linarith)).ne'
  rw [hid]
  convert hcross using 1 <;> dsimp [G] <;> simp only [sub_self, H.zero, sub_zero, show p+q-p = q by ring, show p+q+r-p = q+r by ring, show p+q+r-(p+q) = r by ring]
  <;> ring
private lemma adjacent_middle_cross_pos {v h g : ℝ → ℝ} {δ k p q r : ℝ} (H : CuspControl v h g δ) (hk : 0 < k) (hpositive : ∀ t ∈ Icc 0 δ, 0 < k-v t) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (hs : p+q+r ≤ δ) : 0 < schurCross k (k-v (p+q+r)) (k-v p) (k-v (q+r))
      (k-v (p+q)) (k-v r) (k-v q) := by
  have hzz := G_pos H hk hpositive (by positivity : 0 < p+q+r) le_rfl hs
  have hxz := G_pos H hk hpositive hp (by linarith : p ≤ p+q+r) hs
  have hyz := G_pos H hk hpositive (by positivity : 0 < p+q) (by linarith : p+q ≤ p+q+r) hs
  have hxy := G_pos H hk hpositive hp (by linarith : p ≤ p+q) (by linarith : p+q ≤ δ)
  have hfirst := G_first H hk hpositive (by positivity : 0 < p+q) (by linarith : p+q < p+q+r) le_rfl hs
  have hsecond := G_second H hk hpositive hp (by linarith : p ≤ p+q) (by linarith : p+q < p+q+r) hs
  have hprod : G v k p (p+q+r)*G v k (p+q) (p+q+r) < G v k p (p+q)*G v k (p+q+r) (p+q+r) := by
    have h₁ := mul_pos (sub_pos.mpr hsecond) hyz
    have h₂ := mul_pos hxy (sub_pos.mpr hfirst)
    nlinarith
  have hcross : 0 < G v k p (p+q) - G v k p (p+q+r)*G v k (p+q) (p+q+r)/G v k (p+q+r) (p+q+r) := by
    apply sub_pos.mpr
    exact (div_lt_iff₀ hzz).mpr (by nlinarith)
  have hid := sequential_identity k (k-v (p+q+r)) (k-v p) (k-v (q+r)) (k-v (p+q)) (k-v r) (k-v q) hk.ne' (G_diag_det H hk hpositive (by positivity : 0 < p+q+r) hs).ne'
  rw [hid]
  convert hcross using 1 <;> dsimp [G] <;> simp only [sub_self, H.zero, sub_zero, show p+q-p = q by ring, show p+q+r-p = q+r by ring, show p+q+r-(p+q) = r by ring]
  <;> ring
private lemma sorted_permutation (x : Fin 4 → ℝ) (hx : Function.Injective x) : ∃ e : Equiv.Perm (Fin 4), StrictMono (fun i => x (e i)) := by
  classical
  let s := Finset.univ.image x
  have hs : s.card = 4 := by
    dsimp [s]
    rw [Finset.card_image_of_injective _ hx]
    simp
  let f : Fin 4 → s := fun i => ⟨x i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j hij
      exact hx (congrArg Subtype.val hij)
    · intro y
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp y.property
      exact ⟨i, Subtype.ext hi⟩
  let ex : Fin 4 ≃ s := Equiv.ofBijective f hf
  let e : Equiv.Perm (Fin 4) := (s.orderIsoOfFin hs).toEquiv.trans ex.symm
  refine ⟨e, ?_⟩
  have he (i : Fin 4) : x (e i) = s.orderEmbOfFin hs i := by
    have hh := congrArg Subtype.val (ex.apply_symm_apply (s.orderIsoOfFin hs i))
    change x (ex.symm (s.orderIsoOfFin hs i)) = (s.orderEmbOfFin hs) i at hh
    exact hh
  simpa only [he] using (s.orderEmbOfFin hs).strictMono
set_option maxHeartbeats 2000000 in
/-- One window for all six real precision signs and all four distinct real nodes.
The hypotheses are scalar local differential controls, both logarithmic convexities,
and an ordinary real positive-definite Gram window. No gap ratio is constrained. -/
theorem exists_uniform_four_point_precision {v h g : ℝ → ℝ} {δ₀ k : ℝ} (H : CuspControl v h g δ₀) (hk : 0 < k) (hpositive : ∀ t ∈ Icc 0 δ₀, 0 < k-v t) (hlogK : StrictConvexOn ℝ (Icc 0 δ₀) (fun t => Real.log (k-v t))) (hlogh : StrictConvexOn ℝ (Ioo 0 δ₀) (fun t => Real.log (h t)))
    (hspd : ∀ x : Fin 4 → ℝ, Function.Injective x → (∀ i j, |x i-x j| ≤ δ₀) → Matrix.PosDef (fun i j => k-v |x i-x j|)) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ₀ ∧ ∀ x : Fin 4 → ℝ, Function.Injective x → (∀ i j, |x i-x j| ≤ δ) → ∀ i j : Fin 4, i ≠ j → ((fun i j => k-v |x i-x j|)⁻¹ : Matrix (Fin 4) (Fin 4) ℝ) i j < 0 := by
  obtain ⟨δ, hδ, hδ₀, hend⟩ := exists_uniform_endpoint_cross_pos H hk
  have gap_signs (p q r : ℝ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (hs : p+q+r ≤ δ) : ∀ i j : Fin 4, i ≠ j → (gapGram v k p q r)⁻¹ i j < 0 := by
    have hs₀ : p+q+r ≤ δ₀ := hs.trans hδ₀
    let x : Fin 4 → ℝ := ![0,p,p+q,p+q+r]
    have hx : Function.Injective x := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> norm_num [x] at hij ⊢ <;> linarith
    have hdiam : ∀ i j, |x i-x j| ≤ δ₀ := by
      have hδ₀pos : 0 ≤ δ₀ := H.delta_pos.le
      intro i j
      apply abs_le.mpr
      constructor <;> fin_cases i <;> fin_cases j <;> norm_num [x] <;> linarith
    have hA : (gapGram v k p q r).PosDef := by
      rw [gapGram_nodes H.zero hp hq hr]
      exact hspd x hx hdiam
    have h01' := adjacent_right_cross_pos H hk hpositive hr hq hp (by linarith : r+q+p ≤ δ₀)
    have h01 : 0 < schurCross k (k-v r) (k-v (p+q)) (k-v (p+q+r)) (k-v q) (k-v (q+r)) (k-v p) := by
      have he : schurCross k (k-v r) (k-v (p+q)) (k-v (p+q+r)) (k-v q) (k-v (q+r)) (k-v p) = schurCross k (k-v r) (k-v (r+q)) (k-v q) (k-v (r+q+p)) (k-v (q+p)) (k-v p) := by
        unfold schurCross
        simp only [add_comm, add_left_comm, add_assoc]
        ring
      rw [he]
      exact h01'
    have h02 := distance_two_cross_pos H hk hpositive hlogK hlogh hp hq hr hs₀
    have h03 := hend p q r hp hq hr hs
    have h12 := adjacent_middle_cross_pos H hk hpositive hp hq hr hs₀
    have h13' := distance_two_cross_pos H hk hpositive hlogK hlogh hr hq hp (by linarith : r+q+p ≤ δ₀)
    have h13 : 0 < schurCross k (k-v (p+q)) (k-v p) (k-v q) (k-v (p+q+r)) (k-v r) (k-v (q+r)) := by
      have he : schurCross k (k-v (p+q)) (k-v p) (k-v q) (k-v (p+q+r)) (k-v r) (k-v (q+r)) = schurCross k (k-v (q+p)) (k-v r) (k-v (r+q+p)) (k-v q) (k-v p) (k-v (r+q)) := by
        unfold schurCross
        simp only [add_comm, add_left_comm, add_assoc]
        ring
      rw [he]
      exact h13'
    have h23 := adjacent_right_cross_pos H hk hpositive hp hq hr hs₀
    exact four_inverse_neg k (k-v p) (k-v (p+q)) (k-v q) (k-v (q+r)) (k-v r) (k-v (p+q+r)) hA (G_diag_det H hk hpositive hp (by linarith)) (G_diag_det H hk hpositive (by positivity : 0 < p+q) (by linarith)) (G_diag_det H hk hpositive hq (by linarith))
      (G_diag_det H hk hpositive (by positivity : 0 < q+r) (by linarith))
      (G_diag_det H hk hpositive hr (by linarith))
      (G_diag_det H hk hpositive (by positivity : 0 < p+q+r) hs₀)
      h01 h02 h03 h12 h13 h23
  refine ⟨δ, hδ, hδ₀, ?_⟩
  intro x hx hdiam i j hij
  obtain ⟨e, he⟩ := sorted_permutation x hx
  let y : Fin 4 → ℝ := fun i => x (e i)
  have hy : StrictMono y := he
  have hp : 0 < y 1-y 0 := sub_pos.mpr (hy (by norm_num : (0 : Fin 4) < 1))
  have hq : 0 < y 2-y 1 := sub_pos.mpr (hy (by norm_num : (1 : Fin 4) < 2))
  have hr : 0 < y 3-y 2 := sub_pos.mpr (hy (by norm_num : (2 : Fin 4) < 3))
  have hs : (y 1-y 0)+(y 2-y 1)+(y 3-y 2) ≤ δ := by
    have hd := hdiam (e 3) (e 0)
    have hh := le_abs_self (y 3-y 0)
    change |y 3-y 0| ≤ δ at hd
    linarith
  have hsign := gap_signs (y 1-y 0) (y 2-y 1) (y 3-y 2) hp hq hr hs (e.symm i) (e.symm j) (fun hh => hij (e.symm.injective hh))
  rw [← sorted_gapGram H.zero hy] at hsign
  have hperm : ((fun i j => k-v |y i-y j|)⁻¹ : Matrix (Fin 4) (Fin 4) ℝ) = ((fun i j => k-v |x i-x j|)⁻¹ : Matrix (Fin 4) (Fin 4) ℝ).submatrix e e := by
    let M : Matrix (Fin 4) (Fin 4) ℝ := fun i j => k-v |x i-x j|
    change (M.submatrix e e)⁻¹ = M⁻¹.submatrix e e
    exact Matrix.inv_submatrix_equiv M e e
  rw [hperm] at hsign
  simpa [Matrix.submatrix_apply] using hsign
end D5.S3.Analytic.Fourier.PositiveDefinite.UniformFourPointPrecision
