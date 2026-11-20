/- GID: D5/S3/Analytic/Hardy/FiniteStripMomentBound
   generality: G
   mirror-B: D5/B/S3/Analytic/Hardy/FiniteStripMomentBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [lake/module/D5.S3.Analytic.Hardy.FiniteBlaschkeBound]
   utility: none
   digest: The finite strip Blaschke bound for interpolation by finite-time Laplace moments. -/

import D5.S3.Analytic.Hardy.FiniteBlaschkeBound
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # Finite strip bounds for Laplace moments -/

open Metric Set MeasureTheory
open scoped BigOperators ComplexConjugate

noncomputable section

namespace D5.S3.Analytic.Hardy.FiniteStripMomentBound

/-- The positive radius at a real interpolation node. -/
def radius (β q : ℝ) : ℝ := Real.sqrt (q ^ 2 + β ^ 2)

private theorem radius_sq (β q : ℝ) : radius β q ^ 2 = q ^ 2 + β ^ 2 :=
  Real.sq_sqrt (by positivity)

private theorem radius_pos {β : ℝ} (hβ : 0 < β) (q : ℝ) : 0 < radius β q :=
  Real.sqrt_pos.2 (by positivity)

private def cayley (w : ℂ) : ℂ := (1 + w) / (1 - w)

private theorem cayley_den_ne {w : ℂ} (hw : w ∈ ball 0 1) : 1 - w ≠ 0 := by
  have hn := mem_ball_zero_iff.mp hw
  intro h
  rw [← sub_eq_zero.mp h, norm_one] at hn
  exact (lt_irrefl (1 : ℝ)) hn

private theorem cayley_re_pos {w : ℂ} (hw : w ∈ ball 0 1) : 0 < (cayley w).re := by
  have hn := mem_ball_zero_iff.mp hw
  have hd := cayley_den_ne hw
  have he : (cayley w).re = (1 - ‖w‖ ^ 2) / Complex.normSq (1 - w) := by
    rw [cayley, Complex.div_re, ← Complex.normSq_eq_norm_sq, ← add_div]
    congr 1
    simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.one_re, Complex.one_im, Complex.normSq_apply]
    ring
  rw [he]
  exact div_pos (by nlinarith [norm_nonneg w]) (Complex.normSq_pos.mpr hd)

private def stripMap (β : ℝ) (w : ℂ) : ℂ :=
  ((β : ℂ) / 2) * (cayley w - (cayley w)⁻¹)

private def damping (L β : ℝ) (w : ℂ) : ℂ :=
  Complex.exp (-((L * β / 2 : ℝ) : ℂ) * (cayley w)⁻¹)

private def nodeU (β q : ℝ) : ℝ := (q + radius β q) / β

private def node (β q : ℝ) : ℝ := (nodeU β q - 1) / (nodeU β q + 1)

private theorem nodeU_pos {β q : ℝ} (hβ : 0 < β) (hq : 0 ≤ q) :
    0 < nodeU β q :=
  div_pos (add_pos_of_nonneg_of_pos hq (radius_pos hβ q)) hβ

private theorem nodeU_inv {β q : ℝ} (hβ : 0 < β) (hq : 0 ≤ q) :
    (nodeU β q)⁻¹ = (radius β q - q) / β := by
  apply inv_eq_of_mul_eq_one_right
  unfold nodeU
  field_simp [hβ.ne']
  nlinarith [radius_sq β q]

private theorem node_mem {β q : ℝ} (hβ : 0 < β) (hq : 0 ≤ q) :
    (node β q : ℂ) ∈ ball 0 1 := by
  have ht := nodeU_pos hβ hq
  rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_lt]
  unfold node
  constructor
  · apply (lt_div_iff₀ (by linarith : 0 < nodeU β q + 1)).2
    linarith
  · apply (div_lt_iff₀ (by linarith : 0 < nodeU β q + 1)).2
    linarith

private theorem cayley_node {β q : ℝ} (hβ : 0 < β) (hq : 0 ≤ q) :
    cayley (node β q : ℂ) = (nodeU β q : ℂ) := by
  have ht : (nodeU β q : ℂ) + 1 ≠ 0 := by
    exact_mod_cast (show nodeU β q + 1 ≠ 0 by linarith [nodeU_pos hβ hq])
  unfold cayley node
  push_cast
  field_simp [ht]
  <;> ring

private theorem stripMap_node {β q : ℝ} (hβ : 0 < β) (hq : 0 ≤ q) :
    stripMap β (node β q : ℂ) = (q : ℂ) := by
  rw [stripMap, cayley_node hβ hq, ← Complex.ofReal_inv, nodeU_inv hβ hq, nodeU]
  push_cast
  have h : (β : ℂ) ≠ 0 := by exact_mod_cast hβ.ne'
  field_simp
  <;> ring

private theorem intervalRatio {β q r : ℝ} (hβ : 0 < β) (hq : 0 ≤ q) (hr : 0 ≤ r) :
    ((node β q - node β r) / (1 - node β r * node β q)) =
      (q - r) / (radius β q + radius β r) := by
  let t := nodeU β q
  let s := nodeU β r
  have ht : 0 < t := nodeU_pos hβ hq
  have hs : 0 < s := nodeU_pos hβ hr
  have ht1 : t + 1 ≠ 0 := by linarith
  have hs1 : s + 1 ≠ 0 := by linarith
  have hts : t + s ≠ 0 := (add_pos ht hs).ne'
  have hd : 1 - (s - 1) / (s + 1) * ((t - 1) / (t + 1)) ≠ 0 := by
    have he : 1 - (s - 1) / (s + 1) * ((t - 1) / (t + 1)) =
        2 * (t + s) / ((s + 1) * (t + 1)) := by
      field_simp
      <;> ring
    rw [he]
    exact div_ne_zero (mul_ne_zero (by norm_num) hts) (mul_ne_zero hs1 ht1)
  have hnode : ((t - 1) / (t + 1) - (s - 1) / (s + 1)) /
      (1 - (s - 1) / (s + 1) * ((t - 1) / (t + 1))) = (t - s) / (t + s) := by
    apply (div_eq_div_iff hd hts).2
    field_simp
    <;> ring
  change _ = _
  rw [show (node β q - node β r) / (1 - node β r * node β q) = _ from hnode]
  have htinv : t⁻¹ = (radius β q - q) / β := nodeU_inv hβ hq
  have hsinv : s⁻¹ = (radius β r - r) / β := nodeU_inv hβ hr
  have hqt : q = β / 2 * (t - t⁻¹) := by
    rw [htinv, show t = (q + radius β q) / β from rfl] <;> field_simp <;> ring
  have hrs : r = β / 2 * (s - s⁻¹) := by
    rw [hsinv, show s = (r + radius β r) / β from rfl] <;> field_simp <;> ring
  have hRt : radius β q = β / 2 * (t + t⁻¹) := by
    rw [htinv, show t = (q + radius β q) / β from rfl] <;> field_simp <;> ring
  have hRs : radius β r = β / 2 * (s + s⁻¹) := by
    rw [hsinv, show s = (r + radius β r) / β from rfl] <;> field_simp <;> ring
  apply (div_eq_div_iff hts (add_pos (radius_pos hβ q) (radius_pos hβ r)).ne').2
  conv_lhs => rw [hRt, hRs]
  conv_rhs => rw [hqt, hrs]
  field_simp [ht.ne', hs.ne']
  <;> ring

private theorem norm_nodeFactor {β q r : ℝ} (hβ : 0 < β) (hq : 0 ≤ q) (hr : 0 ≤ r) :
    ‖((node β q : ℂ) - (node β r : ℂ)) /
        (1 - conj (node β r : ℂ) * (node β q : ℂ))‖ =
      |q - r| / (radius β q + radius β r) := by
  rw [Complex.conj_ofReal, ← Complex.ofReal_sub, ← Complex.ofReal_mul,
    ← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_div,
    Complex.norm_real, Real.norm_eq_abs, intervalRatio hβ hq hr,
    abs_div, abs_of_pos (add_pos (radius_pos hβ q) (radius_pos hβ r))]

private theorem norm_damping_node {L β q : ℝ} (hβ : 0 < β) (hq : 0 ≤ q) :
    ‖damping L β (node β q : ℂ)‖ = Real.exp (-L * (radius β q - q) / 2) := by
  rw [damping, cayley_node hβ hq, ← Complex.ofReal_inv, nodeU_inv hβ hq,
    Complex.norm_exp, ← Complex.ofReal_neg, ← Complex.ofReal_mul, Complex.ofReal_re]
  congr 1
  field_simp
  <;> ring

private theorem damped_norm_le {F : ℂ → ℂ} {L β M : ℝ}
    (hL : 0 ≤ L) (hβ : 0 < β) (hM : 0 ≤ M)
    (hgrowth : ∀ z : ℂ, ‖F z‖ ≤ M * Real.exp (L * max 0 (-z.re)))
    {w : ℂ} (hw : w ∈ ball 0 1) :
    ‖F (stripMap β w) * damping L β w‖ ≤ M := by
  have hu := cayley_re_pos hw
  have hun : cayley w ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hu
    exact (lt_irrefl 0) hu
  have hv : 0 < ((cayley w)⁻¹).re := by
    rw [Complex.inv_re]
    exact div_pos hu (Complex.normSq_pos.mpr hun)
  have hre : (stripMap β w).re = (β / 2) * ((cayley w).re - ((cayley w)⁻¹).re) := by
    rw [stripMap, ← Complex.ofReal_ofNat, ← Complex.ofReal_div]
    simp
  have hx : L * max 0 (-(stripMap β w).re) ≤ L * β / 2 * ((cayley w)⁻¹).re := by
    rw [hre, mul_max_of_nonneg _ _ hL, mul_zero, max_le_iff]
    constructor
    · positivity
    · have ht : 0 ≤ L * (β / 2) * (cayley w).re :=
        mul_nonneg (mul_nonneg hL (by positivity)) hu.le
      nlinarith only [ht]
  rw [norm_mul, damping, Complex.norm_exp, ← Complex.ofReal_neg]
  simp only [Complex.re_ofReal_mul]
  calc
    _ ≤ (M * Real.exp (L * max 0 (-(stripMap β w).re))) *
        Real.exp (-(L * β / 2) * ((cayley w)⁻¹).re) :=
      mul_le_mul_of_nonneg_right (hgrowth _) (Real.exp_nonneg _)
    _ = M * Real.exp (L * max 0 (-(stripMap β w).re) -
        L * β / 2 * ((cayley w)⁻¹).re) := by rw [mul_assoc, ← Real.exp_add]; ring_nf
    _ ≤ M := by
      simpa using mul_le_mul_of_nonneg_left
        (Real.exp_le_one_iff.mpr (sub_nonpos.mpr hx)) hM

/-- The damped slit-plane estimate for an entire function of one-sided exponential growth. -/
theorem entire_strip_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    {F : ℂ → ℂ} {L β M : ℝ} (hL : 0 ≤ L) (hβ : 0 < β) (hM : 0 ≤ M)
    (hF : Differentiable ℂ F)
    (hgrowth : ∀ z : ℂ, ‖F z‖ ≤ M * Real.exp (L * max 0 (-z.re)))
    (q : ι → ℝ) (hq : ∀ k, 0 ≤ q k) (hinj : Function.Injective q) (j : ι)
    (hone : F (q j) = 1) (hzero : ∀ k ≠ j, F (q k) = 0) :
    Real.exp (-L * (radius β (q j) - q j) / 2) ≤
      M * ∏ k ∈ Finset.univ.erase j, |q j - q k| / (radius β (q j) + radius β (q k)) := by
  let a (k : ι) : ℂ := (node β (q k) : ℂ)
  let H (w : ℂ) := F (stripMap β w) * damping L β w
  have ha (k : ι) : a k ∈ ball 0 1 := node_mem hβ (hq k)
  have hmap (k : ι) : stripMap β (a k) = (q k : ℂ) := stripMap_node hβ (hq k)
  have hai : Function.Injective a := by
    intro k i he
    apply hinj
    apply Complex.ofReal_injective
    rw [← hmap k, ← hmap i, he]
  have hH : DifferentiableOn ℂ H (ball 0 1) := by
    intro w hw
    have hd := cayley_den_ne hw
    have hu : cayley w ≠ 0 := by
      intro he
      have hp := cayley_re_pos hw
      rw [he, Complex.zero_re] at hp
      exact (lt_irrefl 0) hp
    have hc : DifferentiableAt ℂ cayley w := by
      unfold cayley
      fun_prop (disch := exact hd)
    have hi := hc.inv hu
    have hz : DifferentiableAt ℂ (stripMap β) w :=
      (hc.sub hi).const_mul _
    have hdamp : DifferentiableAt ℂ (damping L β) w := (hi.const_mul _).cexp
    exact ((hF.differentiableAt.comp w hz).mul hdamp).differentiableWithinAt
  have hHz (k : ι) (hk : k ∈ Finset.univ.erase j) : H (a k) = 0 := by
    change F (stripMap β (a k)) * damping L β (a k) = 0
    rw [hmap, hzero k (Finset.ne_of_mem_erase hk), zero_mul]
  have hb := FiniteBlaschkeBound.norm_le_mul_prod (Finset.univ.erase j) a
    hH (fun _ hw => damped_norm_le hL hβ hM hgrowth hw) (fun k _ => ha k) hHz hai (ha j)
  have hnorm : ‖H (a j)‖ = Real.exp (-L * (radius β (q j) - q j) / 2) := by
    change ‖F (stripMap β (a j)) * damping L β (a j)‖ = _
    rw [hmap, hone, one_mul, norm_damping_node hβ (hq j)]
  rw [hnorm] at hb
  refine hb.trans_eq ?_
  congr 1
  exact Finset.prod_congr rfl fun k _ => norm_nodeFactor hβ (hq j) (hq k)


/-- The real Lebesgue (L^2(0,L)) norm written in integral form. -/
def windowNorm (L : ℝ) (h : ℝ → ℝ) : ℝ := Real.sqrt (∫ s in Ioo 0 L, h s ^ 2)

private def laplace (L : ℝ) (h : ℝ → ℝ) (z : ℂ) : ℂ :=
  ∫ s in Ioo 0 L, Complex.exp (-z * (s : ℂ)) * (h s : ℂ)

private theorem laplace_real (L : ℝ) (h : ℝ → ℝ) (q : ℝ) :
    laplace L h (q : ℂ) = ((∫ s in Ioo 0 L, h s * Real.exp (-q * s) : ℝ) : ℂ) := by
  unfold laplace
  rw [← integral_complex_ofReal]
  congr 1
  funext s
  simp only [Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_exp]
  exact mul_comm _ _

private theorem laplace_entire {L : ℝ} {h : ℝ → ℝ}
    (hh : Integrable h (volume.restrict (Ioo 0 L))) : Differentiable ℂ (laplace L h) := by
  intro z
  let μ := volume.restrict (Ioo 0 L)
  let f (w : ℂ) (s : ℝ) := Complex.exp (-w * (s : ℂ)) * (h s : ℂ)
  let f' (w : ℂ) (s : ℝ) := Complex.exp (-w * (s : ℂ)) * (-(s : ℂ)) * (h s : ℂ)
  let C := Real.exp ((‖z‖ + 1) * L) * L
  have hmeas : AEStronglyMeasurable (fun s => (h s : ℂ)) μ :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable hh.aestronglyMeasurable
  have hmeasF (w : ℂ) : AEStronglyMeasurable (f w) μ := by
    exact (by fun_prop : Continuous (fun s : ℝ => Complex.exp (-w * (s : ℂ)))).aestronglyMeasurable.mul hmeas
  have hnorm (w : ℂ) (hw : w ∈ ball z 1) (s : ℝ) (hs : s ∈ Ioo 0 L) :
      ‖Complex.exp (-w * (s : ℂ))‖ ≤ Real.exp ((‖z‖ + 1) * L) := by
    have hdist : ‖w - z‖ < 1 := by simpa [dist_eq_norm] using hw
    have hw' : ‖w‖ ≤ ‖z‖ + 1 := by
      have hn : ‖w‖ ≤ ‖w - z‖ + ‖z‖ := by
        simpa using norm_add_le (w - z) z
      linarith
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    calc
      _ ≤ ‖-w * (s : ℂ)‖ := Complex.re_le_norm _
      _ = ‖w‖ * s := by rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg hs.1.le]
      _ ≤ _ := mul_le_mul hw' hs.2.le hs.1.le (by positivity)
  have hFint : Integrable (f z) μ := by
    apply (hh.norm.const_mul (Real.exp ((‖z‖ + 1) * L))).mono' (hmeasF z)
    filter_upwards [ae_restrict_mem (μ := volume) (s := Ioo 0 L) measurableSet_Ioo] with s hs
    simp only [f, norm_mul, Complex.norm_real]
    exact mul_le_mul_of_nonneg_right (hnorm z (mem_ball_self zero_lt_one) s hs) (norm_nonneg _)
  have hF'meas : AEStronglyMeasurable (f' z) μ := by
    exact (by fun_prop :
      Continuous (fun s : ℝ => Complex.exp (-z * (s : ℂ)) * (-(s : ℂ)))).aestronglyMeasurable.mul hmeas
  have hbound : ∀ᵐ s ∂μ, ∀ w ∈ ball z 1, ‖f' w s‖ ≤ C * ‖h s‖ := by
    filter_upwards [ae_restrict_mem (μ := volume) (s := Ioo 0 L) measurableSet_Ioo] with s hs
    intro w hw
    simp only [f', norm_mul, norm_neg, Complex.norm_real, C]
    rw [Real.norm_of_nonneg hs.1.le]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul (hnorm w hw s hs) hs.2.le hs.1.le (Real.exp_nonneg _)) (norm_nonneg _)
  have hdiff : ∀ᵐ s ∂μ, ∀ w ∈ ball z 1,
      HasDerivAt (fun v => f v s) (f' w s) w := by
    filter_upwards with s
    intro w _
    have hd := ((hasDerivAt_id w).neg.mul_const (s : ℂ)).cexp.mul_const (h s : ℂ)
    simpa [f, f', neg_mul] using hd
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (ball_mem_nhds z zero_lt_one) (Filter.Eventually.of_forall hmeasF)
    hFint hF'meas hbound (hh.norm.const_mul C) hdiff).2.differentiableAt

private theorem laplace_growth {L : ℝ} (hL : 0 < L) {h : ℝ → ℝ}
    (hh : MemLp h 2 (volume.restrict (Ioo 0 L))) (z : ℂ) :
    ‖laplace L h z‖ ≤ (Real.sqrt L * windowNorm L h) * Real.exp (L * max 0 (-z.re)) := by
  let μ := volume.restrict (Ioo 0 L)
  have hone : MemLp (fun _ : ℝ => (1 : ℝ)) 2 μ := memLp_const 1
  have hcs := integral_mul_norm_le_Lp_mul_Lq (μ := μ) Real.HolderConjugate.two_two
    (by simpa using hh : MemLp h (ENNReal.ofReal (2 : ℝ)) μ)
    (by simpa using hone : MemLp (fun _ : ℝ => (1 : ℝ)) (ENNReal.ofReal (2 : ℝ)) μ)
  have hmass : (∫ _ : ℝ, (1 : ℝ) ∂μ) = L := by
    change (∫ _ in Ioo 0 L, (1 : ℝ)) = L
    rw [setIntegral_const, smul_eq_mul, mul_one]
    simp [measureReal_def, Real.volume_Ioo, hL.le]
  have hL1 : (∫ s, ‖h s‖ ∂μ) ≤ Real.sqrt L * windowNorm L h := by
    simp only [norm_one, mul_one, Real.rpow_two, one_pow, Real.norm_eq_abs, sq_abs,
      ← Real.sqrt_eq_rpow] at hcs
    rw [hmass] at hcs
    simpa [windowNorm, μ, mul_comm] using hcs
  let E := Real.exp (L * max 0 (-z.re))
  calc
    ‖laplace L h z‖ ≤ ∫ s, ‖Complex.exp (-z * (s : ℂ)) * (h s : ℂ)‖ ∂μ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ s, E * ‖h s‖ ∂μ := by
      apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
        ((hh.integrable (by norm_num)).norm.const_mul E)
      filter_upwards [ae_restrict_mem (μ := volume) (s := Ioo 0 L) measurableSet_Ioo] with s hs
      simp only [norm_mul, Complex.norm_real, Complex.norm_exp, E]
      gcongr
      rw [Complex.mul_re, Complex.ofReal_im, mul_zero, sub_zero, Complex.ofReal_re, Complex.neg_re]
      calc
        -z.re * s ≤ max 0 (-z.re) * s :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hs.1.le
        _ ≤ L * max 0 (-z.re) := by
          rw [mul_comm L]
          exact mul_le_mul_of_nonneg_left hs.2.le (le_max_left _ _)
    _ ≤ _ := by
      rw [integral_const_mul, mul_comm E]
      exact mul_le_mul_of_nonneg_right hL1 (Real.exp_nonneg _)

/-- A real function on the prescribed positive time window satisfying the exact
Kronecker moment conditions has the finite strip Blaschke lower bound. -/
theorem windowNorm_lower_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    {L β : ℝ} (hL : 0 < L) (hβ : 0 < β) (q : ι → ℝ)
    (hq : ∀ k, 0 ≤ q k) (hinj : Function.Injective q) (j : ι)
    (h : ℝ → ℝ) (hh : MemLp h 2 (volume.restrict (Ioo 0 L)))
    (hm : ∀ k, (∫ s in Ioo 0 L, h s * Real.exp (-q k * s)) = if k = j then 1 else 0) :
    (∏ k ∈ Finset.univ.erase j, (radius β (q j) + radius β (q k)) / |q j - q k|) *
        Real.exp (-L * (radius β (q j) - q j) / 2) / Real.sqrt L ≤ windowNorm L h := by
  have hb := entire_strip_bound hL.le hβ
    (show 0 ≤ Real.sqrt L * windowNorm L h by unfold windowNorm; positivity)
    (laplace_entire (hh.integrable (by norm_num))) (laplace_growth hL hh) q hq hinj j
    (by rw [laplace_real, hm]; simp)
    (by intro k hk; rw [laplace_real, hm, if_neg hk, Complex.ofReal_zero])
  have hpos : 0 < ∏ k ∈ Finset.univ.erase j,
      |q j - q k| / (radius β (q j) + radius β (q k)) := by
    apply Finset.prod_pos
    intro k hk
    apply div_pos _ (add_pos (radius_pos hβ _) (radius_pos hβ _))
    exact abs_pos.mpr (sub_ne_zero.mpr (fun he => Finset.ne_of_mem_erase hk (hinj he).symm))
  have hc := (div_le_iff₀ hpos).2 (show _ ≤ _ * _ from hb)
  rw [div_le_iff₀ (Real.sqrt_pos.2 hL)]
  have hrecip :
      (∏ k ∈ Finset.univ.erase j, (radius β (q j) + radius β (q k)) / |q j - q k|) =
      (∏ k ∈ Finset.univ.erase j, |q j - q k| / (radius β (q j) + radius β (q k)))⁻¹ := by
    rw [← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl fun k _ => (inv_div _ _).symm
  rw [hrecip, mul_comm, ← div_eq_mul_inv]
  simpa [mul_comm] using hc

#print axioms entire_strip_bound
#print axioms windowNorm_lower_bound

end D5.S3.Analytic.Hardy.FiniteStripMomentBound
