/- GID: D5/S3/Quantum/Petz/SpectralSymmetrization
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Dittmann's logarithmic curvature kernel and its cyclic symmetrization including all positive-node coincidences. -/

import D5.S3.Quantum.Petz.KernelSmoothness
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Tactic

namespace D5.S3.Quantum.Petz.SpectralSymmetrization

set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

open Set Filter Topology
open MeasureTheory
open D5.S3.Quantum.PositiveResolvent.LogMeanResolvents
open D5.S3.Quantum.Petz.SymmetricKernel

noncomputable def K (z u : ℝ) : ℝ := deriv (fun r => Real.log (L r u)) z

noncomputable def d (x y z : ℝ) : ℝ :=
  z * ((3 / 2 : ℝ) * dslope (fun u => K z u) x y - K z x * K z y)

private theorem K_eq_of_ne {z u : ℝ} (hz : 0 < z) (hu : 0 < u) (hzu : z ≠ u) :
    K z u = 1 / (z * (Real.log z - Real.log u)) - 1 / (z - u) := by
  have ha : Real.log z - Real.log u ≠ 0 :=
    sub_ne_zero.mpr (fun h => hzu (Real.log_injOn_pos hz hu h))
  have hb : z - u ≠ 0 := sub_ne_zero.mpr hzu
  have hq := ((Real.hasDerivAt_log hz.ne').sub_const (Real.log u)).div
    ((hasDerivAt_id z).sub_const u) hb
  have hl := hq.log (div_ne_zero ha hb)
  have he : (fun r => Real.log (L r u)) =ᶠ[𝓝 z]
      (fun r => Real.log ((Real.log r - Real.log u) / (r - u))) := by
    filter_upwards [eventually_gt_nhds hz, isOpen_ne.mem_nhds hzu] with r hr hru
    rw [L_eq_of_ne hr hu hru]
  rw [K, (hl.congr_of_eventuallyEq he).deriv]
  dsimp
  field_simp [hz.ne', ha, hb]
  <;> ring

private theorem L_hasDerivAt {z u : ℝ} (hz : 0 < z) (hu : 0 < u) :
    HasDerivAt (fun r => L r u) (-m z z u) z := by
  have hc : ContinuousAt (fun r => -m r z u) z := by
    have hm := (m_continuousAt hz hz hu).comp_of_eq
      (continuousAt_id.prodMk (continuousAt_const.prodMk continuousAt_const)) rfl
    exact hm.neg
  apply hasDerivAt_iff_tendsto_slope.mpr
  apply hc.tendsto.mono_left nhdsWithin_le_nhds |>.congr'
  filter_upwards [self_mem_nhdsWithin, (eventually_gt_nhds hz).filter_mono
    nhdsWithin_le_nhds] with r hr hpos
  have hne : r ≠ z := hr
  have h := L_sub_L_eq_m hu hz hpos
  rw [L_symm u r, L_symm u z, m_symm u z r, m_symm_right z u r,
    m_symm z r u] at h
  simp only [slope_def_field]
  rw [h]
  field_simp [sub_ne_zero.mpr hne]
  <;> ring

private theorem K_eq {z u : ℝ} (hz : 0 < z) (hu : 0 < u) :
    K z u = -m z z u / L z u := by
  exact ((L_hasDerivAt hz hu).log (L_pos hz hu).ne').deriv

private theorem K_continuousAt {z u : ℝ} (hz : 0 < z) (hu : 0 < u) :
    ContinuousAt (fun p : ℝ × ℝ => K p.1 p.2) (z, u) := by
  have hid : ContinuousAt (fun p : ℝ × ℝ => p) (z, u) := continuousAt_id
  have hm := (m_continuousAt hz hz hu).comp_of_eq
    (hid.fst.prodMk (hid.fst.prodMk hid.snd)) rfl
  have hc := hm.neg.div (L_continuousAt hz hu) (L_pos hz hu).ne'
  apply hc.congr_of_eventuallyEq
  filter_upwards [(continuousAt_fst.tendsto.eventually (eventually_gt_nhds hz)).and
    (continuousAt_snd.tendsto.eventually (eventually_gt_nhds hu))] with p hp
  exact K_eq hp.1 hp.2

private noncomputable def N (z u v : ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), 1 / ((z + t) * (z + t) * (u + t) * (v + t))

private theorem N_continuousAt {z u v : ℝ} (hz : 0 < z) (hu : 0 < u) (hv : 0 < v) :
    ContinuousAt (fun p : ℝ × ℝ × ℝ => N p.1 p.2.1 p.2.2) (z, u, v) := by
  let r := min z (min u v) / 2
  have hr : 0 < r := by dsimp [r]; exact half_pos (lt_min hz (lt_min hu hv))
  have hrz : r < z := by dsimp [r]; linarith [min_le_left z (min u v)]
  have hru : r < u := by
    dsimp [r]; linarith [(min_le_right z (min u v)).trans (min_le_left u v)]
  have hrv : r < v := by
    dsimp [r]; linarith [(min_le_right z (min u v)).trans (min_le_right u v)]
  have he : ∀ᶠ p : ℝ × ℝ × ℝ in 𝓝 (z, u, v), r < p.1 ∧ r < p.2.1 ∧ r < p.2.2 :=
    (continuousAt_fst.tendsto.eventually (eventually_gt_nhds hrz)).and
      (((continuousAt_fst.comp continuousAt_snd).tendsto.eventually (eventually_gt_nhds hru)).and
        ((continuousAt_snd.comp continuousAt_snd).tendsto.eventually (eventually_gt_nhds hrv)))
  unfold N
  apply continuousAt_of_dominated
    (bound := fun t : ℝ => (1 / r) * (1 / ((r + t) * (r + t) * (r + t))))
  · exact Eventually.of_forall (fun p =>
      (by fun_prop : Measurable (fun t : ℝ =>
        1 / ((p.1 + t) * (p.1 + t) * (p.2.1 + t) * (p.2.2 + t)))).aestronglyMeasurable)
  · filter_upwards [he] with p hp
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change 0 < t at ht
    have hrt : 0 < r + t := by positivity
    have h1 : r ≤ p.1 + t := by linarith [hp.1]
    have h2 : r + t ≤ p.1 + t := by linarith [hp.1]
    have h3 : r + t ≤ p.2.1 + t := by linarith [hp.2.1]
    have h4 : r + t ≤ p.2.2 + t := by linarith [hp.2.2]
    have hp1 : 0 < p.1 + t := hrt.trans_le h2
    have hp2 : 0 < p.2.1 + t := hrt.trans_le h3
    have hp3 : 0 < p.2.2 + t := hrt.trans_le h4
    have hd : 0 < (p.1 + t) * (p.1 + t) * (p.2.1 + t) * (p.2.2 + t) := by
      positivity
    rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hd), one_div_mul_one_div]
    apply one_div_le_one_div_of_le (by positivity)
    calc
      r * ((r + t) * (r + t) * (r + t)) = (r * (r + t)) * ((r + t) * (r + t)) := by ring
      _ ≤ ((p.1 + t) * (p.1 + t)) * ((p.2.1 + t) * (p.2.2 + t)) :=
        mul_le_mul (mul_le_mul h1 h2 hrt.le (by linarith))
          (mul_le_mul h3 h4 hrt.le (by linarith)) (by positivity) (by positivity)
      _ = (p.1 + t) * (p.1 + t) * (p.2.1 + t) * (p.2.2 + t) := by ring
  · exact (m_integrable hr hr hr).const_mul (1 / r)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change 0 < t at ht
    exact continuousAt_const.div (by fun_prop)
      (by positivity : (z + t) * (z + t) * (u + t) * (v + t) ≠ 0)

private theorem m_sub_m {z u v : ℝ} (hz : 0 < z) (hu : 0 < u) (hv : 0 < v) :
    m z z v - m z z u = (u - v) * N z u v := by
  rw [m, m, ← integral_sub (m_integrable hz hz hv) (m_integrable hz hz hu),
    N, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  change 0 < t at ht
  have h1 : z + t ≠ 0 := by positivity
  have h2 : u + t ≠ 0 := by positivity
  have h3 : v + t ≠ 0 := by positivity
  field_simp
  <;> ring

private theorem m_hasDerivAt {z u : ℝ} (hz : 0 < z) (hu : 0 < u) :
    HasDerivAt (fun v => m z z v) (-N z u u) u := by
  have hc : ContinuousAt (fun v => -N z u v) u := by
    have hn := (N_continuousAt hz hu hu).comp_of_eq
      (continuousAt_const.prodMk (continuousAt_const.prodMk continuousAt_id)) rfl
    exact hn.neg
  apply hasDerivAt_iff_tendsto_slope.mpr
  apply hc.tendsto.mono_left nhdsWithin_le_nhds |>.congr'
  filter_upwards [self_mem_nhdsWithin, (eventually_gt_nhds hu).filter_mono
    nhdsWithin_le_nhds] with v hv hpos
  have hne : v ≠ u := hv
  simp only [slope_def_field]
  rw [m_sub_m hz hu hpos]
  field_simp [sub_ne_zero.mpr hne]
  <;> ring

private theorem K_hasDerivAt {z u : ℝ} (hz : 0 < z) (hu : 0 < u) :
    HasDerivAt (fun v => K z v)
      ((N z u u * L z u - m z z u * m u u z) / (L z u) ^ 2) u := by
  have hL : HasDerivAt (fun v => L z v) (-m u u z) u := by
    simpa only [L_symm z] using (L_hasDerivAt hu hz)
  have hd := (m_hasDerivAt hz hu).neg.div hL (L_pos hz hu).ne'
  have he : (fun v => K z v) =ᶠ[𝓝 u] (fun v => -m z z v / L z v) := by
    filter_upwards [eventually_gt_nhds hu] with v hv
    exact K_eq hz hv
  apply (hd.congr_of_eventuallyEq he).congr_deriv
  dsimp
  ring

private theorem deriv_K_continuousAt {z u : ℝ} (hz : 0 < z) (hu : 0 < u) :
    ContinuousAt (fun p : ℝ × ℝ => deriv (fun v => K p.1 v) p.2) (z, u) := by
  have hid : ContinuousAt (fun p : ℝ × ℝ => p) (z, u) := continuousAt_id
  have hN := (N_continuousAt hz hu hu).comp_of_eq
    (hid.fst.prodMk (hid.snd.prodMk hid.snd)) rfl
  have hm1 := (m_continuousAt hz hz hu).comp_of_eq
    (hid.fst.prodMk (hid.fst.prodMk hid.snd)) rfl
  have hm2 := (m_continuousAt hu hu hz).comp_of_eq
    (hid.snd.prodMk (hid.snd.prodMk hid.fst)) rfl
  have hL := L_continuousAt hz hu
  have hc := ((hN.mul hL).sub (hm1.mul hm2)).div (hL.pow 2)
    (pow_ne_zero 2 (L_pos hz hu).ne')
  apply hc.congr_of_eventuallyEq
  filter_upwards [(continuousAt_fst.tendsto.eventually (eventually_gt_nhds hz)).and
    (continuousAt_snd.tendsto.eventually (eventually_gt_nhds hu))] with p hp
  exact (K_hasDerivAt hp.1 hp.2).deriv

/-- Cyclic symmetrization at pairwise-distinct positive nodes. -/
private theorem d_symmetrization_of_ne {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    (d x y z + d y z x + d z x y) / 3 = hs x y z := by
  have ha : Real.log x - Real.log y ≠ 0 :=
    sub_ne_zero.mpr (fun h => hxy (Real.log_injOn_pos hx hy h))
  have hb : Real.log x - Real.log z ≠ 0 :=
    sub_ne_zero.mpr (fun h => hxz (Real.log_injOn_pos hx hz h))
  have hc : Real.log y - Real.log z ≠ 0 :=
    sub_ne_zero.mpr (fun h => hyz (Real.log_injOn_pos hy hz h))
  rw [hs_eq_closedForm hx hy hz hxy hxz hyz]
  unfold d
  rw [dslope_of_ne _ hxy.symm, dslope_of_ne _ hyz.symm, dslope_of_ne _ hxz]
  simp only [slope_def_field]
  rw [K_eq_of_ne hz hx hxz.symm, K_eq_of_ne hz hy hyz.symm,
    K_eq_of_ne hx hy hxy, K_eq_of_ne hx hz hxz,
    K_eq_of_ne hy hz hyz, K_eq_of_ne hy hx hxy.symm]
  dsimp [closedForm]
  rw [show z - x = -(x - z) by ring, show z - y = -(y - z) by ring,
    show y - x = -(x - y) by ring,
    show Real.log z - Real.log x = -(Real.log x - Real.log z) by ring,
    show Real.log z - Real.log y = -(Real.log y - Real.log z) by ring,
    show Real.log y - Real.log x = -(Real.log x - Real.log y) by ring]
  simp only [mul_neg, neg_mul, neg_neg, div_neg_eq_neg_div]
  field_simp [hx.ne', hy.ne', hz.ne', ha, hb, hc,
    sub_ne_zero.mpr hxy, sub_ne_zero.mpr hxy.symm,
    sub_ne_zero.mpr hxz, sub_ne_zero.mpr hxz.symm,
    sub_ne_zero.mpr hyz, sub_ne_zero.mpr hyz.symm]
  <;> ring

attribute [local irreducible] K hs

private theorem d_symm (x y z : ℝ) : d x y z = d y x z := by
  have hd : dslope (fun u => K z u) x y = dslope (fun u => K z u) y x := by
    by_cases hxy : x = y
    · subst y; rfl
    · rw [dslope_of_ne _ (Ne.symm hxy), dslope_of_ne _ hxy, slope_def_field,
        slope_def_field, div_eq_div_iff (sub_ne_zero.mpr (Ne.symm hxy)) (sub_ne_zero.mpr hxy)]
      ring
  unfold d
  rw [hd, mul_comm (K z x) (K z y)]

private theorem d_second_continuousAt {x y z : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hz : 0 < z) : ContinuousAt (fun v => d x v z) y := by
  have hg : ContinuousAt (fun v : ℝ => (z, v)) y :=
    continuousAt_const.prodMk continuousAt_id
  have hK := (K_continuousAt hz hy).comp_of_eq hg rfl
  simp only [Function.comp_def] at hK
  have hd : ContinuousAt (dslope (fun u => K z u) x) y := by
    by_cases hxy : y = x
    · subst y
      exact continuousAt_dslope_same.mpr (K_hasDerivAt hz hx).differentiableAt
    · exact (continuousAt_dslope_of_ne hxy).mpr hK
  exact ((hd.const_mul (3 / 2)).sub (hK.const_mul (K z x))).const_mul z

private theorem d_first_continuousAt {x y z : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hz : 0 < z) : ContinuousAt (fun v => d v y z) x := by
  apply (d_second_continuousAt hy hx hz).congr_of_eventuallyEq
  exact Eventually.of_forall (fun v => d_symm v y z)

private theorem d_third_continuousAt_of_ne {x y z : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hz : 0 < z) (hxy : x ≠ y) : ContinuousAt (fun v => d x y v) z := by
  have hg1 : ContinuousAt (fun v : ℝ => (v, x)) z :=
    continuousAt_id.prodMk continuousAt_const
  have hg2 : ContinuousAt (fun v : ℝ => (v, y)) z :=
    continuousAt_id.prodMk continuousAt_const
  have h1 := (K_continuousAt hz hx).comp_of_eq hg1 rfl
  have h2 := (K_continuousAt hz hy).comp_of_eq hg2 rfl
  simp only [Function.comp_def] at h1 h2
  have hc := continuousAt_id.mul
    ((((h2.sub h1).div_const (y - x)).const_mul (3 / 2)).sub (h1.mul h2))
  apply hc.congr_of_eventuallyEq
  apply Eventually.of_forall
  intro v
  simp only [d, dslope_of_ne _ hxy.symm, slope_def_field,
    Pi.mul_apply, Pi.sub_apply, id_eq]

private theorem d_third_continuousAt_same {x z : ℝ} (hx : 0 < x) (hz : 0 < z) :
    ContinuousAt (fun v => d x x v) z := by
  have hg : ContinuousAt (fun v : ℝ => (v, x)) z :=
    continuousAt_id.prodMk continuousAt_const
  have h1 := (K_continuousAt hz hx).comp_of_eq hg rfl
  have h2 := (deriv_K_continuousAt hz hx).comp_of_eq hg rfl
  simp only [Function.comp_def] at h1 h2
  have hc := continuousAt_id.mul ((h2.const_mul (3 / 2)).sub (h1.mul h1))
  apply hc.congr_of_eventuallyEq
  apply Eventually.of_forall
  intro v
  simp only [d, dslope_same, Pi.mul_apply, Pi.sub_apply, id_eq]

private theorem d_symmetrization_same_of_ne {x z : ℝ} (hx : 0 < x) (hz : 0 < z)
    (hxz : x ≠ z) : (d x x z + d x z x + d z x x) / 3 = hs x x z := by
  have h1 : ContinuousAt (fun y => (d x y z + d y z x + d z x y) / 3) x :=
    (((d_second_continuousAt hx hx hz).add (d_first_continuousAt hx hz hx)).add
      (d_third_continuousAt_of_ne hz hx hx hxz.symm)).div_const 3
  have hg : ContinuousAt (fun y : ℝ => (x, y, z)) x :=
    continuousAt_const.prodMk (continuousAt_id.prodMk continuousAt_const)
  have h2 := (hs_continuousAt hx hx hz).comp_of_eq hg rfl
  simp only [Function.comp_def] at h2
  have he : (fun y => hs x y z) =ᶠ[𝓝[≠] x]
      (fun y => (d x y z + d y z x + d z x y) / 3) := by
    have havoid : ∀ᶠ y in 𝓝 x, y ≠ z := isOpen_ne.mem_nhds hxz
    filter_upwards [self_mem_nhdsWithin,
      (eventually_gt_nhds hx).filter_mono nhdsWithin_le_nhds,
      havoid.filter_mono nhdsWithin_le_nhds] with y hy hpos hyz
    have hne : y ≠ x := hy
    exact (d_symmetrization_of_ne hx hpos hz (Ne.symm hne) hxz hyz).symm
  exact tendsto_nhds_unique ((h1.tendsto.mono_left nhdsWithin_le_nhds).congr' he.symm)
    (h2.tendsto.mono_left nhdsWithin_le_nhds)

private theorem d_symmetrization_same {x z : ℝ} (hx : 0 < x) (hz : 0 < z) :
    (d x x z + d x z x + d z x x) / 3 = hs x x z := by
  by_cases hxz : x = z
  · subst z
    have h1 : ContinuousAt (fun z => (d x x z + d x z x + d z x x) / 3) x :=
      (((d_third_continuousAt_same hx hx).add (d_second_continuousAt hx hx hx)).add
        (d_first_continuousAt hx hx hx)).div_const 3
    have hg : ContinuousAt (fun z : ℝ => (x, x, z)) x :=
      continuousAt_const.prodMk (continuousAt_const.prodMk continuousAt_id)
    have h2 := (hs_continuousAt hx hx hx).comp_of_eq hg rfl
    simp only [Function.comp_def] at h2
    have he : (fun z => hs x x z) =ᶠ[𝓝[≠] x]
        (fun z => (d x x z + d x z x + d z x x) / 3) := by
      filter_upwards [self_mem_nhdsWithin,
        (eventually_gt_nhds hx).filter_mono nhdsWithin_le_nhds] with z hz hpos
      exact (d_symmetrization_same_of_ne hx hpos (by exact Ne.symm hz)).symm
    exact tendsto_nhds_unique ((h1.tendsto.mono_left nhdsWithin_le_nhds).congr' he.symm)
      (h2.tendsto.mono_left nhdsWithin_le_nhds)
  · exact d_symmetrization_same_of_ne hx hz hxz

/-- Dittmann's cyclic symmetrization, including every coincidence of positive nodes. -/
theorem d_symmetrization {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    (d x y z + d y z x + d z x y) / 3 = hs x y z := by
  by_cases hxy : x = y
  · subst y
    exact d_symmetrization_same hx hz
  by_cases hxz : x = z
  · subst z
    rw [hs_symm_right hx hy hx]
    convert d_symmetrization_same hx hy using 1 <;> ring
  by_cases hyz : y = z
  · subst z
    rw [hs_symm hx hy hy, hs_symm_right hy hx hy]
    convert d_symmetrization_same hy hx using 1 <;> ring
  exact d_symmetrization_of_ne hx hy hz hxy hxz hyz

/-- The nonsymmetric and symmetric kernels agree at a fully repeated positive node. -/
theorem d_self {x : ℝ} (hx : 0 < x) : d x x x = -1 / (8 * x) := by
  have h := d_symmetrization hx hx hx
  rw [hs_self hx] at h
  linarith

end D5.S3.Quantum.Petz.SpectralSymmetrization
