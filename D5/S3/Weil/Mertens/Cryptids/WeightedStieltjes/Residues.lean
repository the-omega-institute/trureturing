/- GID: D5/S3/Weil/Mertens/Cryptids/WeightedStieltjes/Residues
   generality: G
   mirror-B: D5/B/S3/Weil/Mertens/Cryptids/WeightedStieltjes/Residues
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original Cryptids WeightedStieltjes analytic source for the RH Chebyshev bound. -/

/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in
  docs/reports/licenses/cryptids-LICENSE.txt.
Source: https://github.com/google-deepmind/cryptids/blob/e5f59ed70d1549a61ef8873a6fbae9268fdbd557/Cryptids/Semantics/Riemann/WeightedStieltjes.lean
Routing adaptations: ordinary D5 modules, redirected imports, and declaration-boundary splitting.
The original declaration namespaces, statements, and mathematical proof text are retained.
Retirement: when this repository's lake-manifest.json Mathlib revision provides an equivalent
RH-only real-x Chebyshev psi estimate for x >= 5000, replace the target with that declaration
and delete the transplanted declarations no longer in its live dependency closure.
-/

import D5.S3.Weil.Mertens.Cryptids.WeightedStieltjes.Integral

/-! Original WeightedStieltjes analytic supplier for the RH Chebyshev estimate. -/

namespace ConjectureMachines.Semantics.Riemann.WeightedStieltjes

open Complex Finset Filter MeasureTheory Set Asymptotics Topology
open scoped Real Topology Interval

/-- If `g : ℂ → ℂ` is differentiable at `p`, then `(g s - g p) / (s - p)` tends to `deriv g p`
on the punctured neighborhood `𝓝[≠] p`. -/
theorem tendsto_sub_div_sub_of_differentiableAt {g : ℂ → ℂ} {p : ℂ}
    (hg : DifferentiableAt ℂ g p) :
    Tendsto (fun s ↦ (g s - g p) / (s - p)) (𝓝[≠] p) (𝓝 (deriv g p)) := by
  have hc : ContinuousAt (dslope g p) p := continuousAt_dslope_same.mpr hg
  have ht : Tendsto (dslope g p) (𝓝[≠] p) (𝓝 (deriv g p)) := by
    rw [← dslope_same]
    exact hc.tendsto.mono_left nhdsWithin_le_nhds
  refine ht.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [dslope_of_ne _ hs, slope_def_field]

/-- **General Single-Pole Removable Singularity Lemma (`AnalyticAt`)**:
If `f : ℂ → ℂ` is complex-differentiable on a punctured neighborhood of `p` and
`f s - r / (s - p) → L` as `s → p` (`s ≠ p`), then updating `s ↦ f s - r / (s - p)` at `p`
with `L` yields a function that is analytic at `p`. -/
theorem analyticAt_update_sub_inv_sub_of_tendsto {f : ℂ → ℂ} {p r L : ℂ}
    (hf : ∀ᶠ z in 𝓝[≠] p, DifferentiableAt ℂ f z)
    (hL : Tendsto (fun s ↦ f s - r / (s - p)) (𝓝[≠] p) (𝓝 L)) :
    AnalyticAt ℂ (Function.update (fun s ↦ f s - r / (s - p)) p L) p := by
  refine Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_
  · filter_upwards [hf, self_mem_nhdsWithin] with z hfz hzp
    have hsub : z - p ≠ 0 := sub_ne_zero.mpr hzp
    have hd : DifferentiableAt ℂ (fun s ↦ f s - r / (s - p)) z :=
      hfz.sub (differentiableAt_const r |>.div (differentiableAt_id.sub_const p) hsub)
    refine hd.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_compl_singleton.mem_nhds hzp] with w hw
    simp [Function.update_of_ne hw]
  · exact continuousAt_update_same.mpr hL

/-- Removing a finite set of simple poles `S : Finset ℂ` from `f : ℂ → ℂ`, where each pole `q ∈ S`
has residue `res q` and punctured-neighborhood limit `limVal q = lim_{s → q} (f s - res q / (s -
q))`.
Away from `S`, `removePoles f S res limVal s = f s - ∑ q ∈ S, res q / (s - q)`. -/
noncomputable def removePoles (f : ℂ → ℂ) (S : Finset ℂ) (res limVal : ℂ → ℂ) (s : ℂ) : ℂ :=
  open Classical in
  if s ∈ S then
    limVal s - ∑ q ∈ S.erase s, res q / (s - q)
  else
    f s - ∑ q ∈ S, res q / (s - q)

/-- For `s ∉ S`, `removePoles f S res limVal s = f s - ∑ q ∈ S, res q / (s - q)`. -/
theorem removePoles_of_notMem (f : ℂ → ℂ) (S : Finset ℂ) (res limVal : ℂ → ℂ) {s : ℂ}
    (hs : s ∉ S) :
    removePoles f S res limVal s = f s - ∑ q ∈ S, res q / (s - q) := by
  simp [removePoles, hs]

/-- For `p ∈ S`, `removePoles f S res limVal p = limVal p - ∑ q ∈ S.erase p, res q / (p - q)`. -/
theorem removePoles_of_mem (f : ℂ → ℂ) (S : Finset ℂ) (res limVal : ℂ → ℂ) {p : ℂ}
    (hp : p ∈ S) :
    removePoles f S res limVal p = limVal p - ∑ q ∈ S.erase p, res q / (p - q) := by
  simp [removePoles, hp]

/-- Near any `p ∈ S`, `removePoles f S res limVal` agrees on a neighborhood of `p` with
`Function.update (fun s ↦ f s - res p / (s - p)) p (limVal p) s - ∑ q ∈ S.erase p, res q / (s -
q)`. -/
theorem removePoles_eventuallyEq_near_pole (f : ℂ → ℂ) (S : Finset ℂ) (res limVal : ℂ → ℂ)
    {p : ℂ} (hp : p ∈ S) :
    removePoles f S res limVal =ᶠ[𝓝 p] fun s ↦
      Function.update (fun z ↦ f z - res p / (z - p)) p (limVal p) s -
        ∑ q ∈ S.erase p, res q / (s - q) := by
  classical
  have hclosed : IsClosed ((S.erase p : Finset ℂ) : Set ℂ) := (S.erase p).finite_toSet.isClosed
  have hp_notMem : p ∉ ((S.erase p : Finset ℂ) : Set ℂ) := by simp
  filter_upwards [hclosed.isOpen_compl.mem_nhds hp_notMem] with s hs
  rcases eq_or_ne s p with rfl | hsp
  · rw [removePoles_of_mem f S res limVal hp, Function.update_self]
  · have hs_notMem_S : s ∉ S := by
      intro hsS
      exact hs (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hsp, hsS⟩))
    rw [removePoles_of_notMem f S res limVal hs_notMem_S,
      Function.update_of_ne hsp, ← Finset.add_sum_erase S (fun q ↦ res q / (s - q)) hp]
    ring

/-- **Analyticity of `removePoles` at a Pole `p ∈ S`**:
If `f` is complex-differentiable on `𝓝[≠] p` and `f s - res p / (s - p) → limVal p` on `𝓝[≠] p`,
then `removePoles f S res limVal` is analytic at `p`. -/
theorem analyticAt_removePoles_of_mem {f : ℂ → ℂ} {S : Finset ℂ} {res limVal : ℂ → ℂ} {p : ℂ}
    (hp : p ∈ S)
    (hf : ∀ᶠ z in 𝓝[≠] p, DifferentiableAt ℂ f z)
    (hL : Tendsto (fun s ↦ f s - res p / (s - p)) (𝓝[≠] p) (𝓝 (limVal p))) :
    AnalyticAt ℂ (removePoles f S res limVal) p := by
  refine AnalyticAt.congr ?_ (removePoles_eventuallyEq_near_pole f S res limVal hp).symm
  refine (analyticAt_update_sub_inv_sub_of_tendsto hf hL).sub ?_
  have hdiff : DifferentiableOn ℂ (fun s ↦ ∑ q ∈ S.erase p, res q / (s - q))
      (((S.erase p : Finset ℂ) : Set ℂ)ᶜ) := by
    intro s hs
    refine DifferentiableAt.differentiableWithinAt ?_
    refine DifferentiableAt.fun_sum fun q hq ↦ ?_
    have hsq : s - q ≠ 0 := by
      refine sub_ne_zero.mpr fun h ↦ hs ?_
      subst h
      exact Finset.mem_coe.mpr hq
    exact (differentiableAt_const (res q)).div (differentiableAt_id.sub_const q) hsq
  have hopen : IsOpen (((S.erase p : Finset ℂ) : Set ℂ)ᶜ) :=
    (S.erase p).finite_toSet.isClosed.isOpen_compl
  exact (hdiff.analyticOnNhd hopen) p (by simp)

/-- **Differentiability of `removePoles` Away from `S`**:
If `s ∉ S` and `DifferentiableAt ℂ f s`, then `DifferentiableAt ℂ (removePoles f S res limVal) s`.
-/
theorem differentiableAt_removePoles_of_notMem {f : ℂ → ℂ} {S : Finset ℂ} {res limVal : ℂ → ℂ}
    {s : ℂ} (hs : s ∉ S) (hf : DifferentiableAt ℂ f s) :
    DifferentiableAt ℂ (removePoles f S res limVal) s := by
  have hd : DifferentiableAt ℂ (fun z ↦ f z - ∑ q ∈ S, res q / (z - q)) s := by
    refine hf.sub (DifferentiableAt.fun_sum fun q hq ↦ ?_)
    have hsq : s - q ≠ 0 := sub_ne_zero.mpr (fun h ↦ hs (h ▸ hq))
    exact (differentiableAt_const (res q)).div (differentiableAt_id.sub_const q) hsq
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [S.finite_toSet.isClosed.isOpen_compl.mem_nhds hs] with z hz
  exact removePoles_of_notMem f S res limVal hz

/-- **Analyticity of `removePoles` Away from `S`**:
If `s ∉ S` and `AnalyticAt ℂ f s`, then `AnalyticAt ℂ (removePoles f S res limVal) s`. -/
theorem analyticAt_removePoles_of_notMem {f : ℂ → ℂ} {S : Finset ℂ} {res limVal : ℂ → ℂ}
    {s : ℂ} (hs : s ∉ S) (hf : AnalyticAt ℂ f s) :
    AnalyticAt ℂ (removePoles f S res limVal) s := by
  refine Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_
  · filter_upwards [nhdsWithin_le_nhds hf.eventually_analyticAt,
      nhdsWithin_le_nhds (S.finite_toSet.isClosed.isOpen_compl.mem_nhds hs)] with z hfz hzs
    exact differentiableAt_removePoles_of_notMem hzs hfz.differentiableAt
  · exact (differentiableAt_removePoles_of_notMem hs hf.differentiableAt).continuousAt

/-!
## Section 2: Principal-Part Limit Theorems for the Smoothed Perron Integrand
-/

/-- For `0 < x`, `s ↦ (x : ℂ) ^ (s + 1)` is complex-differentiable at every `s : ℂ`. -/
theorem differentiableAt_ofReal_cpow_add_one {x : ℝ} (hx : 0 < x) (s : ℂ) :
    DifferentiableAt ℂ (fun z : ℂ ↦ (x : ℂ) ^ (z + 1)) s :=
  (differentiable_ofReal_cpow_add_one hx).differentiableAt

/-- For `0 < x`, `smoothedPerronKernel x` is complex-differentiable at every `s ≠ 0, -1`. -/
theorem differentiableAt_smoothedPerronKernel {x : ℝ} (hx : 0 < x) {s : ℂ}
    (hs0 : s ≠ 0) (hs_neg1 : s ≠ -1) :
    DifferentiableAt ℂ (smoothedPerronKernel x) s := by
  unfold smoothedPerronKernel
  have hs1 : s + 1 ≠ 0 := add_eq_zero_iff_eq_neg.not.mpr hs_neg1
  exact (differentiableAt_ofReal_cpow_add_one hx s).div
    (differentiableAt_id.mul (differentiableAt_id.add_const 1)) (mul_ne_zero hs0 hs1)

/-- For `0 < x`, `smoothedPerronKernel x` is analytic at every `s ≠ 0, -1`. -/
theorem analyticAt_smoothedPerronKernel {x : ℝ} (hx : 0 < x) {s : ℂ}
    (hs0 : s ≠ 0) (hs_neg1 : s ≠ -1) :
    AnalyticAt ℂ (smoothedPerronKernel x) s := by
  have hopen : IsOpen ({0, -1}ᶜ : Set ℂ) :=
    (isClosed_singleton.union isClosed_singleton).isOpen_compl
  have hdiff : DifferentiableOn ℂ (smoothedPerronKernel x) ({0, -1}ᶜ : Set ℂ) := by
    intro z hz
    simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or] at hz
    exact (differentiableAt_smoothedPerronKernel hx hz.1 hz.2).differentiableWithinAt
  exact (hdiff.analyticOnNhd hopen) s (by simp [hs0, hs_neg1])

/-- At `s = 1`, `smoothedPerronKernel x 1 = (x : ℂ) ^ 2 / 2`. -/
theorem smoothedPerronKernel_one (x : ℝ) :
    smoothedPerronKernel x 1 = (x : ℂ) ^ 2 / 2 := by
  unfold smoothedPerronKernel
  have h1 : (1 : ℂ) + 1 = (2 : ℕ) := by norm_num
  rw [h1, cpow_natCast]
  ring

/-- `riemannZeta` is analytic at every `s ≠ 1`. -/
theorem analyticAt_riemannZeta {s : ℂ} (hs1 : s ≠ 1) :
    AnalyticAt ℂ riemannZeta s :=
  analyticOn_riemannZeta s hs1

/-- `deriv riemannZeta` is analytic at every `s ≠ 1`. -/
theorem analyticAt_deriv_riemannZeta {s : ℂ} (hs1 : s ≠ 1) :
    AnalyticAt ℂ (deriv riemannZeta) s :=
  (analyticAt_riemannZeta hs1).deriv

/-- `deriv riemannZeta` is complex-differentiable at every `s ≠ 1`. -/
theorem differentiableAt_deriv_riemannZeta {s : ℂ} (hs1 : s ≠ 1) :
    DifferentiableAt ℂ (deriv riemannZeta) s :=
  (analyticAt_deriv_riemannZeta hs1).differentiableAt

/-- For `0 < x`, `smoothedPerronIntegrand x` is complex-differentiable at every `s` where
`s ≠ 1`, `s ≠ 0`, `s ≠ -1`, and `riemannZeta s ≠ 0`. -/
theorem differentiableAt_smoothedPerronIntegrand {x : ℝ} (hx : 0 < x) {s : ℂ}
    (hs1 : s ≠ 1) (hs0 : s ≠ 0) (hs_neg1 : s ≠ -1) (hζ : riemannZeta s ≠ 0) :
    DifferentiableAt ℂ (smoothedPerronIntegrand x) s := by
  unfold smoothedPerronIntegrand
  exact ((differentiableAt_deriv_riemannZeta hs1).neg.div
    (differentiableAt_riemannZeta hs1) hζ).mul (differentiableAt_smoothedPerronKernel hx hs0
      hs_neg1)

/-- For `0 < x`, `smoothedPerronIntegrand x` is analytic at every `s` where
`s ≠ 1`, `s ≠ 0`, `s ≠ -1`, and `riemannZeta s ≠ 0`. -/
theorem analyticAt_smoothedPerronIntegrand {x : ℝ} (hx : 0 < x) {s : ℂ}
    (hs1 : s ≠ 1) (hs0 : s ≠ 0) (hs_neg1 : s ≠ -1) (hζ : riemannZeta s ≠ 0) :
    AnalyticAt ℂ (smoothedPerronIntegrand x) s := by
  unfold smoothedPerronIntegrand
  exact ((analyticAt_deriv_riemannZeta hs1).neg.div
    (analyticAt_riemannZeta hs1) hζ).mul (analyticAt_smoothedPerronKernel hx hs0 hs_neg1)

/-!
### Subsection 2.1: Principal Part at $s = 1$
-/

/-- The residue of `smoothedPerronIntegrand x` at `s = 1` is `x ^ 2 / 2`. -/
noncomputable def resOne (x : ℝ) : ℂ :=
  (x : ℂ) ^ 2 / 2

/-- The limit value of `smoothedPerronIntegrand x s - resOne x / (s - 1)` as `s → 1`. -/
noncomputable def limOne (x : ℝ) : ℂ :=
  deriv (smoothedPerronKernel x) 1 -
    (deriv riemannZeta₁ 1 / riemannZeta₁ 1) * smoothedPerronKernel x 1

/-- **Principal-Part Limit Theorem at $s = 1$**:
For `0 < x`, `smoothedPerronIntegrand x s - ((x : ℂ) ^ 2 / 2) / (s - 1) → limOne x`
as `s → 1` in `𝓝[≠] 1`. -/
theorem tendsto_smoothedPerronIntegrand_sub_resOne {x : ℝ} (hx : 0 < x) :
    Tendsto (fun s ↦ smoothedPerronIntegrand x s - resOne x / (s - 1))
      (𝓝[≠] 1) (𝓝 (limOne x)) := by
  have hg_diff : DifferentiableAt ℂ (smoothedPerronKernel x) 1 :=
    differentiableAt_smoothedPerronKernel hx one_ne_zero (by norm_num)
  have ht1 : Tendsto (fun s ↦ (smoothedPerronKernel x s - smoothedPerronKernel x 1) / (s - 1))
      (𝓝[≠] 1) (𝓝 (deriv (smoothedPerronKernel x) 1)) :=
    tendsto_sub_div_sub_of_differentiableAt hg_diff
  have hζ₁_an : AnalyticAt ℂ riemannZeta₁ 1 :=
    (differentiable_riemannZeta₁.differentiableOn.analyticOnNhd isOpen_univ) 1 (mem_univ 1)
  have hζ₁_ne : riemannZeta₁ 1 ≠ 0 := by rw [riemannZeta₁_one]; exact one_ne_zero
  have hc2 : ContinuousAt
      (fun s ↦ (deriv riemannZeta₁ s / riemannZeta₁ s) * smoothedPerronKernel x s) 1 := by
    refine ContinuousAt.mul ?_ hg_diff.continuousAt
    exact hζ₁_an.deriv.continuousAt.div differentiable_riemannZeta₁.continuous.continuousAt hζ₁_ne
  have ht2 : Tendsto
      (fun s ↦ (deriv riemannZeta₁ s / riemannZeta₁ s) * smoothedPerronKernel x s)
      (𝓝[≠] 1) (𝓝 ((deriv riemannZeta₁ 1 / riemannZeta₁ 1) * smoothedPerronKernel x 1)) :=
    hc2.tendsto.mono_left nhdsWithin_le_nhds
  refine (ht1.sub ht2).congr' ?_
  filter_upwards [log_deriv_riemannZeta_eq_neg_inv_sub_add] with s hs
  unfold smoothedPerronIntegrand resOne
  rw [← smoothedPerronKernel_one x, neg_div, hs]
  ring

/-- `smoothedPerronIntegrand x` is complex-differentiable on a punctured neighborhood of `1`. -/
theorem eventually_differentiableAt_smoothedPerronIntegrand_nhdsNE_one {x : ℝ} (hx : 0 < x) :
    ∀ᶠ z in 𝓝[≠] (1 : ℂ), DifferentiableAt ℂ (smoothedPerronIntegrand x) z := by
  have hopen : IsOpen {z : ℂ | (1 / 2 : ℝ) < z.re} := isOpen_lt continuous_const continuous_re
  have hmem : {z : ℂ | (1 / 2 : ℝ) < z.re} ∈ 𝓝[≠] (1 : ℂ) :=
    nhdsWithin_le_nhds (hopen.mem_nhds (by norm_num))
  have hζ₁_ne : ∀ᶠ z in 𝓝[≠] (1 : ℂ), riemannZeta₁ z ≠ 0 := by
    refine nhdsWithin_le_nhds ?_
    refine differentiable_riemannZeta₁.continuous.continuousAt.eventually_ne ?_
    rw [riemannZeta₁_one]
    exact one_ne_zero
  filter_upwards [self_mem_nhdsWithin, hmem, hζ₁_ne] with z hz1 hz_re hz_ζ₁
  have hz0 : z ≠ 0 := by
    intro h; subst h; simp at hz_re; linarith
  have hz_neg1 : z ≠ -1 := by
    intro h; subst h; simp at hz_re; linarith
  have hζ_ne : riemannZeta z ≠ 0 := by
    rw [riemannZeta_eq_inv_sub_mul hz1]
    exact mul_ne_zero (inv_ne_zero (sub_ne_zero.mpr hz1)) hz_ζ₁
  exact differentiableAt_smoothedPerronIntegrand hx hz1 hz0 hz_neg1 hζ_ne

/-!
### Subsection 2.2: Principal Part at $s = 0$
-/

/-- The auxiliary function $h_x(s) = \left(-\frac{\zeta'(s)}{\zeta(s)}\right) \frac{x^{s+1}}{s+1}$,
so that `smoothedPerronIntegrand x s = auxZero x s / s`. -/
noncomputable def auxZero (x : ℝ) (s : ℂ) : ℂ :=
  (-deriv riemannZeta s / riemannZeta s) * ((x : ℂ) ^ (s + 1) / (s + 1))

/-- The residue of `smoothedPerronIntegrand x` at `s = 0`:
`resZero x = (-deriv riemannZeta 0 / riemannZeta 0) * (x : ℂ)`. -/
noncomputable def resZero (x : ℝ) : ℂ :=
  (-deriv riemannZeta 0 / riemannZeta 0) * (x : ℂ)

/-- The limit value of `smoothedPerronIntegrand x s - resZero x / (s - 0)` as `s → 0`. -/
noncomputable def limZero (x : ℝ) : ℂ :=
  deriv (auxZero x) 0

/-- At `s = 0`, `auxZero x 0 = resZero x`. -/
theorem auxZero_zero (x : ℝ) : auxZero x 0 = resZero x := by
  unfold auxZero resZero
  simp

/-- For all `s : ℂ`, `smoothedPerronIntegrand x s = auxZero x s / (s - 0)`. -/
theorem smoothedPerronIntegrand_eq_auxZero_div (x : ℝ) (s : ℂ) :
    smoothedPerronIntegrand x s = auxZero x s / (s - 0) := by
  unfold smoothedPerronIntegrand smoothedPerronKernel auxZero
  rw [sub_zero, div_mul_eq_div_div_swap, mul_div_assoc]

/-- For `0 < x`, `auxZero x` is complex-differentiable at `s = 0`. -/
theorem differentiableAt_auxZero_zero {x : ℝ} (hx : 0 < x) :
    DifferentiableAt ℂ (auxZero x) 0 := by
  unfold auxZero
  have h01 : (0 : ℂ) ≠ 1 := zero_ne_one
  have hζ0 : riemannZeta 0 ≠ 0 := by rw [riemannZeta_zero]; norm_num
  refine ((differentiableAt_deriv_riemannZeta h01).neg.div
    (differentiableAt_riemannZeta h01) hζ0).mul ?_
  exact (differentiableAt_ofReal_cpow_add_one hx 0).div
    (differentiableAt_id.add_const 1) (by norm_num)

/-- **Principal-Part Limit Theorem at $s = 0$**:
For `0 < x`, `smoothedPerronIntegrand x s - resZero x / (s - 0) → limZero x`
as `s → 0` in `𝓝[≠] 0`. -/
theorem tendsto_smoothedPerronIntegrand_sub_resZero {x : ℝ} (hx : 0 < x) :
    Tendsto (fun s ↦ smoothedPerronIntegrand x s - resZero x / (s - 0))
      (𝓝[≠] 0) (𝓝 (limZero x)) := by
  have ht := tendsto_sub_div_sub_of_differentiableAt (differentiableAt_auxZero_zero hx)
  unfold limZero
  refine ht.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s _
  rw [smoothedPerronIntegrand_eq_auxZero_div, ← auxZero_zero, sub_div]

/-- `smoothedPerronIntegrand x` is complex-differentiable on a punctured neighborhood of `0`. -/
theorem eventually_differentiableAt_smoothedPerronIntegrand_nhdsNE_zero {x : ℝ} (hx : 0 < x) :
    ∀ᶠ z in 𝓝[≠] (0 : ℂ), DifferentiableAt ℂ (smoothedPerronIntegrand x) z := by
  have h1 : ({1, -1}ᶜ : Set ℂ) ∈ 𝓝[≠] (0 : ℂ) := by
    refine nhdsWithin_le_nhds ?_
    exact (isClosed_singleton.union isClosed_singleton).isOpen_compl.mem_nhds (by simp)
  have hζ : ∀ᶠ z in 𝓝[≠] (0 : ℂ), riemannZeta z ≠ 0 := by
    refine nhdsWithin_le_nhds ?_
    refine (differentiableAt_riemannZeta zero_ne_one).continuousAt.eventually_ne ?_
    rw [riemannZeta_zero]
    norm_num
  filter_upwards [self_mem_nhdsWithin, h1, hζ] with z hz0 hz1 hz_ζ
  simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or] at hz1
  exact differentiableAt_smoothedPerronIntegrand hx hz1.1 hz0 hz1.2 hz_ζ

/-!
### Subsection 2.3: Principal Part at Any Zero $\rho \ne 0, 1, -1$ of `riemannZeta`
-/

/-- If `riemannZeta ρ = 0` and `ρ ≠ 1`, then `analyticOrderNatAt riemannZeta ρ ≠ 0`. -/
theorem analyticOrderNatAt_riemannZeta_ne_zero {ρ : ℂ} (hζ : riemannZeta ρ = 0) (hρ1 : ρ ≠ 1) :
    analyticOrderNatAt riemannZeta ρ ≠ 0 := by
  have hne_top := analyticOrderAt_riemannZeta_ne_top hρ1
  have hne_zero : analyticOrderAt riemannZeta ρ ≠ 0 := by
    intro h0
    exact ((analyticAt_riemannZeta hρ1).analyticOrderAt_eq_zero.mp h0) hζ
  intro hnat0
  apply hne_zero
  rw [← Nat.cast_analyticOrderNatAt hne_top, hnat0, Nat.cast_zero]

/-- If `u` is analytic at `ρ` with `u ρ ≠ 0` and `riemannZeta =ᶠ[𝓝 ρ] fun z ↦ (z - ρ) ^ m • u z`
with `m ≠ 0`, then on `𝓝[≠] ρ`:
`deriv riemannZeta z / riemannZeta z = (m : ℂ) / (z - ρ) + deriv u z / u z`. -/
theorem eventually_logDeriv_riemannZeta_eq_near_zero {ρ : ℂ} {m : ℕ} {u : ℂ → ℂ}
    (hm : m ≠ 0) (hu_an : AnalyticAt ℂ u ρ) (hu_ne : u ρ ≠ 0)
    (heq : riemannZeta =ᶠ[𝓝 ρ] fun z ↦ (z - ρ) ^ m • u z) :
    ∀ᶠ z in 𝓝[≠] ρ,
      deriv riemannZeta z / riemannZeta z = (m : ℂ) / (z - ρ) + deriv u z / u z := by
  have heq_mul : riemannZeta =ᶠ[𝓝 ρ] fun z ↦ (z - ρ) ^ m * u z := by
    simpa only [smul_eq_mul] using heq
  have hderiv_eq : deriv riemannZeta =ᶠ[𝓝 ρ] deriv (fun z ↦ (z - ρ) ^ m * u z) :=
    heq_mul.deriv
  have hu_diff : ∀ᶠ z in 𝓝 ρ, DifferentiableAt ℂ u z :=
    hu_an.eventually_analyticAt.mono fun _ hz ↦ hz.differentiableAt
  have hu_ne_nhds : ∀ᶠ z in 𝓝 ρ, u z ≠ 0 :=
    hu_an.continuousAt.eventually_ne hu_ne
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds heq_mul,
    nhdsWithin_le_nhds hderiv_eq,
    nhdsWithin_le_nhds hu_diff,
    nhdsWithin_le_nhds hu_ne_nhds] with z hzρ hζ_z hdζ_z hu_z hu_z_ne
  have hpow_deriv : HasDerivAt (fun w : ℂ ↦ (w - ρ) ^ m)
      ((m : ℂ) * (z - ρ) ^ (m - 1)) z := by
    have h1 := ((hasDerivAt_id z).sub_const ρ).pow m
    rw [mul_one] at h1
    exact h1
  have hmul_deriv : deriv (fun w : ℂ ↦ (w - ρ) ^ m * u w) z =
      (m : ℂ) * (z - ρ) ^ (m - 1) * u z + (z - ρ) ^ m * deriv u z :=
    (hpow_deriv.mul hu_z.hasDerivAt).deriv
  rw [hdζ_z, hmul_deriv, hζ_z]
  have hsub_ne : z - ρ ≠ 0 := sub_ne_zero.mpr hzρ
  have hpow_split : (z - ρ) ^ m = (z - ρ) ^ (m - 1) * (z - ρ) := by
    rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hm)]
  have hpow_ne : (z - ρ) ^ (m - 1) ≠ 0 := pow_ne_zero (m - 1) hsub_ne
  rw [hpow_split]
  field_simp

/-- The residue of `smoothedPerronIntegrand x` at a zero `ρ` of `riemannZeta` (`ρ ≠ 0, 1, -1`):
`resZeroRho x ρ = -(analyticOrderNatAt riemannZeta ρ : ℂ) * smoothedPerronKernel x ρ`. -/
noncomputable def resZeroRho (x : ℝ) (ρ : ℂ) : ℂ :=
  -(analyticOrderNatAt riemannZeta ρ : ℂ) * smoothedPerronKernel x ρ

/-- **Existence of the Principal-Part Limit at Any Zero $\rho \ne 0, 1, -1$ of `riemannZeta`**:
If `0 < x`, `riemannZeta ρ = 0`, `ρ ≠ 1`, `ρ ≠ 0`, and `ρ ≠ -1`, then there exists `L : ℂ`
such that `smoothedPerronIntegrand x s - resZeroRho x ρ / (s - ρ) → L` on `𝓝[≠] ρ`. -/
theorem exists_tendsto_smoothedPerronIntegrand_sub_resZeroRho {x : ℝ} (hx : 0 < x) {ρ : ℂ}
    (hζ : riemannZeta ρ = 0) (hρ1 : ρ ≠ 1) (hρ0 : ρ ≠ 0) (hρ_neg1 : ρ ≠ -1) :
    ∃ L : ℂ, Tendsto (fun s ↦ smoothedPerronIntegrand x s - resZeroRho x ρ / (s - ρ))
      (𝓝[≠] ρ) (𝓝 L) := by
  have hne_top := analyticOrderAt_riemannZeta_ne_top hρ1
  obtain ⟨u, hu_an, hu_ne, heq⟩ :=
    (analyticAt_riemannZeta hρ1).analyticOrderAt_ne_top.mp hne_top
  set m := analyticOrderNatAt riemannZeta ρ
  have hm : m ≠ 0 := analyticOrderNatAt_riemannZeta_ne_zero hζ hρ1
  have hlog := eventually_logDeriv_riemannZeta_eq_near_zero hm hu_an hu_ne heq
  have hg_diff : DifferentiableAt ℂ (smoothedPerronKernel x) ρ :=
    differentiableAt_smoothedPerronKernel hx hρ0 hρ_neg1
  refine ⟨-(m : ℂ) * deriv (smoothedPerronKernel x) ρ -
    (deriv u ρ / u ρ) * smoothedPerronKernel x ρ, ?_⟩
  have ht1 : Tendsto
      (fun s ↦ -(m : ℂ) * ((smoothedPerronKernel x s - smoothedPerronKernel x ρ) / (s - ρ)))
      (𝓝[≠] ρ) (𝓝 (-(m : ℂ) * deriv (smoothedPerronKernel x) ρ)) :=
    (tendsto_sub_div_sub_of_differentiableAt hg_diff).const_mul (-(m : ℂ))
  have hc2 : ContinuousAt (fun s ↦ (deriv u s / u s) * smoothedPerronKernel x s) ρ :=
    (hu_an.deriv.continuousAt.div hu_an.continuousAt hu_ne).mul hg_diff.continuousAt
  have ht2 : Tendsto (fun s ↦ (deriv u s / u s) * smoothedPerronKernel x s)
      (𝓝[≠] ρ) (𝓝 ((deriv u ρ / u ρ) * smoothedPerronKernel x ρ)) :=
    hc2.tendsto.mono_left nhdsWithin_le_nhds
  refine (ht1.sub ht2).congr' ?_
  filter_upwards [hlog] with s hs
  unfold smoothedPerronIntegrand resZeroRho
  rw [neg_div, hs]
  ring

/-- The limit value of `smoothedPerronIntegrand x s - resZeroRho x ρ / (s - ρ)` as `s → ρ`. -/
noncomputable def limZeroRho (x : ℝ) (ρ : ℂ) : ℂ :=
  limUnder (𝓝[≠] ρ) (fun s ↦ smoothedPerronIntegrand x s - resZeroRho x ρ / (s - ρ))

/-- **Principal-Part Limit Theorem at Any Zero $\rho \ne 0, 1, -1$ of `riemannZeta`**:
If `0 < x`, `riemannZeta ρ = 0`, `ρ ≠ 1`, `ρ ≠ 0`, and `ρ ≠ -1`, then
`smoothedPerronIntegrand x s - resZeroRho x ρ / (s - ρ) → limZeroRho x ρ` on `𝓝[≠] ρ`. -/
theorem tendsto_smoothedPerronIntegrand_sub_resZeroRho {x : ℝ} (hx : 0 < x) {ρ : ℂ}
    (hζ : riemannZeta ρ = 0) (hρ1 : ρ ≠ 1) (hρ0 : ρ ≠ 0) (hρ_neg1 : ρ ≠ -1) :
    Tendsto (fun s ↦ smoothedPerronIntegrand x s - resZeroRho x ρ / (s - ρ))
      (𝓝[≠] ρ) (𝓝 (limZeroRho x ρ)) := by
  obtain ⟨L, hL⟩ := exists_tendsto_smoothedPerronIntegrand_sub_resZeroRho hx hζ hρ1 hρ0 hρ_neg1
  unfold limZeroRho
  rwa [hL.limUnder_eq]

/-- If `0 < x`, `ρ ≠ 1`, `ρ ≠ 0`, and `ρ ≠ -1`, then `smoothedPerronIntegrand x` is
complex-differentiable on a punctured neighborhood `𝓝[≠] ρ`. -/
theorem eventually_differentiableAt_smoothedPerronIntegrand_nhdsNE_of_ne {x : ℝ} (hx : 0 < x)
    {ρ : ℂ} (hρ1 : ρ ≠ 1) (hρ0 : ρ ≠ 0) (hρ_neg1 : ρ ≠ -1) :
    ∀ᶠ z in 𝓝[≠] ρ, DifferentiableAt ℂ (smoothedPerronIntegrand x) z := by
  have hne_top := analyticOrderAt_riemannZeta_ne_top hρ1
  obtain ⟨u, hu_an, hu_ne, heq⟩ :=
    (analyticAt_riemannZeta hρ1).analyticOrderAt_ne_top.mp hne_top
  have hζ_ne : ∀ᶠ z in 𝓝[≠] ρ, riemannZeta z ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds heq,
      nhdsWithin_le_nhds (hu_an.continuousAt.eventually_ne hu_ne)] with z hzρ hζ_z hu_z
    rw [hζ_z, smul_eq_mul]
    exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr hzρ)) hu_z
  have h_avoid : ({1, 0, -1}ᶜ : Set ℂ) ∈ 𝓝[≠] ρ := by
    refine nhdsWithin_le_nhds ?_
    refine (isClosed_singleton.union (isClosed_singleton.union
      isClosed_singleton)).isOpen_compl.mem_nhds ?_
    simp [hρ1, hρ0, hρ_neg1]
  filter_upwards [h_avoid, hζ_ne] with z hz hζ_z
  simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or] at hz
  exact differentiableAt_smoothedPerronIntegrand hx hz.1 hz.2.1 hz.2.2 hζ_z

/-!
## Section 3: Zero Classification in $\{s \in \mathbb{C} \mid -1/2 < s.\text{re} \wedge
|s.\text{im}| \le T\}$
-/

/-- Every zero `s` of `riemannZeta` with `-1 / 2 < s.re` is a nontrivial zero
(since every trivial zero `-2 * (n + 1)` has real part `≤ -2 < -1 / 2`, and `riemannZeta 1 ≠ 0`). -/
theorem isNontrivialZetaZero_of_re_gt_neg_half {s : ℂ}
    (hζ : riemannZeta s = 0) (hre : -1 / 2 < s.re) :
    IsNontrivialZetaZero s := by
  refine ⟨hζ, ?_, ?_⟩
  · rintro ⟨n, rfl⟩
    have hre_le : (-2 * ((n : ℂ) + 1)).re ≤ -2 := by simp
    linarith
  · rintro rfl
    exact riemannZeta_one_ne_zero hζ

theorem isNontrivialZetaZero_ne_neg_one {s : ℂ} (hs : IsNontrivialZetaZero s) : s ≠ -1 := by
  rintro rfl
  have h := zero_lt_re_of_isNontrivialZetaZero hs
  norm_num at h

/-- **Zero Classification in `{s : ℂ | -1 / 2 < s.re ∧ |s.im| ≤ T}`**:
Every zero `s` of `riemannZeta` in the half-strip `-1 / 2 < s.re` with `|s.im| ≤ T`
belongs to `nontrivialZetaZerosUpTo T`. -/
theorem mem_nontrivialZetaZerosUpTo_of_re_gt_neg_half {T : ℝ} {s : ℂ}
    (hζ : riemannZeta s = 0) (hre : -1 / 2 < s.re) (him : |s.im| ≤ T) :
    s ∈ nontrivialZetaZerosUpTo T :=
  mem_nontrivialZetaZerosUpTo.mpr ⟨isNontrivialZetaZero_of_re_gt_neg_half hζ hre, him⟩

theorem one_notMem_nontrivialZetaZerosUpTo (T : ℝ) :
    (1 : ℂ) ∉ nontrivialZetaZerosUpTo T := by
  intro h
  exact (mem_nontrivialZetaZerosUpTo.mp h).1.2.2 rfl

theorem zero_notMem_nontrivialZetaZerosUpTo (T : ℝ) :
    (0 : ℂ) ∉ nontrivialZetaZerosUpTo T := by
  intro h
  exact isNontrivialZetaZero_ne_zero (mem_nontrivialZetaZerosUpTo.mp h).1 rfl

/-!
## Section 4: Regularized Smoothed Perron Integrand & Rectangle Holomorphicity
-/

/-- The finite set of poles of `smoothedPerronIntegrand x` in the region
`-1 / 2 < s.re ∧ |s.im| ≤ T`, namely `{1, 0} ∪ nontrivialZetaZerosUpTo T`. -/
noncomputable def perronPolesUpTo (T : ℝ) : Finset ℂ :=
  insert (1 : ℂ) (insert (0 : ℂ) (nontrivialZetaZerosUpTo T))

@[simp]
theorem mem_perronPolesUpTo {T : ℝ} {s : ℂ} :
    s ∈ perronPolesUpTo T ↔ s = 1 ∨ s = 0 ∨ s ∈ nontrivialZetaZerosUpTo T := by
  simp [perronPolesUpTo]

/-- The residue of `smoothedPerronIntegrand x` at a pole `p ∈ perronPolesUpTo T`. -/
noncomputable def perronResidue (x : ℝ) (p : ℂ) : ℂ :=
  if p = 1 then resOne x
  else if p = 0 then resZero x
  else resZeroRho x p

/-- The punctured-neighborhood limit of `smoothedPerronIntegrand x s - perronResidue x p / (s - p)`
at a pole `p ∈ perronPolesUpTo T`. -/
noncomputable def perronLimVal (x : ℝ) (p : ℂ) : ℂ :=
  if p = 1 then limOne x
  else if p = 0 then limZero x
  else limZeroRho x p

@[simp]
theorem perronResidue_one (x : ℝ) : perronResidue x 1 = resOne x := by
  simp [perronResidue]

@[simp]
theorem perronResidue_zero (x : ℝ) : perronResidue x 0 = resZero x := by
  simp [perronResidue]

theorem perronResidue_of_mem_nontrivialZetaZerosUpTo (x : ℝ) {T : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ nontrivialZetaZerosUpTo T) :
    perronResidue x ρ = resZeroRho x ρ := by
  have hζ := (mem_nontrivialZetaZerosUpTo.mp hρ).1
  have h1 : ρ ≠ 1 := hζ.2.2
  have h0 : ρ ≠ 0 := isNontrivialZetaZero_ne_zero hζ
  simp [perronResidue, h1, h0]

/-- **The Regularized Smoothed Perron Integrand (`regularizedSmoothedPerron`)**:
Obtained from `smoothedPerronIntegrand x` by subtracting the principal parts at `1`, `0`,
and all `ρ ∈ nontrivialZetaZerosUpTo T` and filling in their removable singularities. -/
noncomputable def regularizedSmoothedPerron (x T : ℝ) (s : ℂ) : ℂ :=
  removePoles (smoothedPerronIntegrand x) (perronPolesUpTo T) (perronResidue x) (perronLimVal x) s

/-- **Explicit Formula for `regularizedSmoothedPerron x T s` Away from the Poles**:
For every `s ∉ perronPolesUpTo T` (i.e., `s ≠ 1`, `s ≠ 0`, and `s ∉ nontrivialZetaZerosUpTo T`),
$$
\text{regularizedSmoothedPerron } x\, T\, s =
  \text{smoothedPerronIntegrand } x\, s
  - \frac{\text{resOne } x}{s - 1}
  - \frac{\text{resZero } x}{s}
  - \sum_{\rho \in \text{nontrivialZetaZerosUpTo } T} \frac{\text{resZeroRho } x\, \rho}{s - \rho}.
$$ -/
theorem regularizedSmoothedPerron_eq_of_notMem (x T : ℝ) {s : ℂ}
    (hs : s ∉ perronPolesUpTo T) :
    regularizedSmoothedPerron x T s =
      smoothedPerronIntegrand x s -
        resOne x / (s - 1) -
        resZero x / s -
        ∑ ρ ∈ nontrivialZetaZerosUpTo T, resZeroRho x ρ / (s - ρ) := by
  unfold regularizedSmoothedPerron
  rw [removePoles_of_notMem _ _ _ _ hs]
  unfold perronPolesUpTo
  have h1_notMem : (1 : ℂ) ∉ insert (0 : ℂ) (nontrivialZetaZerosUpTo T) := by
    rw [Finset.mem_insert, not_or]
    exact ⟨one_ne_zero, one_notMem_nontrivialZetaZerosUpTo T⟩
  have h0_notMem : (0 : ℂ) ∉ nontrivialZetaZerosUpTo T :=
    zero_notMem_nontrivialZetaZerosUpTo T
  rw [Finset.sum_insert h1_notMem, Finset.sum_insert h0_notMem,
    perronResidue_one, perronResidue_zero, sub_zero]
  have hsum : ∑ ρ ∈ nontrivialZetaZerosUpTo T, perronResidue x ρ / (s - ρ) =
      ∑ ρ ∈ nontrivialZetaZerosUpTo T, resZeroRho x ρ / (s - ρ) := by
    refine Finset.sum_congr rfl fun ρ hρ ↦ ?_
    rw [perronResidue_of_mem_nontrivialZetaZerosUpTo x hρ]
  rw [hsum]
  ring

/-- For `0 < x` and every pole `p ∈ perronPolesUpTo T`, `regularizedSmoothedPerron x T` is
analytic at `p`. -/
theorem analyticAt_regularizedSmoothedPerron_of_mem_poles {x T : ℝ} (hx : 0 < x) {p : ℂ}
    (hp : p ∈ perronPolesUpTo T) :
    AnalyticAt ℂ (regularizedSmoothedPerron x T) p := by
  unfold regularizedSmoothedPerron
  rcases mem_perronPolesUpTo.mp hp with rfl | rfl | hρ
  · refine analyticAt_removePoles_of_mem hp
      (eventually_differentiableAt_smoothedPerronIntegrand_nhdsNE_one hx) ?_
    simpa [perronResidue, perronLimVal] using tendsto_smoothedPerronIntegrand_sub_resOne hx
  · refine analyticAt_removePoles_of_mem hp
      (eventually_differentiableAt_smoothedPerronIntegrand_nhdsNE_zero hx) ?_
    simpa [perronResidue, perronLimVal] using tendsto_smoothedPerronIntegrand_sub_resZero hx
  · have hζ := (mem_nontrivialZetaZerosUpTo.mp hρ).1
    have h1 : p ≠ 1 := hζ.2.2
    have h0 : p ≠ 0 := isNontrivialZetaZero_ne_zero hζ
    have h_neg1 : p ≠ -1 := isNontrivialZetaZero_ne_neg_one hζ
    refine analyticAt_removePoles_of_mem hp
      (eventually_differentiableAt_smoothedPerronIntegrand_nhdsNE_of_ne hx h1 h0 h_neg1) ?_
    simpa [perronResidue, perronLimVal, h1, h0] using
      tendsto_smoothedPerronIntegrand_sub_resZeroRho hx hζ.1 h1 h0 h_neg1

/-- **Analyticity of `regularizedSmoothedPerron x T` on `{s : ℂ | -1 / 2 < s.re ∧ |s.im| ≤ T}`**:
For `0 < x`, `regularizedSmoothedPerron x T` is analytic at every `s : ℂ` satisfying
`-1 / 2 < s.re` and `|s.im| ≤ T`. -/
theorem analyticAt_regularizedSmoothedPerron {x T : ℝ} (hx : 0 < x) {s : ℂ}
    (hre : -1 / 2 < s.re) (him : |s.im| ≤ T) :
    AnalyticAt ℂ (regularizedSmoothedPerron x T) s := by
  by_cases hs : s ∈ perronPolesUpTo T
  · exact analyticAt_regularizedSmoothedPerron_of_mem_poles hx hs
  · unfold regularizedSmoothedPerron
    refine analyticAt_removePoles_of_notMem hs ?_
    have hs1 : s ≠ 1 := fun h ↦ hs (mem_perronPolesUpTo.mpr (Or.inl h))
    have hs0 : s ≠ 0 := fun h ↦ hs (mem_perronPolesUpTo.mpr (Or.inr (Or.inl h)))
    have hs_neg1 : s ≠ -1 := by
      rintro rfl
      norm_num at hre
    have hζ : riemannZeta s ≠ 0 := by
      intro hζ0
      exact hs (mem_perronPolesUpTo.mpr
        (Or.inr (Or.inr (mem_nontrivialZetaZerosUpTo_of_re_gt_neg_half hζ0 hre him))))
    exact analyticAt_smoothedPerronIntegrand hx hs1 hs0 hs_neg1 hζ

/-- **Differentiability of `regularizedSmoothedPerron x T` on `{s : ℂ | -1 / 2 < s.re ∧ |s.im| ≤
T}`**:
For `0 < x`, `regularizedSmoothedPerron x T` is complex-differentiable at every `s : ℂ`
satisfying `-1 / 2 < s.re` and `|s.im| ≤ T`. -/
theorem differentiableAt_regularizedSmoothedPerron {x T : ℝ} (hx : 0 < x) {s : ℂ}
    (hre : -1 / 2 < s.re) (him : |s.im| ≤ T) :
    DifferentiableAt ℂ (regularizedSmoothedPerron x T) s :=
  (analyticAt_regularizedSmoothedPerron hx hre him).differentiableAt

/-- The counterclockwise boundary integral of `f : ℂ → ℂ` around the rectangle
`[c₁, c₂] × [-T, T]`, defined purely in terms of four 1D `intervalIntegral`s:
- Right vertical edge `c₂ + t * I` (`t` from `-T` to `T`),
- Left vertical edge `c₁ + t * I` (`t` from `-T` to `T`, negated),
- Top horizontal edge `σ + T * I` (`σ` from `c₁` to `c₂`, negated),
- Bottom horizontal edge `σ - T * I` (`σ` from `c₁` to `c₂`). -/
noncomputable def rectBoundaryIntegral (f : ℂ → ℂ) (c₁ c₂ T : ℝ) : ℂ :=
  (I * ∫ t in (-T)..T, f (c₂ + t * I))
  - (I * ∫ t in (-T)..T, f (c₁ + t * I))
  - (∫ σ in c₁..c₂, f (σ + T * I))
  + (∫ σ in c₁..c₂, f (σ - T * I))

/-- Scaling linearity of `rectBoundaryIntegral`: pulling out a constant `r : ℂ`. -/
theorem rectBoundaryIntegral_const_mul (r : ℂ) (f : ℂ → ℂ) (c₁ c₂ T : ℝ) :
    rectBoundaryIntegral (fun s ↦ r * f s) c₁ c₂ T =
      r * rectBoundaryIntegral f c₁ c₂ T := by
  unfold rectBoundaryIntegral
  simp only [intervalIntegral.integral_const_mul]
  ring

/-- For `a ≠ 0` and any `x : ℝ`, `0 < a ^ 2 + x ^ 2`. -/
theorem add_sq_pos_of_ne_zero {a x : ℝ} (ha : a ≠ 0) : 0 < a ^ 2 + x ^ 2 :=
  add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero ha) (sq_nonneg x)

/-- Real derivative of `u ↦ 1 / 2 * Real.log (a ^ 2 + (u - y₀) ^ 2)` for `a ≠ 0`. -/
theorem hasDerivAt_half_log_add_sq {a y₀ t : ℝ} (ha : a ≠ 0) :
    HasDerivAt (fun u : ℝ ↦ 1 / 2 * Real.log (a ^ 2 + (u - y₀) ^ 2))
      ((t - y₀) / (a ^ 2 + (t - y₀) ^ 2)) t := by
  have hpos : a ^ 2 + (t - y₀) ^ 2 ≠ 0 := (add_sq_pos_of_ne_zero ha).ne'
  have hd_inner : HasDerivAt (fun u : ℝ ↦ a ^ 2 + (u - y₀) ^ 2) (2 * (t - y₀)) t := by
    have hd1 : HasDerivAt (fun u : ℝ ↦ (u - y₀) ^ 2) (2 * (t - y₀) ^ (2 - 1) * 1) t :=
      ((hasDerivAt_id t).sub_const y₀).pow 2
    simpa [Pi.pow_def] using hd1.const_add (a ^ 2)
  have hd := ((Real.hasDerivAt_log hpos).comp t hd_inner).const_mul (1 / 2)
  refine hd.congr_deriv ?_
  ring

/-- Real derivative of `u ↦ Real.arctan ((u - y₀) / a)` for `a ≠ 0`. -/
theorem hasDerivAt_arctan_sub_div {a y₀ t : ℝ} (ha : a ≠ 0) :
    HasDerivAt (fun u : ℝ ↦ Real.arctan ((u - y₀) / a))
      (a / (a ^ 2 + (t - y₀) ^ 2)) t := by
  have hpos : a ^ 2 + (t - y₀) ^ 2 ≠ 0 := (add_sq_pos_of_ne_zero ha).ne'
  have hd_inner : HasDerivAt (fun u : ℝ ↦ (u - y₀) / a) (1 / a) t :=
    ((hasDerivAt_id t).sub_const y₀).div_const a
  have hd := hd_inner.arctan
  refine hd.congr_deriv ?_
  field_simp [ha, hpos]

/-- If `a ≠ 0`, then `(a : ℂ) + (b : ℂ) * I ≠ 0`. -/
theorem complex_add_mul_I_ne_zero_of_left {a b : ℝ} (ha : a ≠ 0) :
    (a : ℂ) + (b : ℂ) * I ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  exact ha (by simpa using hre)

/-- If `b ≠ 0`, then `(a : ℂ) + (b : ℂ) * I ≠ 0`. -/
theorem complex_add_mul_I_ne_zero_of_right {a b : ℝ} (hb : b ≠ 0) :
    (a : ℂ) + (b : ℂ) * I ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  exact hb (by simpa using him)

/-- **Vertical 1D Antiderivative**:
For `a ≠ 0` (`a = c - p.re`) and `y₀ = p.im`, the complex antiderivative of
`t ↦ I / (a + (t - y₀) * I)` along the vertical line `s = c + t * I`. -/
noncomputable def vertPoleAntideriv (a y₀ u : ℝ) : ℂ :=
  ((1 / 2 * Real.log (a ^ 2 + (u - y₀) ^ 2) : ℝ) : ℂ) +
    I * ((Real.arctan ((u - y₀) / a) : ℝ) : ℂ)

/-- **Horizontal 1D Antiderivative**:
For `b ≠ 0` (`b = y - p.im`) and `x₀ = p.re`, the complex antiderivative of
`σ ↦ 1 / ((σ - x₀) + b * I)` along the horizontal line `s = σ + y * I`. -/
noncomputable def horizPoleAntideriv (b x₀ u : ℝ) : ℂ :=
  ((1 / 2 * Real.log ((u - x₀) ^ 2 + b ^ 2) : ℝ) : ℂ) -
    I * ((Real.arctan ((u - x₀) / b) : ℝ) : ℂ)

/-- Exact 1D `HasDerivAt` for `vertPoleAntideriv a y₀` when `a ≠ 0`. -/
theorem hasDerivAt_vertPoleAntideriv {a y₀ t : ℝ} (ha : a ≠ 0) :
    HasDerivAt (vertPoleAntideriv a y₀)
      (I / ((a : ℂ) + ((t - y₀ : ℝ) : ℂ) * I)) t := by
  unfold vertPoleAntideriv
  have hd1 := (hasDerivAt_half_log_add_sq ha (y₀ := y₀) (t := t)).ofReal_comp
  have hd2 := ((hasDerivAt_arctan_sub_div ha (y₀ := y₀) (t := t)).ofReal_comp).const_mul I
  refine (hd1.add hd2).congr_deriv ?_
  have hpos : (a : ℂ) ^ 2 + ((t : ℂ) - y₀) ^ 2 ≠ 0 := by
    exact_mod_cast (add_sq_pos_of_ne_zero ha (x := t - y₀)).ne'
  have hden : (a : ℂ) + ((t - y₀ : ℝ) : ℂ) * I ≠ 0 :=
    complex_add_mul_I_ne_zero_of_left ha
  push_cast at hden ⊢
  rw [← mul_div_assoc, ← add_div, div_eq_div_iff hpos hden]
  linear_combination (a : ℂ) * ((t : ℂ) - y₀) * Complex.I_sq

/-- Exact 1D `HasDerivAt` for `horizPoleAntideriv b x₀` when `b ≠ 0`. -/
theorem hasDerivAt_horizPoleAntideriv {b x₀ σ : ℝ} (hb : b ≠ 0) :
    HasDerivAt (horizPoleAntideriv b x₀)
      (1 / (((σ - x₀ : ℝ) : ℂ) + (b : ℂ) * I)) σ := by
  have h_eq : horizPoleAntideriv b x₀ = fun u : ℝ ↦
      ((1 / 2 * Real.log (b ^ 2 + (u - x₀) ^ 2) : ℝ) : ℂ) -
        I * ((Real.arctan ((u - x₀) / b) : ℝ) : ℂ) := by
    ext u
    simp only [horizPoleAntideriv, add_comm ((u - x₀) ^ 2) (b ^ 2)]
  rw [h_eq]
  have hd1 := (hasDerivAt_half_log_add_sq hb (y₀ := x₀) (t := σ)).ofReal_comp
  have hd2 := ((hasDerivAt_arctan_sub_div hb (y₀ := x₀) (t := σ)).ofReal_comp).const_mul I
  refine (hd1.sub hd2).congr_deriv ?_
  have hpos : (b : ℂ) ^ 2 + ((σ : ℂ) - x₀) ^ 2 ≠ 0 := by
    exact_mod_cast (add_sq_pos_of_ne_zero hb (x := σ - x₀)).ne'
  have hden : ((σ - x₀ : ℝ) : ℂ) + (b : ℂ) * I ≠ 0 :=
    complex_add_mul_I_ne_zero_of_right hb
  push_cast at hden ⊢
  rw [← mul_div_assoc, ← sub_div, div_eq_div_iff hpos hden]
  linear_combination -(b : ℂ) ^ 2 * Complex.I_sq

/-- Decomposition of `(c : ℂ) + (t : ℂ) * I - p` into real and imaginary offsets. -/
theorem vertical_sub_eq (c t : ℝ) (p : ℂ) :
    (c : ℂ) + (t : ℂ) * I - p =
      ((c - p.re : ℝ) : ℂ) + ((t - p.im : ℝ) : ℂ) * I := by
  apply Complex.ext <;> simp

/-- Decomposition of `(σ : ℂ) + (y : ℂ) * I - p` into real and imaginary offsets. -/
theorem horizontal_sub_eq (σ y : ℝ) (p : ℂ) :
    (σ : ℂ) + (y : ℂ) * I - p =
      ((σ - p.re : ℝ) : ℂ) + ((y - p.im : ℝ) : ℂ) * I := by
  apply Complex.ext <;> simp

/-- **Closed-Form 1D Vertical Integral of `I / (a + (t - y₀) * I)`**:
For `a ≠ 0` and any `y₀, t₁, t₂ : ℝ`,
$$\int_{t_1}^{t_2} \frac{i}{a + (t - y_0) i} \, dt
  = \Phi_{\text{vert}}(a, y_0, t_2) - \Phi_{\text{vert}}(a, y_0, t_1).$$ -/
theorem intervalIntegral_I_div_add_mul_I {a y₀ : ℝ} (ha : a ≠ 0) (t₁ t₂ : ℝ) :
    (∫ t : ℝ in t₁..t₂, I / ((a : ℂ) + ((t - y₀ : ℝ) : ℂ) * I)) =
      vertPoleAntideriv a y₀ t₂ - vertPoleAntideriv a y₀ t₁ := by
  have hderiv : ∀ t ∈ Set.uIcc t₁ t₂,
      HasDerivAt (vertPoleAntideriv a y₀)
        (I / ((a : ℂ) + ((t - y₀ : ℝ) : ℂ) * I)) t :=
    fun t _ ↦ hasDerivAt_vertPoleAntideriv ha
  have hcont : Continuous (fun t : ℝ ↦ I / ((a : ℂ) + ((t - y₀ : ℝ) : ℂ) * I)) := by
    refine continuous_const.div ?_ (fun t ↦ complex_add_mul_I_ne_zero_of_left ha)
    fun_prop
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable t₁ t₂)

/-- **Closed-Form 1D Horizontal Integral of `1 / ((σ - x₀) + b * I)`**:
For `b ≠ 0` and any `x₀, c₁, c₂ : ℝ`,
$$\int_{c_1}^{c_2} \frac{1}{(\sigma - x_0) + b i} \, d\sigma
  = \Phi_{\text{horiz}}(b, x_0, c_2) - \Phi_{\text{horiz}}(b, x_0, c_1).$$ -/
theorem intervalIntegral_one_div_add_mul_I {b x₀ : ℝ} (hb : b ≠ 0) (c₁ c₂ : ℝ) :
    (∫ σ : ℝ in c₁..c₂, 1 / (((σ - x₀ : ℝ) : ℂ) + (b : ℂ) * I)) =
      horizPoleAntideriv b x₀ c₂ - horizPoleAntideriv b x₀ c₁ := by
  have hderiv : ∀ σ ∈ Set.uIcc c₁ c₂,
      HasDerivAt (horizPoleAntideriv b x₀)
        (1 / (((σ - x₀ : ℝ) : ℂ) + (b : ℂ) * I)) σ :=
    fun σ _ ↦ hasDerivAt_horizPoleAntideriv hb
  have hcont : Continuous (fun σ : ℝ ↦ 1 / (((σ - x₀ : ℝ) : ℂ) + (b : ℂ) * I)) := by
    refine continuous_const.div ?_ (fun σ ↦ complex_add_mul_I_ne_zero_of_right hb)
    fun_prop
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable c₁ c₂)

/-- Vertical line integral of `1 / (c + t * I - p)` multiplied by `I` when `c ≠ p.re`. -/
theorem mul_I_vertical_integral_inv_sub_eq {c : ℝ} {p : ℂ} (hc : c ≠ p.re) (T : ℝ) :
    I * (∫ t : ℝ in (-T)..T, 1 / ((c : ℂ) + (t : ℂ) * I - p)) =
      vertPoleAntideriv (c - p.re) p.im T - vertPoleAntideriv (c - p.re) p.im (-T) := by
  rw [← intervalIntegral.integral_const_mul]
  have h_fn :
      (fun t : ℝ ↦ I * (1 / ((c : ℂ) + (t : ℂ) * I - p))) =
        fun t : ℝ ↦ I / (((c - p.re : ℝ) : ℂ) + ((t - p.im : ℝ) : ℂ) * I) := by
    ext t
    rw [vertical_sub_eq, mul_one_div]
  rw [h_fn]
  exact intervalIntegral_I_div_add_mul_I (sub_ne_zero.mpr hc) (-T) T

end ConjectureMachines.Semantics.Riemann.WeightedStieltjes
