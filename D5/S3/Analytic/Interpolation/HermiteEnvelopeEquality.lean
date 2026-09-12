/- GID: D5/S3/Analytic/Interpolation/HermiteEnvelopeEquality
   generality: G
   mirror-B: D5/B/S3/Analytic/Interpolation/HermiteEnvelopeEquality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Equality in the Hermite logarithmic bound characterizes the two moment nodes and their multiplicities. -/

import D5.S3.Analytic.Interpolation.HermiteUpperEnvelope
import D5.S3.Analytic.Interpolation.LogOneSubExpDerivatives
import D5.S3.Analytic.Interpolation.HermiteMomentBounds
import Mathlib.Geometry.Manifold.PartitionOfUnity

open Set Filter
open scoped Topology ContDiff Manifold

noncomputable section

namespace D5.S3.Analytic.Interpolation.HermiteEnvelopeEquality

private theorem extension_near_interval {s : Set ℝ} (hs : IsOpen s)
    (L H : ℝ) (hsub : Icc L H ⊆ s) (f : ℝ → ℝ) (hf : ContDiffOn ℝ 3 f s) :
    ∃ g : ℝ → ℝ, ContDiff ℝ 3 g ∧ ∀ x ∈ Icc L H, g =ᶠ[𝓝 x] f := by
  obtain ⟨K, hKnhds, hKclosed, hKs⟩ :=
    exists_mem_nhdsSet_isClosed_subset (hs.mem_nhdsSet.mpr hsub) isClosed_Icc
  let t : ℝ → Set ℝ := fun x => {y | x ∈ K → y = f x}
  have ht (x : ℝ) : Convex ℝ (t x) := (convex_singleton (f x)).setOfPred_const_imp
  have hlocal : ∀ x : ℝ, ∃ U ∈ 𝓝 x, ∃ g : ℝ → ℝ,
      ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) 3 g U ∧ ∀ y ∈ U, g y ∈ t y := by
    intro x
    by_cases hx : x ∈ K
    · refine ⟨s, hs.mem_nhds (hKs hx), f, hf.contMDiffOn, ?_⟩
      intro y hy hKy
      exact Eq.refl _
    · refine ⟨Kᶜ, hKclosed.isOpen_compl.mem_nhds hx, fun _ => 0, contMDiffOn_const, ?_⟩
      intro y hy hKy
      exact (hy hKy).elim
  obtain ⟨g, hg⟩ := exists_contMDiffMap_forall_mem_convex_of_local
      (I := 𝓘(ℝ, ℝ)) (n := 3) ht hlocal
  refine ⟨g, g.contMDiff.contDiff, ?_⟩
  intro x hx
  filter_upwards [mem_nhdsSet_iff_forall.mp hKnhds x hx] with y hy
  exact hg y hy


/-- A positive third derivative forces strict negativity left of a double zero. -/
theorem negative_left_of_double_node (x L H : ℝ) (g : ℝ → ℝ)
    (hxL : x < L) (hLH : L < H) (hg : ContDiff ℝ 3 g)
    (hgL : g L = 0) (hgH : g H = 0) (hdL : deriv g L = 0)
    (hpos : ∀ t ∈ Ioo x H, 0 < iteratedDeriv 3 g t) : g x < 0 := by
  by_contra hn
  have hnonneg : 0 ≤ g x := le_of_not_gt hn
  have hc1 : Continuous (deriv g) := by
    simpa only [iteratedDeriv_one] using hg.continuous_iteratedDeriv 1 (by norm_num)
  have hd1 : Differentiable ℝ (deriv g) := by
    simpa only [iteratedDeriv_one] using hg.differentiable_iteratedDeriv 1 (by norm_num)
  have hc2 : Continuous (deriv (deriv g)) := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
      hg.continuous_iteratedDeriv 2 (by norm_num)
  obtain ⟨u, hu, hdu⟩ := exists_deriv_eq_slope g hxL hg.continuous.continuousOn
    (hg.differentiable (by norm_num)).differentiableOn
  have hu0 : deriv g u ≤ 0 := by
    rw [hdu, hgL]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (sub_nonneg.mpr hxL.le)
  obtain ⟨a, ha, hda⟩ := exists_deriv_eq_slope (deriv g) hu.2 hc1.continuousOn
    hd1.differentiableOn
  have ha0 : 0 ≤ deriv (deriv g) a := by
    rw [hda, hdL]
    exact div_nonneg (by linarith) (sub_nonneg.mpr hu.2.le)
  obtain ⟨v, hv, hdv⟩ := exists_deriv_eq_zero hLH hg.continuous.continuousOn
    (hgL.trans hgH.symm)
  obtain ⟨b, hb, hdb⟩ := exists_deriv_eq_zero hv.1 hc1.continuousOn (hdL.trans hdv.symm)
  have hm : StrictMonoOn (deriv (deriv g)) (Ioo x H) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioo x H) hc2.continuousOn
    intro t ht
    have ht' : t ∈ Ioo x H := interior_subset ht
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hpos t ht'
  have hab := hm ⟨hu.1.trans ha.1, ha.2.trans hLH⟩
    ⟨hxL.trans hb.1, hb.2.trans hv.2⟩ (ha.2.trans hb.1)
  linarith


private theorem hermite_strict_majorant (L H x : ℝ) (f p : ℝ → ℝ)
    (hL : 0 < L) (hLH : L < H) (hx : 0 < x) (hxH : x ≤ H)
    (hxLne : x ≠ L) (hxHne : x ≠ H)
    (hf : ContDiffOn ℝ 3 f (Ioi 0)) (hp : ContDiff ℝ 3 p)
    (hzero : ∀ t, iteratedDeriv 3 p t = 0)
    (hvalL : p L = f L) (hderL : deriv p L = deriv f L) (hvalH : p H = f H)
    (hpos : ∀ t ∈ Ioi (0 : ℝ), 0 < iteratedDeriv 3 f t) : f x < p x := by
  rcases lt_trichotomy x L with hxL | rfl | hLx
  · obtain ⟨g, hg, heq⟩ := extension_near_interval isOpen_Ioi x H
      (fun t ht => hx.trans_le ht.1) (f - p) (hf.sub hp.contDiffOn)
    have hLm : L ∈ Icc x H := ⟨hxL.le, hLH.le⟩
    have hHm : H ∈ Icc x H := ⟨hxH, le_rfl⟩
    have hgL : g L = 0 := by
      rw [(heq L hLm).eq_of_nhds, Pi.sub_apply, hvalL, sub_self]
    have hgH : g H = 0 := by
      rw [(heq H hHm).eq_of_nhds, Pi.sub_apply, hvalH, sub_self]
    have hdL : deriv g L = 0 := by
      rw [(heq L hLm).deriv_eq,
        deriv_sub ((hf.contDiffAt (isOpen_Ioi.mem_nhds hL)).differentiableAt (by norm_num))
          (hp.differentiable (by norm_num)).differentiableAt]
      exact sub_eq_zero.mpr hderL.symm
    have hthird (t : ℝ) (ht : t ∈ Ioo x H) : 0 < iteratedDeriv 3 g t := by
      have ht0 : t ∈ Ioi (0 : ℝ) := hx.trans ht.1
      rw [(heq t (Ioo_subset_Icc_self ht)).iteratedDeriv_eq 3,
        iteratedDeriv_sub (hf.contDiffAt (isOpen_Ioi.mem_nhds ht0)) hp.contDiffAt,
        hzero t, sub_zero]
      exact hpos t ht0
    have hneg := negative_left_of_double_node x L H g hxL hLH hg hgL hgH hdL hthird
    rw [(heq x ⟨le_rfl, hxH⟩).eq_of_nhds, Pi.sub_apply] at hneg
    linarith
  · exact (hxLne rfl).elim
  · rcases lt_or_eq_of_le hxH with hxH' | rfl
    · obtain ⟨ξ, hξ, hrem, hneg⟩ := HermiteUpperEnvelope.hermite_two_point_remainder_on isOpen_Ioi L H x
        (fun t ht => hL.trans_le ht.1) f p ⟨hLx, hxH'⟩ hf hp.contDiffOn
        (fun t _ => hzero t) hvalL hderL hvalH (fun t ht => hpos t (hL.trans ht.1))
      linarith
    · exact (hxHne rfl).elim

private theorem quadratic_derivatives (a b c L : ℝ) :
    deriv (fun t : ℝ => a + b * (t - L) + c * (t - L)^2) L = b ∧
      ∀ t, iteratedDeriv 3 (fun t : ℝ => a + b * (t - L) + c * (t - L)^2) t = 0 := by
  have hd : deriv (fun t : ℝ => a + b * (t - L) + c * (t - L)^2) =
      fun t => b + 2 * c * (t - L) := by
    funext t
    convert (((hasDerivAt_const t a).add (((hasDerivAt_id t).sub_const L).const_mul b)).add
      ((((hasDerivAt_id t).sub_const L).pow 2).const_mul c)).deriv using 1
    · congr 1
    · simp only [id_eq]
      ring
  have hd2 : deriv (fun t : ℝ => b + 2 * c * (t - L)) = fun _ => 2 * c := by
    funext t
    simp
  constructor
  · rw [hd]; ring
  · simp [iteratedDeriv_succ, iteratedDeriv_zero, hd, hd2]

private theorem quadratic_sum_of_moments {k : ℕ} (x : Fin k → ℝ) (μ r a b c : ℝ)
    (hsum : ∑ i, x i = (k : ℝ) * μ)
    (hvar : ∑ i, (x i - μ)^2 = (k : ℝ) * ((k : ℝ) - 1) * r^2) :
    let p := fun t => a + b * (t - (μ - r)) + c * (t - (μ - r))^2
    ∑ i, p (x i) = p (μ + ((k : ℝ) - 1) * r) + ((k : ℝ) - 1) * p (μ - r) := by
  have hcenter : ∑ i, (x i - μ) = 0 := by
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    linarith
  have hfirst : ∑ i, (x i - (μ - r)) = (k : ℝ) * r := by
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [hsum]
    ring
  have hsecond : ∑ i, (x i - (μ - r))^2 = (k : ℝ)^2 * r^2 := by
    simp_rw [show ∀ i, (x i - (μ - r))^2 = (x i - μ)^2 + 2*r*(x i - μ) + r^2
      from fun i => by ring]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hcenter, hvar]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  dsimp only
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    hfirst, hsecond]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring


#print axioms negative_left_of_double_node
#print axioms hermite_strict_majorant

end D5.S3.Analytic.Interpolation.HermiteEnvelopeEquality
