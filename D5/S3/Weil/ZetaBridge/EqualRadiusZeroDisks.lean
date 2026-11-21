/- GID: D5/S3/Weil/ZetaBridge/EqualRadiusZeroDisks
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/EqualRadiusZeroDisks
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: An off-line zeta zero gives equal-radius disks on one vertical line with a unique zero in one and none in the other. -/

import D5.S3.Weil.ZetaBridge.AlternatingZetaContinuation
import Mathlib.NumberTheory.LSeries.ZetaZeros
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Topology.MetricSpace.HausdorffDistance

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Complex Set Metric

namespace D5.S3.Weil.ZetaBridge.EqualRadiusZeroDisks

private theorem zero_re_lt_one {z : ℂ} (hz : z ∈ riemannZetaZeros) : z.re < 1 :=
  lt_of_not_ge fun h => riemannZeta_ne_zero_of_one_le_re h hz

private theorem dist_sq_vertical (σ t : ℝ) (z : ℂ) :
    dist (⟨σ,t⟩ : ℂ) z ^ 2 = (σ-z.re)^2 + (t-z.im)^2 := by
  rw [dist_eq_norm, Complex.sq_norm, Complex.normSq_apply]
  simp [pow_two]

private theorem untied_ordinates (σ : ℝ) (hσ : 2 < σ) :
    Dense {t : ℝ | Set.InjOn (dist (⟨σ,t⟩ : ℂ)) riemannZetaZeros} := by
  classical
  let K (z w : ℂ) : ℝ :=
    ((σ-w.re)^2 + w.im^2 - (σ-z.re)^2 - z.im^2) / (2*(w.im-z.im))
  have hct := isClosed_riemannZetaZeros.isLindelof.countable_of_isDiscrete isDiscrete_riemannZetaZeros
  have hct' := (hct.prod hct).image (fun p : ℂ × ℂ => K p.1 p.2)
  apply (hct'.dense_compl ℝ).mono
  intro t ht z hz w hw he
  have hs := congrArg (fun a : ℝ => a^2) he
  change dist (⟨σ,t⟩ : ℂ) z ^ 2 = dist (⟨σ,t⟩ : ℂ) w ^ 2 at hs
  rw [dist_sq_vertical, dist_sq_vertical] at hs
  by_cases hi : z.im = w.im
  · apply Complex.ext _ hi
    rw [hi] at hs
    have hz1 := zero_re_lt_one hz
    have hw1 := zero_re_lt_one hw
    have e : (σ-z.re)^2 = (σ-w.re)^2 := by linarith
    have := (sq_eq_sq₀ (a := σ-z.re) (b := σ-w.re) (by linarith) (by linarith)).mp e
    linarith
  · exfalso
    apply ht
    refine ⟨(z,w), ⟨hz,hw⟩, ?_⟩
    change K z w = t
    apply (div_eq_iff (mul_ne_zero (by norm_num) (sub_ne_zero.mpr (Ne.symm hi)))).2
    nlinarith

private theorem projected_distance (σ : ℝ) (hσ : 2 < σ) {z : ℂ} (hz : z ∈ riemannZetaZeros) :
    dist (⟨σ,z.im⟩ : ℂ) z = σ-z.re := by
  have hs := dist_sq_vertical σ z.im z
  simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero] at hs
  have h := zero_re_lt_one hz
  exact (sq_eq_sq₀ dist_nonneg (by linarith)).mp hs

private theorem first_ordinate (σ : ℝ) (hσ : 2 < σ) {z₀ : ℂ} (hz₀ : z₀ ∈ riemannZetaZeros)
    {δ : ℝ} (hδ : 0 < δ) (hloss : δ < z₀.re - 1/2) :
    ∃ t : ℝ, ∃ z ∈ riemannZetaZeros, dist (⟨σ,t⟩ : ℂ) z <
      min (infDist (σ : ℂ) riemannZetaZeros) (σ-z₀.re+δ) := by
  obtain ⟨w, hw, hdist⟩ := isClosed_riemannZetaZeros.exists_infDist_eq_dist ⟨z₀,hz₀⟩ (σ : ℂ)
  by_cases h : σ-z₀.re+δ ≤ dist (σ : ℂ) w
  · refine ⟨z₀.im, z₀, hz₀, ?_⟩
    rw [hdist, min_eq_right h, projected_distance σ hσ hz₀]
    linarith
  · have hw1 := zero_re_lt_one hw
    have hre := Complex.re_le_norm ((σ : ℂ)-w)
    simp only [Complex.sub_re, Complex.ofReal_re, ← dist_eq_norm] at hre
    have him : w.im ≠ 0 := by
      intro hwr
      have heq : (w.re : ℂ) = w := Complex.ext rfl (by simpa using hwr.symm)
      exact AlternatingZetaContinuation.riemannZeta_ne_zero_of_real_mem_Ioo w.re
        (by linarith [lt_of_not_ge h]) hw1 (heq ▸ hw)
    refine ⟨w.im, w, hw, ?_⟩
    rw [hdist, min_eq_left (le_of_not_ge h), projected_distance σ hσ hw]
    have hs := dist_sq_vertical σ 0 w
    change dist (σ : ℂ) w ^ 2 = _ at hs
    nlinarith [sq_pos_of_ne_zero him]

private theorem radius_gap {p z : ℂ} {R : ℝ}
    (hd : dist p z < R) (hne : ∀ w ∈ riemannZetaZeros, w ≠ z → dist p z < dist p w) :
    ∃ r : ℝ, dist p z < r ∧ r < R ∧ ∀ w ∈ closedBall p r, riemannZeta w = 0 → w = z := by
  let S := riemannZetaZeros \ {z}
  have hclosed : IsClosed S :=
    isClosed_of_subset_discrete_closed sdiff_subset isDiscrete_riemannZetaZeros isClosed_riemannZetaZeros
  by_cases hS : S.Nonempty
  · obtain ⟨w, hw, hwD⟩ := hclosed.exists_infDist_eq_dist hS p
    have hlt := hne w hw.1 hw.2
    obtain ⟨r, hr, hR⟩ := exists_between (lt_min hd hlt)
    refine ⟨r, hr, hR.trans_le (min_le_left _ _), fun y hy hy0 => ?_⟩
    by_contra he
    have hdist := infDist_le_dist_of_mem (x := p) (show y ∈ S from ⟨hy0,he⟩)
    rw [hwD] at hdist
    rw [mem_closedBall, dist_comm] at hy
    linarith [min_le_right R (dist p w)]
  · obtain ⟨r, hr, hR⟩ := exists_between hd
    exact ⟨r, hr, hR, fun w _ hw => by
      by_contra h
      exact hS ⟨w,hw,h⟩⟩

/-- A zero right of one-half yields an empty real disk and a singly occupied
vertically shifted disk, both of the same strictly controlled radius. -/
theorem equal_radius_zero_disks {z₀ : ℂ} (hz₀ : riemannZeta z₀ = 0)
    {σ δ : ℝ} (hσ : 2 < σ) (hδ : 0 < δ) (hloss : δ < z₀.re - 1/2) :
    ∃ (p ρ : ℂ) (r : ℝ), p.re = σ ∧ riemannZeta ρ = 0 ∧
      0 < dist p ρ ∧ dist p ρ < r ∧ r < σ-z₀.re+δ ∧
      (∀ w ∈ closedBall (σ : ℂ) r, 1/2 < w.re ∧ riemannZeta w ≠ 0) ∧
      (∀ w ∈ closedBall p r, 1/2 < w.re ∧ (riemannZeta w = 0 → w = ρ)) := by
  let R := min (infDist (σ : ℂ) riemannZetaZeros) (σ-z₀.re+δ)
  obtain ⟨t₀,z,hz,ht₀⟩ := first_ordinate σ hσ hz₀ hδ hloss
  let V := {t : ℝ | dist (⟨σ,t⟩ : ℂ) z < R}
  have hcont : Continuous (fun t : ℝ => (⟨σ,t⟩ : ℂ)) := by
    simpa only [Complex.mk_eq_add_mul_I] using (show Continuous (fun t : ℝ => (σ : ℂ) + (t : ℂ) * I) by fun_prop)
  have ho : IsOpen V := isOpen_lt (hcont.dist continuous_const) continuous_const
  obtain ⟨t, htV, ht⟩ := (untied_ordinates σ hσ).inter_open_nonempty V ho ⟨t₀,ht₀⟩
  let p : ℂ := ⟨σ,t⟩
  obtain ⟨ρ, hρ, hD⟩ := isClosed_riemannZetaZeros.exists_infDist_eq_dist ⟨z,hz⟩ p
  have hmin (w : ℂ) (hw : w ∈ riemannZetaZeros) : dist p ρ ≤ dist p w :=
    hD ▸ infDist_le_dist_of_mem hw
  have hdR : dist p ρ < R := (hmin z hz).trans_lt htV
  obtain ⟨r,hr,hrR,huniq⟩ := radius_gap hdR (fun w hw h => lt_of_le_of_ne (hmin w hw)
    (fun he => h (ht hρ hw he).symm))
  have hbound : r < σ-z₀.re+δ := hrR.trans_le (min_le_right _ _)
  have halfplane (q w : ℂ) (hq : q.re = σ) (hw : w ∈ closedBall q r) : 1/2 < w.re := by
    have h := Complex.re_le_norm (q-w)
    rw [Complex.sub_re, hq, ← dist_eq_norm] at h
    rw [mem_closedBall, dist_comm] at hw
    linarith
  have hpr : p.re = σ := rfl
  refine ⟨p,ρ,r,hpr,hρ,dist_pos.mpr ?_,hr,hbound,?_,fun w hw => ⟨halfplane p w hpr hw, huniq w hw⟩⟩
  · intro he
    have := zero_re_lt_one hρ
    rw [← he, hpr] at this
    linarith
  · intro w hw
    refine ⟨halfplane _ w rfl hw, fun h => ?_⟩
    have hd := infDist_le_dist_of_mem (x := (σ : ℂ)) (show w ∈ riemannZetaZeros from h)
    rw [mem_closedBall, dist_comm] at hw
    exact (hrR.trans_le (min_le_left _ _)).not_ge (hd.trans hw)

end D5.S3.Weil.ZetaBridge.EqualRadiusZeroDisks
