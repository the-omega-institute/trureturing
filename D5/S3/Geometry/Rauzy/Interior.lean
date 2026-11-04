/- GID: D5/S3/Geometry/Rauzy/Interior
   generality: I
   mirror-B: D5/B/S3/Geometry/Rauzy/Interior
   mirror-E: none(waiver:unbounded-analytic-existence)
   anchors: []
   utility: none
   digest: Synchronized limiting cylinder clusters cover a disk at a planar density point. -/

import D5.S0.Tower.Tribonacci.RauzyFractal
import Mathlib.Topology.Sequences
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.Baire.Lemmas
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
The exact application target is

  theorem rauzyFractal_interior_nonempty {z : Complex}
    (hz : z ∈ Binet.tribonacciCharacteristicPolynomial.roots)
    (hz_ne : z ≠ (Values.tribonacciConstant : Complex)) :
    (interior (RauzyFractal.rauzyFractal z)).Nonempty

Here K is exactly the closure of all finite no-111 Boolean digit sums at
exponents starting with zero. Both non-Perron roots are included; the final
statement assumes neither separation, positive area nor an open-set condition.

Proposed live content: construct ONE finite tuple of translates of the actual
compact K whose union covers ball(0,1). At each scale choose all relevant
normalized prefix centers simultaneously, by a fixed finite c/3-net of a
compact bounding disk. Each net ball contains at most one center. Fill unused
slots by zero, and take one convergent subsequence in the finite product.
A ball missing the limiting union persists as a uniformly sized hole in every
late tuple. Its similarity image contradicts density one at the chosen point.
Compactness alone supplies only a tuple limit; the persistent-hole argument
must supply coverage, and finite closed-set avoidance then supplies interior.

Separation, the word-count lower bound and positive-area disk packing are
consumed infrastructure, not independent admission endpoints. No reverse
prefix-cover inclusion or arbitrary admissible concatenation is asserted.

Classical context: A. Messaoudi, Propriétés arithmétiques et dynamiques du
fractal de Rauzy, JTNB 10(1), 135–162. Its exponent-three normalization and its
imported tiling conclusion are not Lean premises here. No research novelty is
claimed.
-/

namespace D5.S3.Geometry.Rauzy.Interior

open Set Metric Filter MeasureTheory
open scoped Topology ENNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- The approximation hypothesis below is discharged from density one and the
actual upper cylinder covers. It says that a fixed open hole cannot persist;
it does not posit any disk cover by translates of K. -/
private theorem finite_translate_cover_of_separated_approximants
    {K : Set ℂ} (hK : IsCompact K) {c S : ℝ}
    (hc : 0 < c) (hS : 0 ≤ S) (A : ℕ → Set ℂ)
    (hbound : ∀ n, A n ⊆ closedBall 0 S)
    (hsep : ∀ n, ∀ a ∈ A n, ∀ b ∈ A n, a ≠ b → c ≤ dist a b)
    (hfill : ∀ y ∈ ball (0 : ℂ) 1, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop, ∃ a ∈ A n, ∃ k ∈ K, a + k ∈ ball y ε) :
    ∃ (N : ℕ) (t : Fin N → ℂ),
      ball (0 : ℂ) 1 ⊆ ⋃ i, (fun k => t i + k) '' K := by
  classical
  obtain ⟨net, _, hnet, hcover⟩ :=
    (isCompact_closedBall (0 : ℂ) S).finite_cover_balls (by linarith : 0 < c / 3)
  let ι := ↥net
  letI : Fintype ι := hnet.fintype
  let occupied (n : ℕ) (i : ι) := ∃ a ∈ A n, dist a i.1 < c / 3
  let u (n : ℕ) (i : ι) : ℂ :=
    if h : occupied n i then h.choose else 0
  have hu (n : ℕ) (i : ι) (h : occupied n i) :
      u n i ∈ A n ∧ dist (u n i) i.1 < c / 3 := by
    simpa only [u, dif_pos h] using h.choose_spec
  have hubound : ∀ n i, u n i ∈ closedBall (0 : ℂ) S := by
    intro n i
    by_cases h : occupied n i
    · exact hbound n (hu n i h).1
    · simp [u, h, mem_closedBall, hS]
  have hrepresented : ∀ n, ∀ a ∈ A n, ∃ i, u n i = a := by
    intro n a ha
    obtain ⟨b, hb, hab⟩ := mem_iUnion₂.mp (hcover (hbound n ha))
    let i : ι := ⟨b, hb⟩
    have hocc : occupied n i := ⟨a, ha, hab⟩
    refine ⟨i, ?_⟩
    by_contra hne
    have hdist : dist (u n i) a < c := by
      calc
        dist (u n i) a ≤ dist (u n i) b + dist b a := dist_triangle _ _ _
        _ < c := by
          have hh := (hu n i hocc).2
          change dist (u n i) b < c / 3 at hh
          have hab' : dist a b < c / 3 := hab
          rw [dist_comm b a]
          linarith
    exact (not_lt_of_ge (hsep n (u n i) (hu n i hocc).1 a ha hne)) hdist
  have hprod : IsCompact (Set.pi (univ : Set ι) (fun _ => closedBall (0 : ℂ) S)) :=
    isCompact_univ_pi (fun _ => isCompact_closedBall (0 : ℂ) S)
  obtain ⟨t, _, φ, hφ, ht⟩ := hprod.tendsto_subseq
    (x := u) (fun n => by simpa only [Set.mem_pi, mem_univ, forall_true_left] using hubound n)
  let L : Set ℂ := ⋃ i : ι, (fun k => t i + k) '' K
  have hL : IsCompact L := isCompact_iUnion (fun i =>
    hK.image (continuous_const.add continuous_id))
  have hcoverL : ball (0 : ℂ) 1 ⊆ L := by
    intro y hy
    by_contra hyL
    obtain ⟨δ, hδ, hδL⟩ := Metric.mem_nhds_iff.mp
      (hL.isClosed.isOpen_compl.mem_nhds hyL)
    have hclose : ∀ᶠ n in atTop, ∀ i : ι, dist (u (φ n) i) (t i) < δ / 2 := by
      apply eventually_all.mpr
      intro i
      exact ((tendsto_pi_nhds.mp ht) i).eventually
        (ball_mem_nhds (t i) (by linarith))
    have hhit := hφ.tendsto_atTop.eventually (hfill y hy (δ / 2) (by linarith))
    obtain ⟨n, hclose, a, ha, k, hk, hnear⟩ := (hclose.and hhit).exists
    obtain ⟨i, hi⟩ := hrepresented (φ n) a ha
    have hlim : t i + k ∈ ball y δ := by
      rw [mem_ball] at hnear ⊢
      calc
        dist (t i + k) y ≤ dist (t i + k) (a + k) + dist (a + k) y :=
          dist_triangle _ _ _
        _ < δ := by
          have herr : dist (t i) a < δ / 2 := by simpa [hi, dist_comm] using hclose i
          rw [dist_add_right]
          linarith
    exact hδL hlim (mem_iUnion.mpr ⟨i, k, hk, rfl⟩)
  let e := Fintype.equivFin ι
  refine ⟨Fintype.card ι, fun i => t (e.symm i), ?_⟩
  intro y hy
  obtain ⟨i, k, hk, rfl⟩ := mem_iUnion.mp (hcoverL hy)
  exact mem_iUnion.mpr ⟨e i, k, hk, by simp⟩

private theorem real_volume_ball (x : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    volume.real (ball x r) = r ^ 2 * Real.pi := by
  simp [measureReal_def, Complex.volume_ball, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal hr, NNReal.coe_real_pi]

private theorem real_volume_closedBall (x : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    volume.real (closedBall x r) = r ^ 2 * Real.pi := by
  simp [measureReal_def, Complex.volume_closedBall, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal hr, NNReal.coe_real_pi]

/- A hole of relative radius δ costs exactly δ² of a planar density ratio.
This estimate uses only the measure of actual balls, not a general measure
change theorem for similarities. -/
private theorem density_hits_scaled_ball {K : Set ℂ} (x z : ℂ)
    (hz : 0 < ‖z‖)
    (hdensity : Tendsto (fun n : ℕ =>
      volume.real (K ∩ closedBall x (‖z‖ ^ n)) /
        volume.real (closedBall x (‖z‖ ^ n))) atTop (𝓝 1))
    (y : ℂ) {δ : ℝ} (hδ : 0 < δ) (hinside : ‖y‖ + δ ≤ 1) :
    ∀ᶠ n in atTop,
      (K ∩ ball (x + z ^ n * y) (δ * ‖z‖ ^ n)).Nonempty := by
  have hstrict : 1 - δ ^ 2 < (1 : ℝ) := by nlinarith [sq_pos_of_pos hδ]
  filter_upwards [hdensity.eventually (lt_mem_nhds hstrict)] with n hn
  by_contra hmiss
  have hr : 0 < ‖z‖ ^ n := pow_pos hz n
  have hBC : ball (x + z ^ n * y) (δ * ‖z‖ ^ n) ⊆ closedBall x (‖z‖ ^ n) := by
    intro w hw
    rw [mem_ball] at hw
    rw [mem_closedBall]
    have hc : dist (x + z ^ n * y) x = ‖z‖ ^ n * ‖y‖ := by
      simp [dist_eq_norm, norm_mul, norm_pow]
    have ht := dist_triangle w (x + z ^ n * y) x
    rw [hc] at ht
    nlinarith [mul_le_mul_of_nonneg_left hinside hr.le]
  have hdisj : Disjoint (K ∩ closedBall x (‖z‖ ^ n))
      (ball (x + z ^ n * y) (δ * ‖z‖ ^ n)) := by
    apply Set.disjoint_left.mpr
    intro w hw hball
    exact hmiss ⟨w, hw.1, hball⟩
  have hsum : volume.real (K ∩ closedBall x (‖z‖ ^ n)) +
      volume.real (ball (x + z ^ n * y) (δ * ‖z‖ ^ n)) ≤
        volume.real (closedBall x (‖z‖ ^ n)) := by
    rw [← measureReal_union hdisj measurableSet_ball
      (measure_ne_top_of_subset inter_subset_right measure_closedBall_lt_top.ne)
      measure_ball_ne_top]
    exact measureReal_mono (union_subset inter_subset_right hBC) measure_closedBall_lt_top.ne
  rw [real_volume_ball _ (mul_nonneg hδ.le hr.le), real_volume_closedBall _ hr.le] at hsum
  rw [real_volume_closedBall _ hr.le] at hn
  have hden : 0 < (‖z‖ ^ n) ^ 2 * Real.pi := mul_pos (sq_pos_of_pos hr) Real.pi_pos
  have hh := (lt_div_iff₀ hden).mp hn
  nlinarith [hsum]

private theorem finite_disk_cover_at_density_point {K : Set ℂ} (hK : IsCompact K)
    {R c : ℝ} (hR : 0 ≤ R) (hc : 0 < c)
    (hbound : K ⊆ closedBall 0 R) (z x : ℂ) (hz : 0 < ‖z‖)
    (P : ℕ → Set ℂ)
    (hsep : ∀ n, ∀ a ∈ P n, ∀ b ∈ P n, a ≠ b →
      c * ‖z‖ ^ n ≤ dist a b)
    (hcover : ∀ n, ∀ w ∈ K, ∃ a ∈ P n, ∃ k ∈ K, w = a + z ^ n * k)
    (hdensity : Tendsto (fun n : ℕ =>
      volume.real (K ∩ closedBall x (‖z‖ ^ n)) /
        volume.real (closedBall x (‖z‖ ^ n))) atTop (𝓝 1)) :
    ∃ (N : ℕ) (t : Fin N → ℂ),
      ball (0 : ℂ) 1 ⊆ ⋃ i, (fun k => t i + k) '' K := by
  let A (n : ℕ) : Set ℂ :=
    ((fun a => (a - x) / z ^ n) '' P n) ∩ closedBall 0 (R + 1)
  have hz0 : z ≠ 0 := norm_pos_iff.mp hz
  have hAbound : ∀ n, A n ⊆ closedBall 0 (R + 1) := fun _ => inter_subset_right
  have hAsep : ∀ n, ∀ a ∈ A n, ∀ b ∈ A n, a ≠ b → c ≤ dist a b := by
    rintro n a ⟨⟨p, hp, rfl⟩, _⟩ b ⟨⟨q, hq, rfl⟩, _⟩ hab
    have hpq : p ≠ q := by rintro rfl; exact hab rfl
    have heq : (p - x) / z ^ n - (q - x) / z ^ n = (p - q) / z ^ n := by ring
    rw [dist_eq_norm, heq, norm_div, norm_pow]
    apply (le_div_iff₀ (pow_pos hz n)).mpr
    simpa only [dist_eq_norm] using hsep n p hp q hq hpq
  have hlocal : ∀ n, ∀ v ∈ ball (0 : ℂ) 1, x + z ^ n * v ∈ K →
      ∃ a ∈ A n, ∃ k ∈ K, v = a + k := by
    intro n v hv hvK
    obtain ⟨p, hp, k, hk, he⟩ := hcover n _ hvK
    let a := (p - x) / z ^ n
    have hva : v = a + k := by
      dsimp [a]
      apply (mul_right_cancel₀ (pow_ne_zero n hz0))
      field_simp
      linear_combination he
    refine ⟨a, ⟨⟨p, hp, rfl⟩, ?_⟩, k, hk, hva⟩
    have hvnorm : ‖v‖ < 1 := by simpa using hv
    have hknorm : ‖k‖ ≤ R := by simpa using hbound hk
    rw [mem_closedBall, dist_zero_right]
    have ha : a = v - k := by rw [hva]; ring
    rw [ha]
    exact (norm_sub_le v k).trans (by linarith)
  apply finite_translate_cover_of_separated_approximants hK hc (by linarith) A hAbound hAsep
  intro y hy ε hε
  have hynorm : ‖y‖ < 1 := by simpa using hy
  let δ := min (ε / 2) ((1 - ‖y‖) / 2)
  have hδ : 0 < δ := lt_min (by linarith) (by linarith)
  have hδε : δ < ε := (min_le_left _ _).trans_lt (by linarith)
  have hδin : ‖y‖ + δ ≤ 1 := by
    have := min_le_right (ε / 2) ((1 - ‖y‖) / 2)
    dsimp [δ]
    linarith
  filter_upwards [density_hits_scaled_ball x z hz hdensity y hδ hδin] with n hn
  obtain ⟨w, hwK, hwball⟩ := hn
  let v := (w - x) / z ^ n
  have hvy : dist v y < δ := by
    have he : v - y = (w - (x + z ^ n * y)) / z ^ n := by dsimp [v]; field_simp; ring
    rw [dist_eq_norm, he, norm_div, norm_pow]
    apply (div_lt_iff₀ (pow_pos hz n)).mpr
    simpa only [mem_ball, dist_eq_norm] using hwball
  have hv : v ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball, dist_zero_right]
    have ht : ‖v‖ ≤ dist v y + ‖y‖ := by
      simpa only [dist_zero_right] using dist_triangle v y 0
    linarith
  have he : x + z ^ n * v = w := by dsimp [v]; field_simp; ring
  obtain ⟨a, ha, k, hk, hvak⟩ := hlocal n v hv (he.symm ▸ hwK)
  exact ⟨a, ha, k, hk, by rw [← hvak]; exact hvy.trans hδε⟩

private theorem interior_nonempty_of_finite_translate_cover {K : Set ℂ}
    (hK : IsCompact K) {N : ℕ} (t : Fin N → ℂ)
    (hcover : ball (0 : ℂ) 1 ⊆ ⋃ i, (fun k => t i + k) '' K) :
    (interior K).Nonempty := by
  by_contra h
  have hndK : IsNowhereDense K :=
    hK.isClosed.isNowhereDense_iff.mpr (Set.not_nonempty_iff_eq_empty.mp h)
  have hnd : IsNowhereDense (⋃ i, (fun k => t i + k) '' K) := by
    apply IsNowhereDense.iUnion
    intro i
    exact (Homeomorph.addLeft (t i)).isInducing.isNowhereDense_image hndK
  have hndball := hnd.mono hcover
  have hzero : (0 : ℂ) ∈ interior (ball (0 : ℂ) 1) := by
    rw [isOpen_ball.interior_eq]
    simp
  have hz := interior_mono (subset_closure : ball (0 : ℂ) 1 ⊆ closure (ball 0 1)) hzero
  change interior (closure (ball (0 : ℂ) 1)) = ∅ at hndball
  simpa only [hndball, mem_empty_iff_false] using hz

/-- Geometric data for an actual compact planar cylinder construction.
The finite disk cover and interior are conclusions, not fields of the data. -/
structure SeparatedCylinderSystem where
  carrier : Set ℂ
  compact : IsCompact carrier
  positive_volume : 0 < volume carrier
  radius : ℝ
  separation : ℝ
  radius_nonneg : 0 ≤ radius
  separation_pos : 0 < separation
  bounded : carrier ⊆ closedBall 0 radius
  contraction : ℂ
  norm_pos : 0 < ‖contraction‖
  norm_lt_one : ‖contraction‖ < 1
  centers : ℕ → Set ℂ
  separated : ∀ n, ∀ a ∈ centers n, ∀ b ∈ centers n, a ≠ b →
    separation * ‖contraction‖ ^ n ≤ dist a b
  upper_cover : ∀ n, ∀ w ∈ carrier, ∃ a ∈ centers n,
    ∃ k ∈ carrier, w = a + contraction ^ n * k

/-- Compact planar sets of positive area with uniformly separated shrinking
upper cylinder covers have nonempty interior. The proof constructs a finite
family of actual translates covering a disk at one density point. -/
theorem interior_nonempty_of_separated_cylinders (S : SeparatedCylinderSystem) :
    (interior S.carrier).Nonempty := by
  rcases S with ⟨K, hK, hpos, R, c, hR, hc, hbound, z, hz0, hz1, P, hsep, hcover⟩
  obtain ⟨x, _, hx⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos.ne'
    (Besicovitch.ae_tendsto_measure_inter_div volume K)
  have hscale : Tendsto (fun n : ℕ => ‖z‖ ^ n) atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨tendsto_pow_atTop_nhds_zero_of_lt_one hz0.le hz1,
      Filter.Eventually.of_forall (fun n => pow_pos hz0 n)⟩
  have hreal : Tendsto (fun n : ℕ =>
      volume.real (K ∩ closedBall x (‖z‖ ^ n)) /
        volume.real (closedBall x (‖z‖ ^ n))) atTop (𝓝 1) := by
    have ht := (ENNReal.tendsto_toReal (by simp : (1 : ℝ≥0∞) ≠ ∞)).comp (hx.comp hscale)
    simpa only [Function.comp_def, ENNReal.toReal_div, ENNReal.toReal_one,
      measureReal_def] using ht
  obtain ⟨N, t, ht⟩ := finite_disk_cover_at_density_point hK hR hc hbound z x hz0 P hsep hcover hreal
  exact interior_nonempty_of_finite_translate_cover hK t ht

end D5.S3.Geometry.Rauzy.Interior
