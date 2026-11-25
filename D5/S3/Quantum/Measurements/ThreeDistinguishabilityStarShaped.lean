/- GID: D5/S3/Quantum/Measurements/ThreeDistinguishabilityStarShaped
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurements/ThreeDistinguishabilityStarShaped
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The four-outcome mixed three-distinguishability region is star-shaped about uniform. -/

import D5.S3.Quantum.Measurements.ThreeDistinguishabilityMixedPurity
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Data.Finset.Max

/-!
Korzekwa, Czachórski, Puchała and Życzkowski, arXiv:1812.09083v3,
§III.C, Conjecture 9, Eq. (31), for four outcomes and three distinguishable states.
-/

set_option autoImplicit false

open scoped BigOperators

noncomputable section

namespace D5.S3.Quantum.Measurements.ThreeDistinguishabilityStarShaped

open ThreeDistinguishabilityProductRefutation (InRegion)
open ThreeDistinguishabilityMixedPurity (inRegion_iff_cubic)
open ThreeDistinguishabilityCubic (q d phaseCubic cubicAfterConstant)

section Polynomial

private def shape (x : Fin 4 → ℝ) : ℝ :=
  (x 0 + x 1 - x 2 - x 3) ^ 2 - 4 * x 0 * x 1 - 4 * x 2 * x 3

private def quartic (x : Fin 4 → ℝ) : ℝ :=
  shape x ^ 2 - 64 * ∏ i, x i

private theorem quartic_scale (x : Fin 4 → ℝ) (s : ℝ) :
    quartic (fun i => s * x i) = s ^ 4 * quartic x := by
  simp only [quartic, shape, Fin.prod_univ_four]
  ring

private theorem quartic_of_zero_entry (x : Fin 4 → ℝ) (j : Fin 4) (hj : x j = 0) :
    quartic x = shape x ^ 2 := by
  have hs := Finset.prod_erase_mul Finset.univ x (Finset.mem_univ j)
  rw [hj, mul_zero] at hs
  rw [quartic, ← hs, mul_zero, sub_zero]

private theorem quartic_squares_zero (a : Fin 4 → ℝ) (ha : ∑ i, a i = 0) :
    quartic (fun i => a i ^ 2) = 0 := by
  rw [Fin.sum_univ_four] at ha
  have ha3 : a 3 = -(a 0 + a 1 + a 2) := by linarith only [ha]
  simp only [quartic, shape, Fin.prod_univ_four, ha3]
  ring

set_option maxHeartbeats 1500000 in
-- Full expansion of the quartic and cubic coefficients.
private theorem quartic_cubic_expansion (u v : Fin 4 → ℝ) (t : ℝ) :
    quartic (fun i => u i * t - v i) = t * cubicAfterConstant u v t + quartic v := by
  simp only [quartic, shape, Fin.prod_univ_four, cubicAfterConstant]
  ring

private theorem quartic_phaseCubic (p : Fin 4 → ℝ) (hp : ∑ i, p i = 1) (t : ℝ) :
    quartic (fun i => q p i ^ 2 * t - d p i ^ 2) = t * phaseCubic p t := by
  have hd : ∑ i, d p i = 0 := by
    norm_num [d, Finset.sum_sub_distrib, ← Finset.mul_sum, hp]
  rw [phaseCubic, quartic_cubic_expansion, quartic_squares_zero _ hd, add_zero]

private def e2 (a : Fin 4 → ℝ) : ℝ :=
  a 0 * a 1 + a 0 * a 2 + a 0 * a 3 + a 1 * a 2 + a 1 * a 3 + a 2 * a 3

private def e3 (a : Fin 4 → ℝ) : ℝ :=
  a 0 * a 1 * a 2 + a 0 * a 1 * a 3 + a 0 * a 2 * a 3 + a 1 * a 2 * a 3

private def e4 (a : Fin 4 → ℝ) : ℝ := ∏ i, a i

private def A (a : Fin 4 → ℝ) (w : ℝ) : ℝ :=
  8 * e3 a + 4 * w * (e2 a ^ 2 - 4 * e4 a) -
    4 * w ^ 2 * e2 a * e3 a + w ^ 3 * e3 a ^ 2

private def B (a : Fin 4 → ℝ) (w : ℝ) : ℝ :=
  4 * (e2 a ^ 2 - 4 * e4 a) - 12 * w * e2 a * e3 a +
    9 * w ^ 2 * e3 a ^ 2 - 8 * w ^ 3 * e3 a * e4 a

private def coefficient (a : Fin 4 → ℝ) (w : ℝ) (i : Fin 4) : ℝ :=
  2 * a i + w * a i ^ 2

private def radicand (a : Fin 4 → ℝ) (r w : ℝ) (i : Fin 4) : ℝ :=
  1 - r * coefficient a w i

set_option maxHeartbeats 2000000 in
-- Expansion after eliminating the fourth coordinate using the zero-sum constraint.
private theorem quartic_radicand (a : Fin 4 → ℝ) (ha : ∑ i, a i = 0) (r w : ℝ) :
    quartic (radicand a r w) = 64 * r ^ 3 * (A a w + r * B a w) := by
  rw [Fin.sum_univ_four] at ha
  have ha3 : a 3 = -(a 0 + a 1 + a 2) := by linarith only [ha]
  simp only [quartic, shape, radicand, coefficient, A, B, e2, e3, e4,
    Fin.prod_univ_four, ha3]
  ring

end Polynomial

section Contraction

/-- The first zero along the fixed-`w` line, as determined by the maximal coefficient. -/
private theorem first_radius_zero (a : Fin 4 → ℝ) (ha : ∑ i, a i = 0)
    (hne : ∃ i, a i ≠ 0) {r w : ℝ} (hw : 0 < w)
    (hy : ∀ i, 0 ≤ radicand a r w i) :
    ∃ (R : ℝ) (j : Fin 4), r ≤ R ∧
      (∀ i, 0 ≤ radicand a R w i) ∧ radicand a R w j = 0 := by
  obtain ⟨k, hk⟩ := hne
  have hs : 0 < ∑ i, a i ^ 2 :=
    (sq_pos_of_ne_zero hk).trans_le
      (Finset.single_le_sum (fun i _ => sq_nonneg (a i)) (Finset.mem_univ k))
  have hc : 0 < ∑ i, coefficient a w i := by
    simp only [coefficient, Finset.sum_add_distrib, ← Finset.mul_sum, ha, mul_zero, zero_add]
    exact mul_pos hw hs
  obtain ⟨j, _, hj⟩ :=
    Finset.exists_max_image Finset.univ (coefficient a w) Finset.univ_nonempty
  have hmax (i : Fin 4) : coefficient a w i ≤ coefficient a w j :=
    hj i (Finset.mem_univ i)
  have hjpos : 0 < coefficient a w j := by
    by_contra! h
    exact hc.not_ge (Finset.sum_nonpos fun i _ => (hmax i).trans h)
  let R := 1 / coefficient a w j
  have hR : 0 < R := one_div_pos.mpr hjpos
  have hRj : R * coefficient a w j = 1 := by
    dsimp [R]
    field_simp
  refine ⟨R, j, (le_div_iff₀ hjpos).2 (sub_nonneg.mp (hy j)), ?_, ?_⟩
  · intro i
    exact sub_nonneg.mpr ((mul_le_mul_of_nonneg_left (hmax i) hR.le).trans_eq hRj)
  · simp [radicand, hRj]

/-- At a vanishing radicand, the two product derivatives give the exact slope. -/
private theorem B_at_boundary (a : Fin 4 → ℝ) (ha : ∑ i, a i = 0)
    {R w : ℝ} (hR : 0 < R) {j : Fin 4} (hj : radicand a R w j = 0)
    (hroot : A a w + R * B a w = 0) :
    B a w = (∏ i ∈ Finset.univ.erase j, radicand a R w i) / R ^ 4 := by
  let y (r : ℝ) := radicand a r w
  let rest (r : ℝ) := ∏ i ∈ Finset.univ.erase j, y r i
  have hF : quartic (y R) = 0 := by
    rw [quartic_radicand a ha, hroot, mul_zero]
  have hG : shape (y R) = 0 := by
    rw [quartic_of_zero_entry _ j hj] at hF
    exact sq_eq_zero_iff.mp hF
  have hy (i : Fin 4) :
      HasDerivAt (fun r : ℝ => y r i) (-coefficient a w i) R := by
    simpa [y, radicand] using
      (((hasDerivAt_id R).mul_const (coefficient a w i)).const_sub (1 : ℝ))
  have hrest : DifferentiableAt ℝ rest R :=
    DifferentiableAt.fun_finsetProd (fun i _ => (hy i).differentiableAt)
  have hprod_eq (s : ℝ) : rest s * y s j = ∏ i, y s i :=
    Finset.prod_erase_mul Finset.univ (y s) (Finset.mem_univ j)
  have hprod : HasDerivAt (fun s : ℝ => ∏ i, y s i)
      (rest R * -coefficient a w j) R := by
    have h := hrest.hasDerivAt.mul (hy j)
    simp only [show y R j = 0 from hj, mul_zero, zero_add] at h
    exact (funext hprod_eq) ▸ h
  have hshape : DifferentiableAt ℝ (fun s : ℝ => shape (y s)) R := by
    unfold shape y radicand
    fun_prop
  have hsq : HasDerivAt (fun s : ℝ => shape (y s) ^ 2) 0 R := by
    have h := hshape.hasDerivAt.pow 2
    change HasDerivAt (fun s : ℝ => shape (y s) ^ 2) _ R at h
    simpa [hG] using h
  have hfactor : HasDerivAt (fun s : ℝ => A a w + s * B a w) (B a w) R := by
    simpa using ((hasDerivAt_id R).mul_const (B a w)).const_add (A a w)
  have hnorm : HasDerivAt (fun s : ℝ => 64 * s ^ 3 * (A a w + s * B a w))
      (64 * R ^ 3 * B a w) R := by
    have h := (((hasDerivAt_id R).pow 3).const_mul (64 : ℝ)).mul hfactor
    change HasDerivAt (fun s : ℝ => 64 * s ^ 3 * (A a w + s * B a w)) _ R at h
    simpa [hroot] using h
  have hexpand : (fun s => quartic (y s)) =
      fun s => 64 * s ^ 3 * (A a w + s * B a w) :=
    funext (quartic_radicand a ha · w)
  have hquartic : HasDerivAt (fun s => quartic (y s))
      (0 - 64 * (rest R * -coefficient a w j)) R :=
    hsq.sub (hprod.const_mul (64 : ℝ))
  rw [hexpand] at hquartic
  have hder := hnorm.unique hquartic
  have hcoeff : coefficient a w j = 1 / R := by
    apply (eq_div_iff hR.ne').2
    change 1 - R * coefficient a w j = 0 at hj
    linarith only [hj]
  change B a w = rest R / R ^ 4
  apply (eq_div_iff (pow_ne_zero 4 hR.ne')).2
  rw [hcoeff] at hder
  field_simp at hder
  linarith only [hder]

private theorem B_nonneg_of_root (a : Fin 4 → ℝ) (ha : ∑ i, a i = 0)
    (hne : ∃ i, a i ≠ 0) {r w : ℝ} (hr : 0 < r) (hw : 0 < w)
    (hy : ∀ i, 0 ≤ radicand a r w i) (hroot : A a w + r * B a w = 0) :
    0 ≤ B a w := by
  obtain ⟨R, j, hrR, hR, hj⟩ := first_radius_zero a ha hne hw hy
  rcases hrR.eq_or_lt with heq | hlt
  · subst R
    rw [B_at_boundary a ha hr hj hroot]
    exact div_nonneg (Finset.prod_nonneg fun i _ => hR i) (by positivity)
  · have hF : 0 ≤ quartic (radicand a R w) := by
      rw [quartic_of_zero_entry _ j hj]
      exact sq_nonneg _
    have hRpos := hr.trans hlt
    rw [quartic_radicand a ha, ← sub_nonneg] at hF
    have hsign : 0 ≤ A a w + R * B a w := by
      have hp : 0 < 64 * R ^ 3 := by positivity
      exact nonneg_of_mul_nonneg_right (sub_nonneg.mp hF) hp
    have hdiff : 0 ≤ (R - r) * B a w := by
      calc
        0 ≤ (A a w + R * B a w) - (A a w + r * B a w) := by simpa [hroot] using hsign
        _ = (R - r) * B a w := by ring
    exact nonneg_of_mul_nonneg_right hdiff (sub_pos.mpr hlt)

/-- For fixed positive radius, increasing the parameter reaches a zero radicand
at the minimum of the finite list of ratios. -/
private theorem first_parameter_zero (a : Fin 4 → ℝ) (hne : ∃ i, a i ≠ 0)
    {r w₀ : ℝ} (hr : 0 < r) (hy : ∀ i, 0 < radicand a r w₀ i) :
    ∃ (W : ℝ) (j : Fin 4), w₀ < W ∧
      (∀ w ∈ Set.Icc w₀ W, ∀ i, 0 ≤ radicand a r w i) ∧ radicand a r W j = 0 := by
  let support := Finset.univ.filter (fun i : Fin 4 => a i ≠ 0)
  let ratio (i : Fin 4) := (1 - 2 * r * a i) / (r * a i ^ 2)
  have hsupport : support.Nonempty := by
    obtain ⟨i, hi⟩ := hne
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  obtain ⟨j, hj, hmin⟩ := Finset.exists_min_image support ratio hsupport
  have hden (i : Fin 4) (hi : a i ≠ 0) : 0 < r * a i ^ 2 :=
    mul_pos hr (sq_pos_of_ne_zero hi)
  have hy_eq (w : ℝ) (i : Fin 4) :
      radicand a r w i = (1 - 2 * r * a i) - w * (r * a i ^ 2) := by
    unfold radicand coefficient
    ring
  have hjden := hden j (Finset.mem_filter.mp hj).2
  refine ⟨ratio j, j, (lt_div_iff₀ hjden).2 (sub_pos.mp ((hy_eq w₀ j) ▸ hy j)), ?_, ?_⟩
  · intro w hw i
    by_cases hi : a i = 0
    · simp [radicand, coefficient, hi]
    · rw [hy_eq]
      apply sub_nonneg.mpr
      exact (le_div_iff₀ (hden i hi)).1
        (hw.2.trans (hmin i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)))
  · rw [hy_eq, sub_eq_zero]
    exact ((div_mul_cancel₀ _ hjden.ne') : ratio j * (r * a j ^ 2) = _).symm

private theorem inward_root (a : Fin 4 → ℝ) (ha : ∑ i, a i = 0)
    (hne : ∃ i, a i ≠ 0) {r r₀ w₀ : ℝ} (hr : 0 < r) (hrr : r < r₀) (hw₀ : 3 * r₀ ≤ w₀)
    (hy₀ : ∀ i, 0 ≤ radicand a r₀ w₀ i) (hroot : A a w₀ + r₀ * B a w₀ = 0) :
    ∃ w, 3 * r ≤ w ∧ (∀ i, 0 ≤ radicand a r w i) ∧ A a w + r * B a w = 0 := by
  have hr₀ := hr.trans hrr
  have hB := B_nonneg_of_root a ha hne hr₀ (by linarith only [hw₀, hr₀]) hy₀ hroot
  have hy (i : Fin 4) : 0 < radicand a r w₀ i := by
    have hratio : r / r₀ < 1 := (div_lt_one₀ hr₀).2 hrr
    have hfactor : 0 ≤ r / r₀ * radicand a r₀ w₀ i :=
      mul_nonneg (div_nonneg hr.le hr₀.le) (hy₀ i)
    calc
      0 < (1 - r / r₀) + r / r₀ * radicand a r₀ w₀ i := by linarith only [hratio, hfactor]
      _ = radicand a r w₀ i := by
        unfold radicand
        field_simp
        ring
  obtain ⟨W, j, hW, hYW, hj⟩ := first_parameter_zero a hne hr hy
  let P (w : ℝ) := A a w + r * B a w
  have hleft : P w₀ ≤ 0 := by
    have hn := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hrr.le) hB
    change A a w₀ + r * B a w₀ ≤ 0
    calc
      A a w₀ + r * B a w₀ = (A a w₀ + r₀ * B a w₀) + (r - r₀) * B a w₀ := by ring
      _ ≤ 0 := by simpa [hroot] using hn
  have hright : 0 ≤ P W := by
    have hF : 0 ≤ quartic (radicand a r W) := by
      rw [quartic_of_zero_entry _ j hj]
      exact sq_nonneg _
    rw [quartic_radicand a ha] at hF
    exact nonneg_of_mul_nonneg_right hF (by positivity)
  have hcont : Continuous P := by
    unfold P A B
    fun_prop
  obtain ⟨w, hw, hzero⟩ := intermediate_value_Icc hW.le hcont.continuousOn
    (show (0 : ℝ) ∈ Set.Icc (P w₀) (P W) from ⟨hleft, hright⟩)
  exact ⟨w, (show 3 * r ≤ 3 * r₀ by linarith only [hrr]).trans (hw₀.trans hw.1),
    hYW w hw, hzero⟩

end Contraction

section MixedRegion

private def rayLaw (a : Fin 4 → ℝ) (r : ℝ) (i : Fin 4) : ℝ := (1 + r * a i) / 4

private theorem rayLaw_sum (a : Fin 4 → ℝ) (ha : ∑ i, a i = 0) (r : ℝ) :
    ∑ i, rayLaw a r i = 1 := by
  unfold rayLaw
  rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum, ha, mul_zero, add_zero]
  norm_num

private theorem scale_radicand (a : Fin 4 → ℝ) {r w t : ℝ}
    (ht : t * (w + r) = 4 * r) (i : Fin 4) :
    q (rayLaw a r) i ^ 2 * t - d (rayLaw a r) i ^ 2 = (t / 4) * radicand a r w i := by
  unfold q d rayLaw radicand coefficient
  linear_combination (r * a i ^ 2 / 4) * ht

private theorem ray_witness_iff (a : Fin 4 → ℝ) (ha : ∑ i, a i = 0) {r : ℝ} (hr : 0 < r) :
    (∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
      (∀ i, q (rayLaw a r) i ^ 2 * t ≥ d (rayLaw a r) i ^ 2) ∧ phaseCubic (rayLaw a r) t = 0) ↔
    ∃ w : ℝ, 3 * r ≤ w ∧ (∀ i, 0 ≤ radicand a r w i) ∧ A a w + r * B a w = 0 := by
  have hscale {t w : ℝ} (heq : t * (w + r) = 4 * r) :
      t * phaseCubic (rayLaw a r) t = (t / 4) ^ 4 * (64 * r ^ 3 * (A a w + r * B a w)) := by
    rw [← quartic_phaseCubic _ (rayLaw_sum a ha r),
      show (fun i => q (rayLaw a r) i ^ 2 * t - d (rayLaw a r) i ^ 2) =
        (fun i => (t / 4) * radicand a r w i) from funext (scale_radicand a heq),
      quartic_scale, quartic_radicand a ha]
  constructor
  · rintro ⟨t, ht, ht₁, hy, hroot⟩
    let w := 4 * r / t - r
    have heq : t * (w + r) = 4 * r := by
      dsimp [w]
      field_simp
      ring
    have hw : 3 * r ≤ w := by
      have hdiv : 4 * r ≤ 4 * r / t := (le_div_iff₀ ht).2 (by
        simpa using mul_le_mul_of_nonneg_left ht₁ (show 0 ≤ 4 * r by positivity))
      dsimp [w]
      linarith only [hdiv]
    refine ⟨w, hw, ?_, ?_⟩
    · intro i
      have h := sub_nonneg.mpr (hy i)
      rw [scale_radicand a heq] at h
      exact nonneg_of_mul_nonneg_right h (by positivity)
    · have h := hscale heq
      rw [hroot, mul_zero] at h
      exact (mul_eq_zero.mp ((mul_eq_zero.mp h.symm).resolve_left
        (by positivity : (t / 4) ^ 4 ≠ 0))).resolve_left (by positivity)
  · rintro ⟨w, hw, hy, hroot⟩
    have hden : 0 < w + r := by linarith only [hw, hr]
    let t := 4 * r / (w + r)
    have ht : 0 < t := by dsimp [t]; positivity
    have ht₁ : t ≤ 1 := (div_le_iff₀ hden).2 (by linarith only [hw])
    have heq : t * (w + r) = 4 * r := div_mul_cancel₀ _ hden.ne'
    refine ⟨t, ht, ht₁, ?_, ?_⟩
    · intro i
      apply sub_nonneg.mp
      rw [scale_radicand a heq]
      exact mul_nonneg (by positivity) (hy i)
    · have h := hscale heq
      rw [hroot, mul_zero, mul_zero] at h
      exact (mul_eq_zero.mp h).resolve_left ht.ne'

/-- The real uniform law belongs to the full mixed distinguishability region. -/
theorem uniform_inRegion : InRegion (fun _ : Fin 4 => (1 / 4 : ℝ)) := by
  apply (inRegion_iff_cubic _ (fun _ => by norm_num) (by norm_num)).2
  refine ⟨fun _ => by norm_num, 1, by norm_num, le_rfl, fun _ => ?_, ?_⟩
  · norm_num [q, d]
  · norm_num [phaseCubic, cubicAfterConstant, q, d]

/-- The full mixed distinguishability region for four outcomes and three states
is star-shaped about the real uniform law. -/
theorem inRegion_uniform_interpolation (p : Fin 4 → ℝ) (hp : InRegion p)
    (s : ℝ) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1) :
    InRegion (fun i => (1 - s) * (1 / 4 : ℝ) + s * p i) := by
  rcases hs₀.eq_or_lt with hzero | hpos
  · subst s
    simpa using uniform_inRegion
  rcases hs₁.eq_or_lt with hone | hlt
  · subst s
    simpa using hp
  let a := d p
  have ha : ∑ i, a i = 0 := by
    norm_num [a, d, Finset.sum_sub_distrib, ← Finset.mul_sum, hp.1.2]
  have hp_ray : rayLaw a 1 = p := by
    funext i
    simp only [rayLaw, a, d]
    ring
  have hinterp : (fun i => (1 - s) * (1 / 4 : ℝ) + s * p i) = rayLaw a s := by
    funext i
    simp only [rayLaw, a, d]
    ring
  rw [hinterp]
  by_cases hne : ∃ i, a i ≠ 0
  · obtain ⟨hcap, hwitness⟩ := (inRegion_iff_cubic _ hp.1.1 hp.1.2).1 hp
    rw [← hp_ray] at hwitness
    obtain ⟨w₀, hw₀, hy₀, hroot⟩ := (ray_witness_iff a ha zero_lt_one).1 hwitness
    have hw := inward_root a ha hne hpos hlt hw₀ hy₀ hroot
    have hnn (i : Fin 4) : 0 ≤ rayLaw a s i := by
      rw [← hinterp]
      exact add_nonneg (mul_nonneg (sub_nonneg.mpr hs₁) (by norm_num))
        (mul_nonneg hs₀ (hp.1.1 i))
    have hcap' (i : Fin 4) : rayLaw a s i ≤ 1 / 3 := by
      rw [← hinterp]
      calc
        _ ≤ (1 - s) * (1 / 3) + s * (1 / 3) :=
          add_le_add (mul_le_mul_of_nonneg_left (by norm_num) (sub_nonneg.mpr hs₁))
            (mul_le_mul_of_nonneg_left (hcap i) hs₀)
        _ = _ := by ring
    exact (inRegion_iff_cubic _ hnn (rayLaw_sum a ha s)).2
      ⟨hcap', (ray_witness_iff a ha hpos).2 hw⟩
  · push Not at hne
    have hconst : rayLaw a s = fun _ => (1 / 4 : ℝ) := by
      funext i
      simp [rayLaw, hne i]
    exact hconst ▸ uniform_inRegion

end MixedRegion

end D5.S3.Quantum.Measurements.ThreeDistinguishabilityStarShaped
