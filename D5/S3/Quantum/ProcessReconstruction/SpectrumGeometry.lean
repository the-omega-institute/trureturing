/- GID: D5/S3/Quantum/ProcessReconstruction/SpectrumGeometry
   generality: G
   mirror-B: D5/B/S3/Quantum/ProcessReconstruction/SpectrumGeometry
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unit-circle supporting lines and angular bounds for finite chains of unit vectors. -/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality
import Mathlib.Tactic

/-! Unit-circle supporting lines and angular bounds for finite chains of unit vectors. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace UnitaryReconstruction

private theorem circle_lens {a b x y : ℝ}
    (ha : 1 / 2 < a) (hb : 0 ≤ b) (hab : a ^ 2 + b ^ 2 = 1) (hxy : x ^ 2 + y ^ 2 = 1)
    (hp : a ^ 2 - b ^ 2 ≤ a * x + b * y)
    (hq : a ^ 2 - b ^ 2 ≤ a * x - b * y) : a ≤ x := by
  have hap : 0 < a := by linarith
  have hmin : a ^ 2 - b ^ 2 ≤ a * x - b * |y| := by
    rcases le_total 0 y with h | h
    · rwa [abs_of_nonneg h]
    · rw [abs_of_nonpos h]
      linarith
  by_contra! hx
  by_cases hxa : -a < x
  · have hxs : x ^ 2 < a ^ 2 := by
      have := mul_pos (sub_pos.mpr hx) (show 0 < a + x by linarith)
      nlinarith
    have hyb : b ≤ |y| := by
      apply (sq_le_sq₀ hb (abs_nonneg y)).mp
      rw [sq_abs]
      linarith
    have hby := mul_le_mul_of_nonneg_left hyb hb
    have hax := mul_lt_mul_of_pos_left hx hap
    nlinarith
  · push Not at hxa
    have hys : |y| ≤ b := by
      apply (sq_le_sq₀ (abs_nonneg y) hb).mp
      rw [sq_abs]
      have := mul_nonneg (show 0 ≤ -x - a by linarith) (show 0 ≤ -x + a by linarith)
      nlinarith
    have hx1 : 0 ≤ 1 + x := by
      by_contra! hn
      have := mul_pos (show 0 < -x - 1 by linarith) (show 0 < -x + 1 by linarith)
      nlinarith [sq_nonneg y]
    have h1 := mul_le_mul_of_nonneg_right hys (abs_nonneg y)
    have h2 := mul_nonneg hx1 (show 0 ≤ 1 - x - a by linarith)
    rw [← sq] at h1
    rw [sq_abs] at h1
    have hlow : a * (1 + x) ≤ b * |y| := by nlinarith
    have hroot := mul_pos (show 0 < 2 * a - 1 by linarith) (show 0 < a + 1 by linarith)
    nlinarith

private theorem unit_norm_coordinates {z : ℂ} (hz : ‖z‖ = 1) :
    z.re ^ 2 + z.im ^ 2 = 1 := by
  have h := Complex.sq_norm z
  rw [hz, Complex.normSq_apply] at h
  nlinarith

set_option maxHeartbeats 800000 in
-- The real-coordinate estimates for the rotated unit-circle lens need a larger budget.
/-- The midpoint of a diameter chord of length below `sqrt 3` determines
a half-plane containing the whole set of unit complex numbers. -/
theorem circle_diameter_halfPlane {p q : ℂ} (hp : ‖p‖ = 1) (hq : ‖q‖ = 1)
    (hd : ‖p - q‖ < Real.sqrt 3) :
    ∃ c : ℂ, ‖c‖ = 1 ∧
      ∃ a : ℝ, 0 < a ∧ 4 * (1 - a ^ 2) = ‖p - q‖ ^ 2 ∧
        ∀ z : ℂ, ‖z‖ = 1 → ‖z - p‖ ≤ ‖p - q‖ → ‖z - q‖ ≤ ‖p - q‖ →
          a ≤ (c * z).re := by
  let m : ℂ := (p + q) / 2
  let a := ‖m‖
  have hpn := unit_norm_coordinates hp
  have hqn := unit_norm_coordinates hq
  have hm (v : ℂ) : ‖v‖ ^ 2 = v.re ^ 2 + v.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have ha : 4 * (1 - a ^ 2) = ‖p - q‖ ^ 2 := by
    unfold a m
    rw [hm, hm]
    simp only [div_eq_mul_inv, show (2 : ℂ)⁻¹ = ((1 / 2 : ℝ) : ℂ) by norm_num,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im]
    ring_nf
    nlinarith
  have hap : 1 / 2 < a := by
    have hd2 := (sq_lt_sq₀ (norm_nonneg _) (Real.sqrt_nonneg 3)).mpr hd
    rw [Real.sq_sqrt (by norm_num)] at hd2
    by_contra! h
    nlinarith [mul_nonneg (sub_nonneg.mpr h) (show 0 ≤ a + 1 / 2 by positivity)]
  let c := star m * ((a⁻¹ : ℝ) : ℂ)
  have hc : ‖c‖ = 1 := by
    simp only [c, norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr (show 0 < a by linarith))]
    exact mul_inv_cancel₀ (show a ≠ 0 by linarith)
  have hcm : c * m = (a : ℂ) := by
    calc
      c * m = (star m * m) * ((a⁻¹ : ℝ) : ℂ) := by simp only [c]; ring
      _ = (a : ℂ) := by
        rw [mul_comm (star m), show m * star m = (‖m‖ : ℂ) ^ 2 from Complex.mul_conj' m]
        change (a : ℂ) ^ 2 * ↑a⁻¹ = ↑a
        have h : a ^ 2 * a⁻¹ = a := by
          rw [pow_two, mul_assoc, mul_inv_cancel₀ (show a ≠ 0 by linarith), mul_one]
        exact_mod_cast h
  refine ⟨c, hc, a, by linarith, ha, fun z hz hzp hzq => ?_⟩
  have hP : ‖c * p‖ = 1 := by simp [hc, hp]
  have hQ : ‖c * q‖ = 1 := by simp [hc, hq]
  have hZ : ‖c * z‖ = 1 := by simp [hc, hz]
  have hsum : c * p + c * q = (2 * a : ℝ) := by
    have hsum' : p + q = 2 * m := by unfold m; ring
    rw [← mul_add, hsum', mul_left_comm, hcm]
    push_cast
    rfl
  have hre := congrArg Complex.re hsum
  have him := congrArg Complex.im hsum
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im] at hre him
  have hnP := unit_norm_coordinates hP
  have hnQ := unit_norm_coordinates hQ
  have hnZ := unit_norm_coordinates hZ
  have heq : (c * p).re = (c * q).re := by
    have h1 : (c * p).im = -(c * q).im := by linarith
    rw [h1, neg_sq] at hnP
    have hs : (c * p).re ^ 2 = (c * q).re ^ 2 := by linarith
    have hf : ((c * p).re - (c * q).re) * (2 * a) = 0 := by rw [← hre]; nlinarith
    rcases mul_eq_zero.mp hf with hf | hf
    · linarith
    · linarith
  have hPa : (c * p).re = a := by linarith
  have hQa : (c * q).re = a := by linarith
  have hchord (v w : ℂ) : ‖c * v - c * w‖ = ‖v - w‖ := by rw [← mul_sub, norm_mul, hc, one_mul]
  have hp2 := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hzp
  have hq2 := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hzq
  rw [← hchord z p, hm, ← ha] at hp2
  rw [← hchord z q, hm, ← ha] at hq2
  simp only [Complex.sub_re, Complex.sub_im, hPa, hQa] at hp2 hq2 hnP hnQ
  rcases le_total 0 (c * p).im with hb | hb
  · apply circle_lens hap hb hnP hnZ
    · nlinarith
    · have he : (c * q).im = -(c * p).im := by linarith
      rw [he] at hq2
      nlinarith
  · have hbq : 0 ≤ (c * q).im := by linarith
    apply circle_lens hap hbq hnQ hnZ
    · nlinarith
    · have he : (c * p).im = -(c * q).im := by linarith
      rw [he] at hp2
      nlinarith

open scoped BigOperators InnerProductSpace

section InsertionChain

open InnerProductGeometry Real

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem unit_chord_sq {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ‖x - y‖ ^ 2 = 2 - 2 * cos (angle x y) := by
  have hcos : cos (angle x y) = ⟪x, y⟫_ℝ := by
    simpa only [hx, hy, mul_one] using cos_angle_mul_norm_mul_norm x y
  rw [norm_sub_pow_two_real, hx, hy, ← hcos]
  ring

/-- A chord of length at most `δ ≤ 1` bounds the angle by `(π / 3) * δ`. -/
theorem angle_le_pi_div_three_mul_of_unit_chord_le {x y : E}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) {δ : ℝ} (hδ₀ : 0 ≤ δ) (hδ₁ : δ ≤ 1)
    (hxy : ‖x - y‖ ≤ δ) : angle x y ≤ (π / 3) * δ := by
  have hangle₀ := angle_nonneg x y
  have hangle₁ := angle_le_pi x y
  have hsin₀ : 0 ≤ sin (angle x y / 2) :=
    sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [pi_pos])
  have hchord : ‖x - y‖ = 2 * sin (angle x y / 2) := by
    apply (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [unit_chord_sq hx hy, mul_pow, sin_sq_eq_half_sub,
      show 2 * (angle x y / 2) = angle x y by ring]
    ring
  have hδangle₀ : 0 ≤ δ * (π / 6) := by positivity
  have hδangle₁ : δ * (π / 6) ≤ π / 6 := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hδ₁ (by positivity : 0 ≤ π / 6)
  have hconc := strictConcaveOn_sin_Icc.concaveOn.2
    (x := π / 6) (y := 0) ⟨by positivity, by linarith [pi_pos]⟩ ⟨le_rfl, pi_pos.le⟩
    hδ₀ (sub_nonneg.mpr hδ₁) (show δ + (1 - δ) = 1 by ring)
  have hsin : δ / 2 ≤ sin (δ * (π / 6)) := by
    simpa only [smul_eq_mul, sin_pi_div_six, sin_zero, mul_zero, add_zero,
      mul_one_div] using hconc
  have hhalf : angle x y / 2 ≤ δ * (π / 6) := by
    apply (strictMonoOn_sin.le_iff_le
      ⟨by linarith [pi_pos], by linarith⟩ ⟨by linarith [pi_pos], by linarith [pi_pos]⟩).mp
    exact (show sin (angle x y / 2) ≤ δ / 2 by linarith [hchord]).trans hsin
  linarith

/-- Follow a single insertion order, with the head of the list inserted last.
Only vectors and insertion chords along that chain are constrained. -/
theorem ordered_finset_unit_chord_lt_sqrt_three {ι : Type*} [DecidableEq ι]
    (order : List ι) (horder : order.Nodup) (v : Finset ι → E) (δ : ι → ℝ)
    (hv : ∀ t : List ι, t <:+ order → ‖v t.toFinset‖ = 1)
    (hδ₀ : ∀ i ∈ order.toFinset, 0 ≤ δ i) (hδ₁ : ∀ i ∈ order.toFinset, δ i ≤ 1)
    (hstep : ∀ i (t : List ι), i :: t <:+ order → ‖v (insert i t.toFinset) - v t.toFinset‖ ≤ δ i)
    (hsum : ∑ i ∈ order.toFinset, δ i < 2) : ‖v order.toFinset - v ∅‖ < √3 := by
  have hv₀ : ‖v ∅‖ = 1 := by simpa only [List.toFinset_nil] using hv [] List.nil_suffix
  have hangles (t : List ι) (ht : t <:+ order) :
      angle (v ∅) (v t.toFinset) ≤ (π / 3) * ∑ i ∈ t.toFinset, δ i := by
    induction t with
    | nil =>
      have hne : v ∅ ≠ 0 := by
        intro h
        simp [h] at hv₀
      simp [angle_self hne]
    | cons i t ih =>
      have hi : i ∉ t.toFinset := by
        simpa only [List.mem_toFinset] using (List.nodup_cons.mp (ht.nodup horder)).1
      have hit : i ∈ order.toFinset := List.mem_toFinset.mpr (ht.subset List.mem_cons_self)
      have hts := (List.suffix_cons i t).trans ht
      have hangle := angle_le_pi_div_three_mul_of_unit_chord_le
        (hv t hts) (hv (i :: t) ht) (hδ₀ i hit) (hδ₁ i hit)
        (by rw [norm_sub_rev, List.toFinset_cons]; exact hstep i t ht)
      calc
        angle (v ∅) (v (i :: t).toFinset) ≤
            angle (v ∅) (v t.toFinset) + angle (v t.toFinset) (v (i :: t).toFinset) :=
          angle_le_angle_add_angle _ _ _
        _ ≤ (π / 3) * ∑ j ∈ t.toFinset, δ j + (π / 3) * δ i := add_le_add (ih hts) hangle
        _ = (π / 3) * ∑ j ∈ (i :: t).toFinset, δ j := by
          rw [List.toFinset_cons, Finset.sum_insert hi, mul_add, add_comm]
  have hlt : angle (v ∅) (v order.toFinset) < 2 * π / 3 := by
    calc
      _ ≤ (π / 3) * ∑ i ∈ order.toFinset, δ i := hangles order List.suffix_rfl
      _ < (π / 3) * 2 := mul_lt_mul_of_pos_left hsum (by positivity)
      _ = _ := by ring
  have hcos := cos_lt_cos_of_nonneg_of_le_pi
    (angle_nonneg (v ∅) (v order.toFinset)) (show 2 * π / 3 ≤ π by linarith [pi_pos]) hlt
  have hc : cos (2 * π / 3) = -(1 / 2) := by
    rw [show 2 * π / 3 = π - π / 3 by ring, cos_pi_sub, cos_pi_div_three]
  rw [hc] at hcos
  apply (sq_lt_sq₀ (norm_nonneg _) (sqrt_nonneg 3)).mp
  rw [norm_sub_rev, unit_chord_sq hv₀ (hv order List.suffix_rfl), sq_sqrt (by norm_num)]
  linarith

/-- If the insertion estimates hold throughout the subset family, the endpoint
chord is below `√3` whenever the total budget is below two. -/
theorem finset_unit_chord_lt_sqrt_three {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (v : Finset ι → E) (δ : ι → ℝ)
    (hv : ∀ t ⊆ s, ‖v t‖ = 1)
    (hδ₀ : ∀ i ∈ s, 0 ≤ δ i) (hδ₁ : ∀ i ∈ s, δ i ≤ 1)
    (hstep : ∀ t ⊆ s, ∀ i ∈ s, i ∉ t → ‖v (insert i t) - v t‖ ≤ δ i)
    (hsum : ∑ i ∈ s, δ i < 2) : ‖v s - v ∅‖ < √3 := by
  have hsub {t : List ι} (ht : t <:+ s.toList) : t.toFinset ⊆ s := by
    intro i hi
    rw [← s.toList_toFinset, List.mem_toFinset]
    exact ht.subset (List.mem_toFinset.mp hi)
  rw [← s.toList_toFinset]
  refine ordered_finset_unit_chord_lt_sqrt_three s.toList s.nodup_toList v δ
    (fun t ht => hv t.toFinset (hsub ht)) (by simpa only [Finset.toList_toFinset])
    (by simpa only [Finset.toList_toFinset]) ?_ (by simpa only [Finset.toList_toFinset])
  intro i t ht
  have hi := hsub ht (List.mem_toFinset.mpr (List.mem_cons_self : i ∈ i :: t))
  have hnot : i ∉ t.toFinset := by
    simpa only [List.mem_toFinset] using (List.nodup_cons.mp (ht.nodup s.nodup_toList)).1
  exact hstep t.toFinset (hsub ((List.suffix_cons i t).trans ht)) i hi hnot

end InsertionChain

section UnitCircle

private theorem complex_unit_coordinates {z : ℂ} (hz : ‖z‖ = 1) :
    z.re ^ 2 + z.im ^ 2 = 1 := by
  have h := Complex.sq_norm z
  rw [hz, Complex.normSq_apply] at h
  nlinarith

/-- A finite subset of the unit circle whose convex hull misses zero has a supporting
half-plane with an attained chord of length `2 * √(1 - t²)`. -/
theorem unitCircle_halfPlane_with_chord_of_zero_not_mem_convexHull {S : Set ℂ}
    (hS : S.Finite) (hne : S.Nonempty) (hunit : ∀ z ∈ S, ‖z‖ = 1)
    (hzero : 0 ∉ convexHull ℝ S) :
    ∃ (c : ℂ) (t : ℝ), ‖c‖ = 1 ∧ 0 < t ∧ t ≤ 1 ∧ (∀ z ∈ S, t ≤ (c * z).re) ∧
      ∃ p ∈ S, ∃ q ∈ S, 2 * Real.sqrt (1 - t ^ 2) = ‖p - q‖ := by
  classical
  have hconv := convex_convexHull ℝ S
  have hsub := subset_convexHull ℝ S
  obtain ⟨m, hm, hmin⟩ := exists_norm_eq_iInf_of_complete_convex
    (hne.mono hsub) (hS.isCompact_convexHull ℝ).isComplete hconv (0 : ℂ)
  let t := ‖m‖
  have ht : 0 < t := norm_pos_iff.mpr fun hm0 => hzero (hm0 ▸ hm)
  let c := star m * ((t⁻¹ : ℝ) : ℂ)
  have hc : ‖c‖ = 1 := by
    simp only [c, norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr ht)]
    exact mul_inv_cancel₀ ht.ne'
  have hrot : c * m = (t : ℂ) := by
    calc
      c * m = (m * star m) * ((t⁻¹ : ℝ) : ℂ) := by dsimp only [c]; ring
      _ = (t : ℂ) := by
        rw [show m * star m = (‖m‖ : ℂ) ^ 2 from Complex.mul_conj' m]
        change (t : ℂ) ^ 2 * ((t⁻¹ : ℝ) : ℂ) = (t : ℂ)
        exact_mod_cast (show t ^ 2 * t⁻¹ = t by
          rw [pow_two, mul_assoc, mul_inv_cancel₀ ht.ne', mul_one])
  have hsupport (z : ℂ) (hz : z ∈ S) : t ≤ (c * z).re := by
    have h := (norm_eq_iInf_iff_real_inner_le_zero hconv hm).mp hmin z (hsub hz)
    have hproj : ‖m‖ ^ 2 ≤ ⟪m, z⟫_ℝ := by
      rw [zero_sub, inner_neg_left, inner_sub_right, real_inner_self_eq_norm_sq] at h
      linarith
    have hre : (c * z).re = t⁻¹ * ⟪m, z⟫_ℝ := by
      rw [Complex.inner]
      change (star m * ((t⁻¹ : ℝ) : ℂ) * z).re = _
      rw [show star m * ((t⁻¹ : ℝ) : ℂ) * z = ((t⁻¹ : ℝ) : ℂ) * (z * star m) by ring]
      simp [Complex.mul_re]
    rw [hre]
    calc
      t = t⁻¹ * t ^ 2 := by rw [pow_two, ← mul_assoc, inv_mul_cancel₀ ht.ne', one_mul]
      _ ≤ t⁻¹ * ⟪m, z⟫_ℝ := mul_le_mul_of_nonneg_left hproj (inv_nonneg.mpr ht.le)
  have hrotunit (z : ℂ) (hz : z ∈ S) : ‖c * z‖ = 1 := by
    rw [norm_mul, hc, hunit z hz, one_mul]
  obtain ⟨z₀, hz₀⟩ := hne
  have ht₁ : t ≤ 1 := (hsupport z₀ hz₀).trans ((Complex.re_le_norm _).trans_eq (hrotunit z₀ hz₀))
  refine ⟨c, t, hc, ht, ht₁, hsupport, ?_⟩
  by_cases ht_eq : t = 1
  · exact ⟨z₀, hz₀, z₀, hz₀, by simp [ht_eq]⟩
  let r := Real.sqrt (1 - t ^ 2)
  have hr_sq : r ^ 2 = 1 - t ^ 2 :=
    Real.sq_sqrt (by nlinarith [mul_nonneg (sub_nonneg.mpr ht₁) (show 0 ≤ 1 + t by positivity)])
  have hr : 0 < r := Real.sqrt_pos.2 (by
    nlinarith [mul_pos (sub_pos.mpr (lt_of_le_of_ne ht₁ ht_eq)) (show 0 < 1 + t by positivity)])
  let s := hS.toFinset
  have hs : (s : Set ℂ) = S := hS.coe_toFinset
  obtain ⟨w, hw₀, hw₁, hwm⟩ := (Finset.mem_convexHull' (R := ℝ) (s := s)).mp (hs ▸ hm)
  have hrot_sum : ∑ z ∈ s, w z • (c * z) = (t : ℂ) := by
    rw [← hrot, ← hwm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    simp only [Algebra.smul_def]
    ring
  have hre_sum : ∑ z ∈ s, w z * (c * z).re = t := by
    simpa only [map_sum, map_smul, smul_eq_mul, Complex.reCLM_apply, Complex.ofReal_re]
      using congrArg Complex.reCLM hrot_sum
  have him_sum : ∑ z ∈ s, w z * (c * z).im = 0 := by
    simpa only [map_sum, map_smul, smul_eq_mul, Complex.imCLM_apply, Complex.ofReal_im]
      using congrArg Complex.imCLM hrot_sum
  have hsum_zero : ∑ z ∈ s, w z * ((c * z).re - t) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hw₁, one_mul,
      hre_sum, sub_self]
  have hmem {z : ℂ} (hz : z ∈ s) : z ∈ S := hs ▸ Finset.mem_coe.mpr hz
  have hactive (z : ℂ) (hz : z ∈ s) (hwz : 0 < w z) : (c * z).re = t := by
    have hnonneg : ∀ z ∈ s, 0 ≤ w z * ((c * z).re - t) :=
      fun z hz => mul_nonneg (hw₀ z hz) (sub_nonneg.mpr (hsupport z (hmem hz)))
    have hz0 := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum_zero z hz
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz0).resolve_left hwz.ne')
  have him_sq (z : ℂ) (hz : z ∈ s) (hwz : 0 < w z) : (c * z).im ^ 2 = r ^ 2 := by
    have h := complex_unit_coordinates (hrotunit z (hmem hz))
    rw [hactive z hz hwz] at h
    linarith
  have hpositive_weight : ∃ z ∈ s, 0 < w z :=
    (Finset.sum_pos_iff_of_nonneg hw₀).mp (by rw [hw₁]; norm_num)
  have exists_pos (f : ℂ → ℝ) (hf : ∑ z ∈ s, w z * f z = 0)
      (hfne : ∀ z ∈ s, 0 < w z → f z ≠ 0) : ∃ z ∈ s, 0 < w z ∧ 0 < f z := by
    by_contra! h
    have hnonneg (z : ℂ) (hz : z ∈ s) : 0 ≤ -(w z * f z) := by
      rcases (hw₀ z hz).eq_or_lt with hzero | hp
      · rw [← hzero, zero_mul, neg_zero]
      · exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos hp.le (h z hz hp))
    obtain ⟨z, hz, hp⟩ := hpositive_weight
    have hsum : ∑ z ∈ s, -(w z * f z) = 0 := by rw [Finset.sum_neg_distrib, hf, neg_zero]
    have hz0 := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum z hz
    exact hfne z hz hp ((mul_eq_zero.mp (neg_eq_zero.mp hz0)).resolve_left hp.ne')
  have him_ne (z : ℂ) (hz : z ∈ s) (hwz : 0 < w z) : (c * z).im ≠ 0 := by
    intro he
    have h := him_sq z hz hwz
    rw [he, zero_pow (by decide : (2 : ℕ) ≠ 0)] at h
    exact (pow_pos hr 2).ne' h.symm
  obtain ⟨p, hp, hwp, hpim⟩ := exists_pos (fun z => (c * z).im) him_sum him_ne
  obtain ⟨q, hq, hwq, hqim⟩ := exists_pos (fun z => -(c * z).im)
    (by simp only [mul_neg, Finset.sum_neg_distrib, him_sum, neg_zero])
    (fun z hz hwz => neg_ne_zero.mpr (him_ne z hz hwz))
  have hp_im : (c * p).im = r :=
    (sq_eq_sq₀ hpim.le hr.le).mp (him_sq p hp hwp)
  have hq_im : (c * q).im = -r := by
    have h := (sq_eq_sq₀ hqim.le hr.le).mp (by rw [neg_sq]; exact him_sq q hq hwq)
    linarith
  refine ⟨p, hmem hp, q, hmem hq, ?_⟩
  calc
    2 * r = ‖((2 * r : ℝ) : ℂ) * Complex.I‖ := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity)]
    _ = ‖c * p - c * q‖ := by
      congr 1
      apply Complex.ext
      · simp [Complex.mul_re, hactive p hp hwp, hactive q hq hwq]
      · rw [Complex.sub_im, hp_im, hq_im]
        simp [Complex.mul_im]
        ring
    _ = ‖p - q‖ := by rw [← mul_sub, norm_mul, hc, one_mul]

/-- The supporting half-plane threshold yields a bound by the metric diameter. -/
theorem unitCircle_halfPlane_of_zero_not_mem_convexHull {S : Set ℂ}
    (hS : S.Finite) (hne : S.Nonempty) (hunit : ∀ z ∈ S, ‖z‖ = 1)
    (hzero : 0 ∉ convexHull ℝ S) :
    ∃ (c : ℂ) (t : ℝ), ‖c‖ = 1 ∧ 0 ≤ t ∧ (∀ z ∈ S, t ≤ (c * z).re) ∧
      2 * Real.sqrt (1 - t ^ 2) ≤ Metric.diam S := by
  obtain ⟨c, t, hc, ht, _, hsupport, p, hp, q, hq, heq⟩ :=
    unitCircle_halfPlane_with_chord_of_zero_not_mem_convexHull hS hne hunit hzero
  refine ⟨c, t, hc, ht.le, hsupport, ?_⟩
  rw [heq, ← dist_eq_norm]
  exact Metric.dist_le_diam_of_mem hS.isBounded hp hq

end UnitCircle

end UnitaryReconstruction
