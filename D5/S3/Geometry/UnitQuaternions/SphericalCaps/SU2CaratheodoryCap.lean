/- GID: D5/S3/Geometry/UnitQuaternions/SphericalCaps/SU2CaratheodoryCap
   generality: G
   mirror-B: none(waiver:covered-by-chordal-su2-caratheodory-bounds-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite spherical caps obtained by Caratheodory reduction. -/

import OmegaBuild.Commands
import D5.S3.Geometry.UnitQuaternions.Holonomy.SU2HolonomyHemisphere
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

compile_only_with_mathlib

/-! Omega original.

Finite spherical caps obtained by Caratheodory reduction. The normalization
retains the supporting inequality, including when the comparison cap has
radius greater than a hemisphere.
-/

open scoped Quaternion InnerProductSpace
open Set Real

noncomputable section

namespace Omega.Geometry.SphericalJung

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A positive simplex bound on `dim E + 1` vertices excludes zero from
the convex hull of an arbitrary finite family. -/
theorem zero_not_mem_convexHull_of_dimension {ι : Type*} [Fintype ι]
    (q : ι → E) (n : ℕ) (hn : 0 < n) (hd : Module.finrank ℝ E + 1 ≤ n)
    (hq : ∀ i, ‖q i‖ = 1) {c : ℝ} (hc : c ≤ 1)
    (hpair : ∀ i j, i ≠ j → c ≤ ⟪q i, q j⟫_ℝ)
    (hpos : 0 < c + (1 - c) / n) :
    (0 : E) ∉ convexHull ℝ (range q) := by
  classical
  intro hz
  obtain ⟨κ, _, p, w, hp, hlin, hw, hs, he⟩ :=
    eq_pos_convex_span_of_mem_convexHull hz
  choose f hf using fun j => hp (mem_range_self j)
  have hzero := zero_not_mem_convexHull_of_card_bound p n hn
    (hlin.card_le_finrank_succ.trans
      ((Nat.add_le_add_right (Submodule.finrank_le _) 1).trans hd))
    (fun i => hf i ▸ hq (f i)) hc
    (fun i j hij => by
      rw [← hf i, ← hf j]
      exact hpair _ _ (fun h => hij (hlin.injective ((hf i).symm.trans (h ▸ hf j))))) hpos
  apply hzero
  rw [← he]
  exact (convex_convexHull ℝ (range p)).sum_mem (fun i _ => (hw i).le) hs
    (fun i _ => subset_convexHull ℝ _ (mem_range_self i))

end Omega.Geometry.SphericalJung

namespace Omega.Geometry.SU2Caratheodory

open UnitQuaternion HolonomySpectrum
local notation "U" => unitary ℍ[ℝ]

/-- The four-contact spherical radius. -/
def radius (δ : ℝ) : ℝ := arcsin (√(3 / 2 : ℝ) * sin δ)

theorem radius_facts {δ : ℝ} (hδ : 0 ≤ δ) (hδπ : δ ≤ π / 2)
    (ht : sin δ ^ 2 ≤ 5 / 12) :
    0 ≤ radius δ ∧ radius δ ≤ π / 2 ∧
      sin (radius δ) = √(3 / 2 : ℝ) * sin δ ∧
      cos (radius δ) = √(1 - (3 / 2) * sin δ ^ 2) ∧
      0 < cos (radius δ) ∧ δ ≤ radius δ := by
  have hs : 0 ≤ sin δ := sin_nonneg_of_nonneg_of_le_pi hδ (by linarith [pi_pos])
  have ha : (√(3 / 2 : ℝ)) ^ 2 = 3 / 2 := sq_sqrt (by norm_num)
  have ha₁ : (1 : ℝ) ≤ √(3 / 2 : ℝ) := (le_sqrt (by norm_num) (by norm_num)).2 (by norm_num)
  have hx : 0 ≤ √(3 / 2 : ℝ) * sin δ := mul_nonneg (sqrt_nonneg _) hs
  have hx₁ : √(3 / 2 : ℝ) * sin δ < 1 := by
    nlinarith [sq_nonneg (√(3 / 2 : ℝ) * sin δ), mul_pow (√(3 / 2 : ℝ)) (sin δ) 2]
  have hsin : sin (radius δ) = √(3 / 2 : ℝ) * sin δ :=
    sin_arcsin (by linarith) hx₁.le
  have hcos : cos (radius δ) = √(1 - (3 / 2) * sin δ ^ 2) := by
    rw [radius, cos_arcsin, mul_pow, ha]
  refine ⟨arcsin_nonneg.2 hx, arcsin_le_pi_div_two _, hsin, hcos, ?_, ?_⟩
  · rw [hcos]
    exact sqrt_pos.2 (by linarith)
  · have h := arcsin_le_arcsin (show sin δ ≤ √(3 / 2 : ℝ) * sin δ by nlinarith)
    rwa [arcsin_sin (by linarith [pi_pos]) hδπ] at h

/-- The normalizing center remains within twice its own cap radius after
the candidates move by `δ`, throughout the extended small-defect interval. -/
theorem same_layer {ι κ : Type*} [Fintype ι] {q : ι → U} {v : κ → U}
    {δ : ℝ} (hδ : 0 ≤ δ) (hδπ : δ ≤ π / 2) (ht : sin δ ^ 2 ≤ 5 / 12)
    (C : SU2Cap q (radius δ)) (D : SU2Cap v (radius δ)) (e : ι → κ) (u : U)
    (hp : ∀ i, roundDist (q i * u) (v (e i)) ≤ δ) :
    roundDist (C.center * u) D.center ≤ 2 * radius δ := by
  obtain ⟨hR, hRπ, hsin, hcos, hcospos, hδR⟩ := radius_facts hδ hδπ ht
  let R := radius δ
  let θ := roundDist (C.center * u) D.center
  have hθ : θ ∈ Icc 0 π := ⟨round_nonneg _ _, round_le_pi _ _⟩
  have hproj := cap_projection C D e u hδ hR (by linarith) hp
  change cos (R + δ) ≤ ‖C.nearest‖ * cos θ at hproj
  have hnorm := C.nearest_norm_le_one
  have hlow := C.cos_radius_le_nearest_norm hR (by linarith [pi_pos])
  have hs : 0 ≤ sin δ := sin_nonneg_of_nonneg_of_le_pi hδ (by linarith [pi_pos])
  have hcd : 0 ≤ cos δ := cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos], hδπ⟩
  have ha : (√(3 / 2 : ℝ)) ^ 2 = 3 / 2 := sq_sqrt (by norm_num)
  have hsR : sin R ^ 2 = (3 / 2) * sin δ ^ 2 := by rw [hsin, mul_pow, ha]
  have hcR : cos R ^ 2 = 1 - (3 / 2) * sin δ ^ 2 := by
    nlinarith only [sin_sq_add_cos_sq R, hsR]
  have hhemisphere (h : sin δ ^ 2 ≤ 2 / 5) : R + δ ≤ π / 2 := by
    have hsc : sin R ≤ cos δ := by
      have hn : 0 ≤ sin R := sin_nonneg_of_nonneg_of_le_pi hR (by linarith [pi_pos])
      nlinarith [sin_sq_add_cos_sq δ]
    have hm := strictMonoOn_sin.le_iff_le
      (show R ∈ Icc (-(π / 2)) (π / 2) from ⟨by linarith [pi_pos], hRπ⟩)
      (show π / 2 - δ ∈ Icc (-(π / 2)) (π / 2) from ⟨by linarith [pi_pos], by linarith⟩)
    rw [sin_pi_div_two_sub] at hm
    linarith [(hm.mp hsc)]
  by_cases hh : R + δ ≤ π / 2
  · have hn : 0 ≤ cos (R + δ) := cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos], hh⟩
    have hcθ : 0 ≤ cos θ := nonneg_of_mul_nonneg_right (hn.trans hproj) C.pos
    have hcomp : cos (R + δ) ≤ cos θ := hproj.trans (by nlinarith)
    have hb := (strictAntiOn_cos.le_iff_ge
      (show R + δ ∈ Icc 0 π from ⟨by linarith, by linarith [pi_pos]⟩) hθ).mp hcomp
    change θ ≤ 2 * R
    linarith
  · have htlo : 2 / 5 < sin δ ^ 2 := lt_of_not_ge (fun h => hh (hhemisphere h))
    have hc₂ : cos (2 * R) = 1 - 3 * sin δ ^ 2 := by
      rw [cos_two_mul_eq_one_sub, hsR]
      ring
    have hc₂neg : cos (2 * R) < 0 := by rw [hc₂]; linarith
    have hcδ : 19 / 30 < cos δ := by nlinarith [sin_sq_add_cos_sq δ]
    have hrprod : (√(3 / 2 : ℝ) * sin δ ^ 2) ≤ (5 / 6) * cos R := by
      have hA : 0 ≤ √(3 / 2 : ℝ) * sin δ ^ 2 := by positivity
      have hB : 0 ≤ (5 / 6 : ℝ) * cos R := by positivity
      have htsq : sin δ ^ 2 * sin δ ^ 2 ≤ (5 / 12 : ℝ) ^ 2 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr ht) (by positivity : 0 ≤ 5 / 12 + sin δ ^ 2)]
      nlinarith [mul_pow (√(3 / 2 : ℝ)) (sin δ ^ 2) 2]
    have hcompare : cos R * cos (2 * R) ≤ cos (R + δ) := by
      rw [cos_add, hsin, hc₂]
      have hbound := mul_nonneg (show 0 ≤ cos δ - 19 / 30 by linarith) hcospos.le
      have ht' := mul_nonneg (show 0 ≤ 3 * sin δ ^ 2 - 6 / 5 by linarith) hcospos.le
      nlinarith only [hbound, ht', hrprod]
    have hmul : ‖C.nearest‖ * cos (2 * R) ≤ cos R * cos (2 * R) :=
      mul_le_mul_of_nonpos_right hlow hc₂neg.le
    have hθcos : cos (2 * R) ≤ cos θ := by
      exact le_of_mul_le_mul_left (hmul.trans (hcompare.trans hproj)) C.pos
    change θ ≤ 2 * R
    exact (strictAntiOn_cos.le_iff_ge
      (show 2 * R ∈ Icc 0 π from ⟨by linarith, by linarith⟩) hθ).mp hθcos

/-- Caratheodory gives a normalized nearest-point cap for any finite family,
with no bound on the number of candidates. -/
theorem exists_cap {ι : Type*} [Fintype ι] [Nonempty ι] (q : ι → U)
    {δ R : ℝ} (hδ : 0 ≤ δ) (hδπ : δ ≤ π / 2)
    (hpair : ∀ i j, i ≠ j → roundDist (q i) (q j) ≤ 2 * δ)
    (hpos : -(1 / 4 : ℝ) < cos (2 * δ)) (hR : 0 ≤ R) (hRπ : R ≤ π)
    (hcos : cos R ≤ √(cos (2 * δ) + (1 - cos (2 * δ)) / 4)) :
    Nonempty (SU2Cap q R) := by
  let x (i : ι) := (q i : ℍ[ℝ])
  have hx (i j : ι) (hij : i ≠ j) : cos (2 * δ) ≤ ⟪x i, x j⟫_ℝ :=
    (round_le_iff _ _ (by linarith) (by linarith)).mp (hpair i j hij)
  have hz₀ := SphericalJung.zero_not_mem_convexHull_of_dimension x 5 (by decide)
    (by rw [Quaternion.finrank_eq_four]) (fun _ => norm_coe _) (cos_le_one _)
    hx (by linarith)
  obtain ⟨z, hz, hs⟩ := SphericalJung.exists_min_norm_support x
  have hp : 0 < ‖z‖ := norm_pos_iff.mpr (fun he => hz₀ (he ▸ hz))
  obtain ⟨v, hv, hcap⟩ := SphericalJung.exists_cap x 4 (by decide)
    (.inr (by rw [Quaternion.finrank_eq_four])) (fun _ => norm_coe _)
    (cos_le_one _) hx hz₀
  obtain ⟨w, hw, hw₁, hwz⟩ := SphericalJung.exists_weights_of_mem_convexHull hz
  have hi : cos R ≤ ⟪v, z⟫_ℝ := by
    rw [← hwz, inner_sum]
    simp only [real_inner_smul_right]
    have h := Finset.sum_le_sum (s := Finset.univ)
      (fun i _ => mul_le_mul_of_nonneg_left (hcos.trans (hcap i)) (hw i))
    simpa only [← Finset.sum_mul, hw₁, one_mul] using h
  have hn := real_inner_le_norm v z
  rw [hv, one_mul] at hn
  exact SU2Cap.of_nearest hR hRπ z hz hp (hi.trans hn) hs

/-- The Caratheodory cap is available through the extended small-defect
threshold `sin δ ^ 2 ≤ 5 / 12`. -/
theorem exists_radius_cap {ι : Type*} [Fintype ι] [Nonempty ι] (q : ι → U)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδπ : δ ≤ π / 2) (ht : sin δ ^ 2 ≤ 5 / 12)
    (hpair : ∀ i j, i ≠ j → roundDist (q i) (q j) ≤ 2 * δ) :
    Nonempty (SU2Cap q (radius δ)) := by
  obtain ⟨hR, hRπ, _, hcos, _, _⟩ := radius_facts hδ hδπ ht
  apply exists_cap q hδ hδπ hpair
    (by rw [cos_two_mul_eq_one_sub]; linarith) hR (by linarith [pi_pos])
  rw [hcos, cos_two_mul_eq_one_sub]
  apply le_of_eq
  congr 1
  ring

end Omega.Geometry.SU2Caratheodory
