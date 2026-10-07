/- GID: D5/S3/Arith/Lattices/Klartag/Construction/Scaling
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Construction/Scaling
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Construction A lattices, covolumes and ellipsoid transfer. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import Mathlib

open MeasureTheory
open Metric
open Set
open scoped ENNReal

namespace D5.S3.Arith.Lattices.Klartag.Construction.Scaling

noncomputable section

variable {n : ℕ}

theorem ereal_rhs (c : ℝ) (m : ℕ) :
    (c : EReal) * (m : EReal) ^ 2 = ((c * (m : ℝ) ^ 2 : ℝ) : EReal) := by
  rw [EReal.coe_mul, EReal.coe_pow, EReal.coe_natCast]

theorem ereal_coe_volume_eq {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α} {r : ℝ}
    (hr : 0 ≤ r) (h : μ s = ENNReal.ofReal r) : ((μ s : ℝ≥0∞) : EReal) = (r : EReal) := by
  rw [h, EReal.coe_ennreal_ofReal, max_eq_left hr]

theorem volume_image_ball
    (φ : EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1))) :
    volume (φ '' Metric.ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
      = ENNReal.ofReal |LinearMap.det φ| *
          volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
  MeasureTheory.Measure.addHaar_image_linearMap volume φ _

theorem volume_image_ball_ne_top
    (φ : EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1))) :
    volume (φ '' Metric.ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) ≠ ⊤ := by
  rw [volume_image_ball]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne

theorem smul_image_ball_subset
    (φ ψ : EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    {t : ℝ} (ht : |t| ≤ 1) (hψ : ψ = t • φ) :
    ψ '' Metric.ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1
      ⊆ φ '' Metric.ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 := by
  subst hψ
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨t • x, ?_, ?_⟩
  · rw [mem_ball_zero_iff] at hx ⊢
    rw [norm_smul, Real.norm_eq_abs]
    calc |t| * ‖x‖ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right ht (norm_nonneg x)
      _ = ‖x‖ := one_mul _
      _ < 1 := hx
  · simp

theorem volume_smul_image_ball
    (φ ψ : EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    {t : ℝ} (ht : 0 ≤ t) (hψ : ψ = t • φ) :
    volume (ψ '' Metric.ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
      = ENNReal.ofReal (t ^ (n + 1)) *
          volume (φ '' Metric.ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := by
  subst hψ
  rw [volume_image_ball, volume_image_ball, LinearMap.det_smul, finrank_euclideanSpace_fin,
    abs_mul, abs_pow, abs_of_nonneg ht, ENNReal.ofReal_mul (by positivity), mul_assoc]

theorem exists_volume_eq_of_le
    (φ : EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    (hfree : {v ∈ φ '' Metric.ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 |
        ∀ i, v i ∈ Set.range ((↑) : ℤ → ℝ)} = {0})
    {target : ℝ} (hpos : 0 < target)
    (hge : ENNReal.ofReal target
      ≤ volume (φ '' Metric.ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) :
    ∃ ψ : EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1)),
      volume (ψ '' Metric.ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
          = ENNReal.ofReal target ∧
      {v ∈ ψ '' Metric.ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 |
        ∀ i, v i ∈ Set.range ((↑) : ℤ → ℝ)} = {0} := by
  have htop : volume (φ '' Metric.ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) ≠ ⊤ :=
    volume_image_ball_ne_top φ
  obtain ⟨A, hA0, hAv⟩ :
      ∃ A : ℝ, 0 ≤ A ∧
        volume (φ '' Metric.ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) = ENNReal.ofReal A :=
    ⟨_, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal htop).symm⟩
  rw [hAv] at hge
  have hle : target ≤ A := (ENNReal.ofReal_le_ofReal_iff hA0).1 hge
  have hApos : 0 < A := lt_of_lt_of_le hpos hle
  have hqpos : 0 < target / A := div_pos hpos hApos
  have hqle : target / A ≤ 1 := (div_le_one hApos).2 hle
  set t : ℝ := (target / A) ^ (((n : ℝ) + 1)⁻¹) with ht
  have htpos : 0 < t := Real.rpow_pos_of_pos hqpos _
  have htle : t ≤ 1 := Real.rpow_le_one hqpos.le hqle (by positivity)
  have htpow : t ^ (n + 1) = target / A := by
    have hcast : ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [ht, hcast]
    exact Real.rpow_inv_natCast_pow hqpos.le (Nat.succ_ne_zero n)
  refine ⟨t • φ, ?_, ?_⟩
  · rw [volume_smul_image_ball φ (t • φ) htpos.le rfl, htpow, hAv,
      ← ENNReal.ofReal_mul (by positivity), div_mul_cancel₀ _ hApos.ne']
  · refine Set.Subset.antisymm ?_ ?_
    · intro v hv
      have hv' : v ∈ {v ∈ φ '' Metric.ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 |
          ∀ i, v i ∈ Set.range ((↑) : ℤ → ℝ)} :=
        ⟨smul_image_ball_subset φ (t • φ) (by rw [abs_of_pos htpos]; exact htle) rfl hv.1, hv.2⟩
      rwa [hfree] at hv'
    · have h0 : (0 : EuclideanSpace ℝ (Fin (n + 1))) ∈
          φ '' Metric.ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 := by
        have hmem : (0 : EuclideanSpace ℝ (Fin (n + 1))) ∈
            {v ∈ φ '' Metric.ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 |
              ∀ i, v i ∈ Set.range ((↑) : ℤ → ℝ)} := by
          rw [hfree]; rfl
        exact hmem.1
      obtain ⟨x, hx, hxv⟩ := h0
      intro v hv
      rw [Set.mem_singleton_iff] at hv
      subst hv
      refine ⟨⟨t • x, ?_, ?_⟩, fun i => ⟨0, by simp⟩⟩
      · rw [mem_ball_zero_iff] at hx ⊢
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
        calc t * ‖x‖ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right htle (norm_nonneg x)
          _ = ‖x‖ := one_mul _
          _ < 1 := hx
      · simp [LinearMap.smul_apply, map_smul, hxv]

theorem image_zero_ball (m : ℕ) :
    (0 : EuclideanSpace ℝ (Fin (m + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (m + 1))) ''
        Metric.ball (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 = {0} := by
  ext x
  constructor
  · rintro ⟨y, -, rfl⟩; simp
  · intro hx
    rw [Set.mem_singleton_iff] at hx
    exact ⟨0, by simp, by simp [hx]⟩

theorem case_zero (c : ℝ) :
    ∃ φ : EuclideanSpace ℝ (Fin (0 + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (0 + 1)),
      ((volume (φ '' Metric.ball (0 : EuclideanSpace ℝ (Fin (0 + 1))) 1) : ℝ≥0∞) : EReal)
          = (c : EReal) * ((0 : ℕ) : EReal) ^ 2 ∧
      {v ∈ φ '' Metric.ball (0 : EuclideanSpace ℝ (Fin (0 + 1))) 1 |
        ∀ i, v i ∈ Set.range ((↑) : ℤ → ℝ)} = {0} := by
  refine ⟨0, ?_, ?_⟩
  · rw [image_zero_ball 0, measure_singleton]
    simp
  · rw [image_zero_ball 0]
    ext v
    constructor
    · rintro ⟨hv, -⟩; exact hv
    · intro hv
      rw [Set.mem_singleton_iff] at hv
      exact ⟨by simp [hv], fun i => ⟨0, by simp [hv]⟩⟩

theorem klartag_of_volume_ge (c : ℝ) (hc : 0 < c)
    (H : ∀ m : ℕ, 0 < m →
      ∃ φ : EuclideanSpace ℝ (Fin (m + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (m + 1)),
        ENNReal.ofReal (c * (m : ℝ) ^ 2)
            ≤ volume (φ '' Metric.ball (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) ∧
        {v ∈ φ '' Metric.ball (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 |
          ∀ i, v i ∈ Set.range ((↑) : ℤ → ℝ)} = {0}) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
      let V := EuclideanSpace ℝ (Fin (n + 1))
      ∃ φ : V →ₗ[ℝ] V, let E := φ '' Metric.ball (0 : V) 1
        (MeasureTheory.volume E : EReal) = c * n ^ 2 ∧
        {v ∈ E | ∀ i, v i ∈ Set.range ((↑) : ℤ → ℝ)} = {0} := by
  refine ⟨c, hc, fun m => ?_⟩
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact case_zero c
  · obtain ⟨φ, hvol, hfree⟩ := H m hm
    have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    have hpos : 0 < c * (m : ℝ) ^ 2 := by positivity
    obtain ⟨ψ, hψvol, hψfree⟩ := exists_volume_eq_of_le φ hfree hpos hvol
    refine ⟨ψ, ?_, hψfree⟩
    rw [ereal_rhs]
    exact ereal_coe_volume_eq hpos.le hψvol

end

end D5.S3.Arith.Lattices.Klartag.Construction.Scaling
