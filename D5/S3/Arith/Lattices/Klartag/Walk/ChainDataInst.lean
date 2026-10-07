/- GID: D5/S3/Arith/Lattices/Klartag/Walk/ChainDataInst
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Walk/ChainDataInst
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Gaussian matrix walk, filtration and stopped increments. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import Mathlib
import D5.S3.Arith.Lattices.Klartag.Construction.Section5
import D5.S3.Arith.Lattices.Klartag.Contact.Lemma43
import D5.S3.Arith.Lattices.Klartag.Walk.ChainDrift
import D5.S3.Arith.Lattices.Klartag.Construction.LatticeTransfer

open MeasureTheory
open Metric
open Set
open Finset
open Matrix
open scoped ENNReal

open D5.S3.Arith.Lattices.Klartag.Construction
open D5.S3.Arith.Lattices.Klartag.Walk

namespace D5.S3.Arith.Lattices.Klartag.Walk.ChainDataInst

open D5.S3.Arith.Lattices.Klartag.Construction.ConstructionA
open D5.S3.Arith.Lattices.Klartag.Construction.Tiling
open D5.S3.Arith.Lattices.Klartag.Construction.Section5
open D5.S3.Arith.Lattices.Klartag.Construction.LatticeTransfer
open D5.S3.Arith.Lattices.Klartag.Walk.ChainEllipsoid

variable {p n : ℕ}

theorem expected_card_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {ι : Type*} [DecidableEq ι] (W : Finset ι) (Cset : Ω → Finset ι)
    (hsub : ∀ ω, Cset ω ⊆ W)
    (hmeas : ∀ i ∈ W, MeasurableSet {ω | i ∈ Cset ω})
    (weight err : ι → ℝ)
    (htail : ∀ i ∈ W, μ.real {ω | i ∈ Cset ω} ≤ 2 * weight i + err i)
    {θ E : ℝ} (hθ : ∑ i ∈ W, weight i ≤ θ) (hE : ∑ i ∈ W, err i ≤ E) :
    ∫ ω, ((Cset ω).card : ℝ) ∂μ ≤ 2 * θ + E := by
  classical
  have hcard : ∀ ω, ((Cset ω).card : ℝ)
      = ∑ i ∈ W, Set.indicator {ω | i ∈ Cset ω} (fun _ => (1 : ℝ)) ω := by
    intro ω
    have hfil : W.filter (fun i => i ∈ Cset ω) = Cset ω := by
      ext i
      simp only [Finset.mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨hsub ω h, h⟩⟩
    rw [← hfil, Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl (fun i _ => ?_)
    by_cases hi : i ∈ Cset ω <;> simp [Set.indicator, hi]
  have hint : ∀ i ∈ W, Integrable
      (fun ω => Set.indicator {ω | i ∈ Cset ω} (fun _ => (1 : ℝ)) ω) μ :=
    fun i hi => (integrable_const (1 : ℝ)).indicator (hmeas i hi)
  calc ∫ ω, ((Cset ω).card : ℝ) ∂μ
      = ∫ ω, ∑ i ∈ W, Set.indicator {ω | i ∈ Cset ω} (fun _ => (1 : ℝ)) ω ∂μ := by
        simp_rw [hcard]
    _ = ∑ i ∈ W, ∫ ω, Set.indicator {ω | i ∈ Cset ω} (fun _ => (1 : ℝ)) ω ∂μ :=
        integral_finsetSum W hint
    _ = ∑ i ∈ W, μ.real {ω | i ∈ Cset ω} :=
        Finset.sum_congr rfl (fun i hi => integral_indicator_one (hmeas i hi))
    _ ≤ ∑ i ∈ W, (2 * weight i + err i) := Finset.sum_le_sum htail
    _ = 2 * (∑ i ∈ W, weight i) + ∑ i ∈ W, err i := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ 2 * θ + E := by
        have h2 : 2 * (∑ i ∈ W, weight i) ≤ 2 * θ := by linarith
        linarith

structure Params (p n : ℕ) where
  dim_pos : 1 ≤ n
  /-- The lattice scale: `αⁿ·p^{n-1} = κ_n`, so `covol(α·Λ(g)) = Vol(Bⁿ)`. -/
  alpha : ℝ
  alpha_pos : 0 < alpha
  alpha_norm : alpha ^ n * ((p ^ (n - 1) : ℕ) : ℝ) = kappa n
  /-- Klartag's `a₀ = (1-1/n)⁻²`, p. 21 eq. (61). -/
  a0 : ℝ
  a0_eq : a0 = (1 - 1 / (n : ℝ))⁻¹ ^ 2
  /-- The unscaled Use-1 radius; `α·R ≤ 1 - 1/n` is `a₀·|αx|² > 1` by `a0_gt_one_iff`. -/
  R : ℝ
  R_nonneg : 0 ≤ R
  R_scaled : alpha * R ≤ 1 - 1 / (n : ℝ)
  R_lt_p : R < (p : ℝ)
  tiling_defect : (n : ℝ) * (alpha * Real.sqrt n / 2) ≤ 1 / 4

  T : ℝ
  T_eq : T = ChainDrift.horizon n
  N : ℕ
  N_eq : N = ChainDrift.numSteps n 5
  h : ℝ
  h_eq : h = ChainDrift.stepSize n 5
  /-- The window: eq. (55)'s shell `R_t`, unscaled. -/
  windowRadius : ℝ
  window_lt_p : windowRadius < (p : ℝ)
  /-- Lemma 4.3's radial profile, already widened to the cube's worst point. -/
  f : ℝ → ℝ
  f_nonneg : ∀ r : ℝ, 0 ≤ f r
  /-- Eq. (65)'s contact weight and its finite support. -/
  w : (Fin n → ℤ) → ℝ≥0∞
  supp : Finset (Fin n → ℤ)
  supp_ne_zero : ∀ y ∈ supp, y ≠ 0
  supp_radius : ∀ y ∈ supp, ‖toE n y‖ ≤ windowRadius
  dom : ∀ y ∈ supp, ∀ x ∈ cube (toE n y), w y ≤ ENNReal.ofReal (f ‖x‖)
  integrable : Integrable (fun x : EuclideanSpace ℝ (Fin n) => f ‖x‖)
  /-- Lemma 4.3's number: `C = C₁·e^{n²T/8}/n` in the paper's notation. -/
  C : ℝ
  radial_bound : ∫ y in Set.Ioi (0 : ℝ), y ^ (n - 1) * f y ≤ C
  /-- Markov's threshold, `16C₁n⁻²e^{n²T/8}`. -/
  theta : ℝ≥0∞
  theta_ne_zero : theta ≠ 0
  theta_ne_top : theta ≠ ⊤
  markov : 2 * (((p - 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal ((n : ℝ) * kappa n * C))
      < theta * ((p ^ n - 1 : ℕ) : ℝ≥0∞)

/-- **`ChainData` from the chain's parameters.** -/
def chainData_of_params [Fact (Nat.Prime p)] [NeZero p] (P : Params p n) : ChainData p n where
  dim_pos := P.dim_pos
  alpha := P.alpha
  alpha_pos := P.alpha_pos
  alpha_norm := P.alpha_norm
  R := P.R
  R_nonneg := P.R_nonneg
  R_scaled := P.R_scaled
  tiling_defect := P.tiling_defect
  w := P.w
  supp := P.supp
  theta := P.theta
  theta_ne_zero := P.theta_ne_zero
  theta_ne_top := P.theta_ne_top
  weight_bound :=
    D5.S3.Arith.Lattices.Klartag.weight_bound_of_radial P.dim_pos P.supp P.w P.f P.f_nonneg P.dom
      P.integrable P.radial_bound P.theta P.markov
  ball_indivisible := fun _y hy0 hyR =>
    redMod_ne_zero_of_norm_lt hy0 (lt_of_le_of_lt hyR P.R_lt_p)
  supp_indivisible := fun y hy =>
    redMod_ne_zero_of_norm_lt (P.supp_ne_zero y hy)
      (lt_of_le_of_lt (P.supp_radius y hy) P.window_lt_p)

/-- **The composite.**  From the chain's parameters to §5's single line `g`. -/
theorem exists_good_line_of_params [Fact (Nat.Prime p)] [NeZero p] (P : Params p n) :
    ∃ g : Fin n → ZMod p, g ≠ 0 ∧
      (∀ y : Fin n → ℤ, y ≠ 0 → ‖toE n y‖ ≤ P.R → y ∉ latZ p n g) ∧
      ∑ y ∈ P.supp.filter (fun y => y ∈ latZ p n g), P.w y < P.theta :=
  exists_good_line_of_chainData (chainData_of_params P)

theorem exists_scaled_basisMatrix [Fact (Nat.Prime p)] [NeZero p] (hn : 1 ≤ n)
    {α : ℝ} (hα : 0 < α) (hnorm : α ^ n * ((p ^ (n - 1) : ℕ) : ℝ) = kappa n)
    {g : Fin n → ZMod p} (hg : g ≠ 0) :
    ∃ B : Matrix (Fin n) (Fin n) ℝ, B.det ≠ 0 ∧ |B.det| = kappa n ∧
      ∀ y : Fin n → ℤ, B *ᵥ (fun i => (y i : ℝ)) ∈ (α • ·) '' (latR p n g : Set (Fin n → ℝ)) := by
  obtain ⟨B₀, hB₀det, hB₀cov, hB₀mem⟩ := exists_basisMatrix (latR p n g)
  refine ⟨α • B₀, ?_, ?_, ?_⟩
  · rw [Matrix.det_smul]
    exact mul_ne_zero (by positivity) hB₀det
  · rw [Matrix.det_smul, abs_mul, abs_pow, abs_of_pos hα, Fintype.card_fin, hB₀cov,
      covolume_latR hn g hg, ← hnorm]
    push_cast
    ring
  · intro y
    refine ⟨B₀ *ᵥ (fun i => (y i : ℝ)), (hB₀mem _).2 ⟨y, rfl⟩, ?_⟩
    rw [Matrix.smul_mulVec]

/-- **The determinant condition, in Klartag's eq. (68) form.**  With `|det B| = κ_n` the
transfer's hypothesis reduces to `√(det A)·(c·m²) ≤ 1`: the chain's `det A_T ≤ C/n⁴` with
`c ≤ C^{-1/2}`. -/
theorem transfer_det_of_eq68 {m : ℕ} {A B : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ} {c : ℝ}
    (hB : |B.det| = kappa (m + 1))
    (heq68 : Real.sqrt A.det * (c * (m : ℝ) ^ 2) ≤ 1) :
    Real.sqrt (B.det ^ 2 * A.det) * (c * (m : ℝ) ^ 2)
      ≤ (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)).toReal := by
  have hsq : Real.sqrt (B.det ^ 2 * A.det) = |B.det| * Real.sqrt A.det := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq_eq_abs]
  have hk : kappa (m + 1) = (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)).toReal :=
    rfl
  have hkpos : 0 ≤ kappa (m + 1) := kappa_nonneg _
  rw [hsq, hB, ← hk, mul_assoc]
  calc kappa (m + 1) * (Real.sqrt A.det * (c * (m : ℝ) ^ 2))
      ≤ kappa (m + 1) * 1 := by exact mul_le_mul_of_nonneg_left heq68 hkpos
    _ = kappa (m + 1) := mul_one _

end D5.S3.Arith.Lattices.Klartag.Walk.ChainDataInst
