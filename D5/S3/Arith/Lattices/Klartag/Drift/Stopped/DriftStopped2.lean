/- GID: D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped2
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped2
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Stopped log determinant drift and integrability estimates. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Drift.Stopped.DriftStopped
import D5.S3.Arith.Lattices.Klartag.Completion.Assembly

open D5.S3.Arith.Lattices.Klartag.Completion
open D5.S3.Arith.Lattices.Klartag.Construction
open D5.S3.Arith.Lattices.Klartag.Contact
open D5.S3.Arith.Lattices.Klartag.Drift
open D5.S3.Arith.Lattices.Klartag.Drift.Stopped
open D5.S3.Arith.Lattices.Klartag.Gaussian
open D5.S3.Arith.Lattices.Klartag.State
open D5.S3.Arith.Lattices.Klartag.Walk

namespace D5.S3.Arith.Lattices.Klartag.Drift.Stopped.DriftStopped2

open MeasureTheory
open Matrix
open Finset
open Module
open D5.S3.Arith.Lattices.Klartag
open D5.S3.Arith.Lattices.Klartag.Walk.Increments
open D5.S3.Arith.Lattices.Klartag.Walk.StoppedChain
open D5.S3.Arith.Lattices.Klartag.Drift.Stopped.DriftStopped
open scoped RealInnerProductSpace

variable {n : ℕ}

/-- **`‖A⁻¹ y‖ ≤ ‖y‖ / m`** from the quadratic-form lower bound.  With `x = A⁻¹ y`,
`m‖x‖² ≤ ⟪x, A x⟫ = ⟪x, y⟫ ≤ ‖x‖‖y‖`. -/
theorem norm_inv_apply_le {A : Matrix (Fin n) (Fin n) ℝ} {m M : ℝ}
    (hSB : Discharge.StateBounds A m M) (y : EuclideanSpace ℝ (Fin n)) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹ y‖ ≤ ‖y‖ / m := by
  set x := Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹ y with hx
  have hunit : IsUnit A.det := isUnit_iff_ne_zero.2 (ne_of_gt hSB.posDef.det_pos)
  have hAx : Matrix.toEuclideanCLM (𝕜 := ℝ) A x = y := by
    have hmul : (Matrix.toEuclideanCLM (𝕜 := ℝ) A) (Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹ y)
        = (Matrix.toEuclideanCLM (𝕜 := ℝ) (A * A⁻¹)) y := by
      rw [map_mul]; rfl
    rw [hx, hmul, Matrix.mul_nonsing_inv A hunit, map_one]
    rfl
  have h1 := hSB.lower x
  rw [hAx] at h1
  have h2 : ⟪x, y⟫ ≤ ‖x‖ * ‖y‖ := real_inner_le_norm x y
  have hm := hSB.mpos
  rcases eq_or_lt_of_le (norm_nonneg x) with h0 | hpos
  · rw [← h0]
    positivity
  · rw [le_div_iff₀ hm]
    nlinarith [h1, h2]

/-- The Frobenius norm of a symmetric matrix, in the model's currency: `‖matToUT M‖² =
∑_{i,j} M_ij²`. -/
theorem norm_matToUT_sq {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.IsSymm) :
    ‖Discharge.matToUT M‖ ^ 2 = ∑ i, ∑ j, (M i j) ^ 2 := by
  have h := sum_symMat_mul_eq_inner (Discharge.matToUT M) (Discharge.matToUT M)
  rw [real_inner_self_eq_norm_sq] at h
  rw [← h]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
    rw [Discharge.symMat_matToUT hM]; ring

/-- `‖M eⱼ‖² = ∑ᵢ Mᵢⱼ²`. -/
theorem norm_apply_single_sq (M : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) M (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
      = ∑ i, (M i j) ^ 2 := by
  have hcoe : ((Matrix.toEuclideanCLM (𝕜 := ℝ) M) (EuclideanSpace.single j (1 : ℝ))).ofLp
      = fun i => M i j := by
    show M *ᵥ (EuclideanSpace.single j (1 : ℝ)).ofLp = _
    ext i
    simp [Matrix.mulVec_single]
  rw [ChainEllipsoid.norm_sq_eq_dotProduct, hcoe, dotProduct]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **The Frobenius norm as a sum of column norms** — the shape the bound on `V` needs. -/
theorem sum_sq_eq_sum_norm_sq (M : Matrix (Fin n) (Fin n) ℝ) :
    ∑ i, ∑ j, (M i j) ^ 2
      = ∑ j, ‖Matrix.toEuclideanCLM (𝕜 := ℝ) M (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => (norm_apply_single_sq M j).symm

/-- **`‖matToUT A⁻¹‖ ≤ √(dim) / m`.**  The Frobenius norm of the inverse is bounded column by
column by `norm_inv_apply_le`, and `matToUT` is a Frobenius isometry. -/
theorem norm_matToUT_inv_le {A : Matrix (Fin n) (Fin n) ℝ} {m M : ℝ}
    (hSB : Discharge.StateBounds A m M) :
    ‖Discharge.matToUT A⁻¹‖ ≤ Real.sqrt n / m := by
  have hm := hSB.mpos
  have hsymm : A.IsSymm := Matrix.isHermitian_iff_isSymm.1 hSB.posDef.isHermitian
  have hsq : ‖Discharge.matToUT A⁻¹‖ ^ 2 ≤ (n : ℝ) / m ^ 2 := by
    rw [norm_matToUT_sq hsymm.inv, sum_sq_eq_sum_norm_sq]
    have hcol : ∀ j : Fin n,
        ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹ (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
          ≤ (1 / m) ^ 2 := by
      intro j
      have h1 := norm_inv_apply_le hSB (EuclideanSpace.single j (1 : ℝ))
      have h2 : ‖(EuclideanSpace.single j (1 : ℝ) : EuclideanSpace ℝ (Fin n))‖ = 1 := by
        simp
      rw [h2] at h1
      have h3 : 0 ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹ (EuclideanSpace.single j (1 : ℝ))‖ :=
        norm_nonneg _
      nlinarith [h1, h3]
    calc ∑ j, ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹ (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
        ≤ ∑ _j : Fin n, (1 / m) ^ 2 := Finset.sum_le_sum fun j _ => hcol j
      _ = (n : ℝ) * (1 / m) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = (n : ℝ) / m ^ 2 := by field_simp
  have hrhs : (0 : ℝ) ≤ Real.sqrt n / m := by positivity
  have hlhs : (0 : ℝ) ≤ ‖Discharge.matToUT A⁻¹‖ := norm_nonneg _
  have hsqrt : (Real.sqrt n / m) ^ 2 = (n : ℝ) / m ^ 2 := by
    rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  nlinarith [hsq, hrhs, hlhs, hsqrt]

/-- **The bound on `V`** — `‖π_k(A_k⁻¹)‖ ≤ √(dim)/m`, for the stopped chain, everywhere. -/
theorem norm_stoppedV_le {ι : Type*} [DecidableEq ι] [Countable ι] {Ω : Type*}
    [MeasurableSpace Ω] {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι}
    {A₀ : EuclideanSpace ℝ (UT n)} {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)}
    {η a₀ r₀ c₃ : ℝ} {N : ℕ} (hN : 1 ≤ N)
    (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    (hA₀m : symMat A₀ = a₀ • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hη : 0 ≤ η) (hr₀ : 0 ≤ r₀) (hc₃ : 0 ≤ c₃) (hlt : r₀ + c₃ * η < a₀)
    (k : ℕ) (ω : Ω) :
    ‖stoppedV q W A₀ ξ η r₀ c₃ N k ω‖ ≤ Real.sqrt n / (a₀ - (r₀ + c₃ * η)) := by
  have hpos : (0 : ℝ) ≤ Real.sqrt n / (a₀ - (r₀ + c₃ * η)) := by
    have : 0 < a₀ - (r₀ + c₃ * η) := by linarith
    positivity
  rw [stoppedV]
  split
  · rename_i hkt
    have hSB : Discharge.StateBounds (symMat (Chain.chain q W A₀ ξ k ω).1)
        (a₀ - (r₀ + c₃ * η)) (a₀ + (r₀ + c₃ * η)) := by
      have h := stateBounds_stopped (ξ := ξ) (N := N) hN hA₀ hq hne hA₀m hη hr₀ hc₃ hlt k ω
      have hmin : min k (tau q W A₀ ξ η r₀ c₃ N ω - 1) = k := by omega
      rwa [stoppedState, hmin] at h
    exact le_trans (Submodule.norm_starProjection_apply_le _ _) (norm_matToUT_inv_le hSB)
  · simpa using hpos

/-- **The integrand bound at the one disagreeing step.**  At `k = τ − 1` the stopped error is
`c‖π_kξ_k‖² − ⟪V k, ξ k⟫`, and both terms are controlled by `‖ξ k ω‖`: the projection is a
contraction, and `‖V k‖ ≤ √(dim)/m` by §1.  This is the integrand whose integral the drift's
`hbd` needs, and it is the only place the stopped error is not `ChainWiring.chainErr`. -/
theorem stoppedErr_mid_le {ι : Type*} [DecidableEq ι] [Countable ι] {Ω : Type*}
    [MeasurableSpace Ω] {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι}
    {A₀ : EuclideanSpace ℝ (UT n)} {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)}
    {η a₀ r₀ c₃ c : ℝ} {N : ℕ} (hN : 1 ≤ N) (hc : 0 ≤ c)
    (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    (hA₀m : symMat A₀ = a₀ • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hη : 0 ≤ η) (hr₀ : 0 ≤ r₀) (hc₃ : 0 ≤ c₃) (hlt : r₀ + c₃ * η < a₀)
    {k : ℕ} {ω : Ω}
    (hcase1 : ¬ (k + 1 ≤ tau q W A₀ ξ η r₀ c₃ N ω - 1))
    (hcase2 : k < tau q W A₀ ξ η r₀ c₃ N ω) :
    stoppedErr q W A₀ ξ η r₀ c₃ c N k ω
      ≤ c * ‖ξ k ω‖ ^ 2 + (Real.sqrt n / (a₀ - (r₀ + c₃ * η))) * ‖ξ k ω‖ := by
  rw [stoppedErr, if_neg hcase1, if_pos hcase2]
  have hproj : ‖(Chain.freeSub q (Chain.chain q W A₀ ξ k ω).2).starProjection (ξ k ω)‖
      ≤ ‖ξ k ω‖ := Submodule.norm_starProjection_apply_le _ _
  have hquad : c * ‖(Chain.freeSub q (Chain.chain q W A₀ ξ k ω).2).starProjection (ξ k ω)‖ ^ 2
      ≤ c * ‖ξ k ω‖ ^ 2 := by
    refine mul_le_mul_of_nonneg_left ?_ hc
    have h0 : (0 : ℝ) ≤ ‖(Chain.freeSub q (Chain.chain q W A₀ ξ k ω).2).starProjection (ξ k ω)‖ :=
      norm_nonneg _
    nlinarith [hproj, h0]
  have hV := norm_stoppedV_le (ξ := ξ) hN hA₀ hq hne hA₀m hη hr₀ hc₃ hlt k ω
  have hinner : -⟪stoppedV q W A₀ ξ η r₀ c₃ N k ω, ξ k ω⟫
      ≤ (Real.sqrt n / (a₀ - (r₀ + c₃ * η))) * ‖ξ k ω‖ := by
    have h1 : -⟪stoppedV q W A₀ ξ η r₀ c₃ N k ω, ξ k ω⟫
        ≤ ‖stoppedV q W A₀ ξ η r₀ c₃ N k ω‖ * ‖ξ k ω‖ := by
      have := abs_real_inner_le_norm (stoppedV q W A₀ ξ η r₀ c₃ N k ω) (ξ k ω)
      have h2 := neg_abs_le (⟪stoppedV q W A₀ ξ η r₀ c₃ N k ω, ξ k ω⟫)
      linarith [abs_le.1 (le_of_eq (rfl : |⟪stoppedV q W A₀ ξ η r₀ c₃ N k ω, ξ k ω⟫|
        = |⟪stoppedV q W A₀ ξ η r₀ c₃ N k ω, ξ k ω⟫|))]
    exact le_trans h1 (mul_le_mul_of_nonneg_right hV (norm_nonneg _))
  linarith

end D5.S3.Arith.Lattices.Klartag.Drift.Stopped.DriftStopped2
