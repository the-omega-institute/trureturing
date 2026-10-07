/- GID: D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Stopped log determinant drift and integrability estimates. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Walk.StoppedChain
import D5.S3.Arith.Lattices.Klartag.Walk.ChainSetup

open D5.S3.Arith.Lattices.Klartag.Completion
open D5.S3.Arith.Lattices.Klartag.Construction
open D5.S3.Arith.Lattices.Klartag.Contact
open D5.S3.Arith.Lattices.Klartag.Drift
open D5.S3.Arith.Lattices.Klartag.Gaussian
open D5.S3.Arith.Lattices.Klartag.State
open D5.S3.Arith.Lattices.Klartag.Walk

namespace D5.S3.Arith.Lattices.Klartag.Drift.Stopped.DriftStopped

open MeasureTheory
open Matrix
open Finset
open Module
open D5.S3.Arith.Lattices.Klartag
open D5.S3.Arith.Lattices.Klartag.Walk.Increments
open D5.S3.Arith.Lattices.Klartag.Walk.StoppedChain
open scoped RealInnerProductSpace

variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι] {Ω : Type*} [mΩ : MeasurableSpace Ω]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}
  {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)}

/-- `D^τ_k = log det A_{min k (τ−1)}`. -/
noncomputable def stoppedLogDet (q : ι → EuclideanSpace ℝ (UT n)) (W : Finset ι)
    (A₀ : EuclideanSpace ℝ (UT n)) (ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)) (η r₀ c₃ : ℝ)
    (N k : ℕ) (ω : Ω) : ℝ :=
  ChainWiring.logDet (stoppedState q W A₀ ξ η r₀ c₃ N k ω)

/-- `K^τ_k = F(C_k)` before the stopping time and `⊥` after: the free subspace the drift's `N_k`
and quadratic term read. -/
noncomputable def stoppedSub (q : ι → EuclideanSpace ℝ (UT n)) (W : Finset ι)
    (A₀ : EuclideanSpace ℝ (UT n)) (ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)) (η r₀ c₃ : ℝ)
    (N k : ℕ) (ω : Ω) : Submodule ℝ (EuclideanSpace ℝ (UT n)) :=
  if k < tau q W A₀ ξ η r₀ c₃ N ω then Chain.freeSub q (Chain.chain q W A₀ ξ k ω).2 else ⊥

/-- `V^τ_k = π_k(A_k⁻¹)` before the stopping time and `0` after. -/
noncomputable def stoppedV (q : ι → EuclideanSpace ℝ (UT n)) (W : Finset ι)
    (A₀ : EuclideanSpace ℝ (UT n)) (ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)) (η r₀ c₃ : ℝ)
    (N k : ℕ) (ω : Ω) : EuclideanSpace ℝ (UT n) :=
  if k < tau q W A₀ ξ η r₀ c₃ N ω then
    (Chain.freeSub q (Chain.chain q W A₀ ξ k ω).2).starProjection
      (Discharge.matToUT (symMat (Chain.chain q W A₀ ξ k ω).1)⁻¹)
  else 0

noncomputable def stoppedErr (q : ι → EuclideanSpace ℝ (UT n)) (W : Finset ι)
    (A₀ : EuclideanSpace ℝ (UT n)) (ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)) (η r₀ c₃ c : ℝ)
    (N k : ℕ) (ω : Ω) : ℝ :=
  if k + 1 ≤ tau q W A₀ ξ η r₀ c₃ N ω - 1 then ChainWiring.chainErr q W A₀ ξ k ω
  else if k < tau q W A₀ ξ η r₀ c₃ N ω then
    c * ‖(Chain.freeSub q (Chain.chain q W A₀ ξ k ω).2).starProjection (ξ k ω)‖ ^ 2
      - ⟪stoppedV q W A₀ ξ η r₀ c₃ N k ω, ξ k ω⟫
  else 0

omit [Countable ι] mΩ in

theorem hpt_stopped {η a₀ r₀ c₃ δ : ℝ} {N : ℕ} (hN : 1 ≤ N)
    (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    (hA₀m : symMat A₀ = a₀ • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hη : 0 ≤ η) (hr₀ : 0 ≤ r₀) (hc₃ : 0 ≤ c₃)
    (hlt : r₀ + c₃ * η < a₀)
    (hδ : η / (a₀ - (r₀ + c₃ * η)) ≤ δ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (k : ℕ) (ω : Ω) :
    stoppedLogDet q W A₀ ξ η r₀ c₃ N (k + 1) ω
      ≤ stoppedLogDet q W A₀ ξ η r₀ c₃ N k ω
        + ⟪stoppedV q W A₀ ξ η r₀ c₃ N k ω, ξ k ω⟫
        - (1 / (2 * (a₀ + (r₀ + c₃ * η)) ^ 2 * (1 + δ) ^ 2))
          * ‖(stoppedSub q W A₀ ξ η r₀ c₃ N k ω).starProjection (ξ k ω)‖ ^ 2
        + stoppedErr q W A₀ ξ η r₀ c₃
            (1 / (2 * (a₀ + (r₀ + c₃ * η)) ^ 2 * (1 + δ) ^ 2)) N k ω := by
  set t := tau q W A₀ ξ η r₀ c₃ N ω with ht
  set c := 1 / (2 * (a₀ + (r₀ + c₃ * η)) ^ 2 * (1 + δ) ^ 2) with hc
  by_cases hcase1 : k + 1 ≤ t - 1
  ·
    have hkt : k < t := by omega
    have hk1 : k + 1 < t := by omega
    have hgood : ω ∈ stateGood q W A₀ ξ η r₀ c₃ (k + 1) := stateGood_of_lt_tau hk1
    have hSB : Discharge.StateBounds (symMat (Chain.chain q W A₀ ξ k ω).1)
        (a₀ - (r₀ + c₃ * η)) (a₀ + (r₀ + c₃ * η)) := by
      have := stateBounds_stopped (ξ := ξ) (N := N) hN hA₀ hq hne hA₀m hη hr₀ hc₃ hlt k ω
      rwa [stoppedState, ← ht, min_eq_left (by omega : k ≤ t - 1)] at this
    have hηk : ‖Matrix.toEuclideanCLM (𝕜 := ℝ)
        (symMat ((Chain.freeSub q (Chain.chain q W A₀ ξ k ω).2).starProjection (ξ k ω)))‖ ≤ η :=
      le_trans (StepInputs2.opNorm_symMat_starProjection_le _ _) (hgood.1 k (by omega))
    have hstep := Discharge.hpt_step (q := q) (W := W) (A₀ := A₀) (ξ := ξ) hSB hηk hδ hδ0 hδ1
    have hD1 : stoppedLogDet q W A₀ ξ η r₀ c₃ N (k + 1) ω
        = ChainWiring.logDet (Chain.chain q W A₀ ξ (k + 1) ω).1 := by
      rw [stoppedLogDet, stoppedState, ← ht, min_eq_left (by omega : k + 1 ≤ t - 1)]
    have hD0 : stoppedLogDet q W A₀ ξ η r₀ c₃ N k ω
        = ChainWiring.logDet (Chain.chain q W A₀ ξ k ω).1 := by
      rw [stoppedLogDet, stoppedState, ← ht, min_eq_left (by omega : k ≤ t - 1)]
    have hV : stoppedV q W A₀ ξ η r₀ c₃ N k ω
        = (Chain.freeSub q (Chain.chain q W A₀ ξ k ω).2).starProjection
            (Discharge.matToUT (symMat (Chain.chain q W A₀ ξ k ω).1)⁻¹) := by
      rw [stoppedV, ← ht, if_pos hkt]
    have hK : stoppedSub q W A₀ ξ η r₀ c₃ N k ω
        = Chain.freeSub q (Chain.chain q W A₀ ξ k ω).2 := by
      rw [stoppedSub, ← ht, if_pos hkt]
    have hE : stoppedErr q W A₀ ξ η r₀ c₃ c N k ω = ChainWiring.chainErr q W A₀ ξ k ω := by
      rw [stoppedErr, ← ht, if_pos hcase1]
    rw [hD1, hD0, hV, hK, hE]
    exact hstep
  · by_cases hcase2 : k < t
    ·
      have hfreeze : min (k + 1) (t - 1) = min k (t - 1) := by omega
      have hD : stoppedLogDet q W A₀ ξ η r₀ c₃ N (k + 1) ω
          = stoppedLogDet q W A₀ ξ η r₀ c₃ N k ω := by
        rw [stoppedLogDet, stoppedLogDet, stoppedState, stoppedState, ← ht, hfreeze]
      have hK : stoppedSub q W A₀ ξ η r₀ c₃ N k ω
          = Chain.freeSub q (Chain.chain q W A₀ ξ k ω).2 := by
        rw [stoppedSub, ← ht, if_pos hcase2]
      have hE : stoppedErr q W A₀ ξ η r₀ c₃ c N k ω
          = c * ‖(Chain.freeSub q (Chain.chain q W A₀ ξ k ω).2).starProjection (ξ k ω)‖ ^ 2
            - ⟪stoppedV q W A₀ ξ η r₀ c₃ N k ω, ξ k ω⟫ := by
        rw [stoppedErr, ← ht, if_neg hcase1, if_pos hcase2]
      rw [hD, hK, hE]
      ring_nf
      exact le_refl _
    ·
      have hfreeze : min (k + 1) (t - 1) = min k (t - 1) := by omega
      have hD : stoppedLogDet q W A₀ ξ η r₀ c₃ N (k + 1) ω
          = stoppedLogDet q W A₀ ξ η r₀ c₃ N k ω := by
        rw [stoppedLogDet, stoppedLogDet, stoppedState, stoppedState, ← ht, hfreeze]
      have hK : stoppedSub q W A₀ ξ η r₀ c₃ N k ω = ⊥ := by
        rw [stoppedSub, ← ht, if_neg hcase2]
      have hV : stoppedV q W A₀ ξ η r₀ c₃ N k ω = 0 := by
        rw [stoppedV, ← ht, if_neg hcase2]
      have hE : stoppedErr q W A₀ ξ η r₀ c₃ c N k ω = 0 := by
        rw [stoppedErr, ← ht, if_neg hcase1, if_neg hcase2]
      rw [hD, hK, hV, hE]
      simp

section ErrCond

variable {m0 : MeasurableSpace Ω} {μ : Measure Ω}

noncomputable def errCond (μ : Measure Ω) (ℱ : ℕ → MeasurableSpace Ω)
    (q : ι → EuclideanSpace ℝ (UT n)) (W : Finset ι) (A₀ : EuclideanSpace ℝ (UT n))
    (ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)) (η r₀ c₃ c : ℝ) (N k : ℕ) : Ω → ℝ :=
  μ[stoppedErr q W A₀ ξ η r₀ c₃ c N k|ℱ k]

omit [Countable ι] mΩ in
theorem integrable_errCond (ℱ : ℕ → MeasurableSpace Ω) {η r₀ c₃ c : ℝ} {N k : ℕ} :
    Integrable (errCond μ ℱ q W A₀ ξ η r₀ c₃ c N k) μ :=
  integrable_condExp

omit [Countable ι] mΩ in
/-- **The integral is unchanged** — which is why substituting `errCond` for `err` leaves the drift
bound's conclusion alone. -/
theorem integral_errCond {ℱ : ℕ → MeasurableSpace Ω} {η r₀ c₃ c : ℝ} {N k : ℕ}
    (hm : ℱ k ≤ m0) [SigmaFinite (μ.trim hm)] :
    ∫ ω, errCond μ ℱ q W A₀ ξ η r₀ c₃ c N k ω ∂μ
      = ∫ ω, stoppedErr q W A₀ ξ η r₀ c₃ c N k ω ∂μ :=
  integral_condExp hm

end ErrCond

end D5.S3.Arith.Lattices.Klartag.Drift.Stopped.DriftStopped
