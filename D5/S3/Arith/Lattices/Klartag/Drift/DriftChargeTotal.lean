/- GID: D5/S3/Arith/Lattices/Klartag/Drift/DriftChargeTotal
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Drift/DriftChargeTotal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Second order log determinant bounds and accumulated drift. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Drift.DriftChargeMoments

set_option linter.unusedSectionVars false

open D5.S3.Arith.Lattices.Klartag.Completion
open D5.S3.Arith.Lattices.Klartag.Construction
open D5.S3.Arith.Lattices.Klartag.Contact
open D5.S3.Arith.Lattices.Klartag.Drift
open D5.S3.Arith.Lattices.Klartag.Drift.Stopped
open D5.S3.Arith.Lattices.Klartag.Gaussian
open D5.S3.Arith.Lattices.Klartag.Lemma43R
open D5.S3.Arith.Lattices.Klartag.Lemma43R2
open D5.S3.Arith.Lattices.Klartag.State
open D5.S3.Arith.Lattices.Klartag.Tail
open D5.S3.Arith.Lattices.Klartag.Walk

namespace D5.S3.Arith.Lattices.Klartag.Drift.DriftChargeTotal

open MeasureTheory
open ProbabilityTheory
open Matrix
open Finset
open Module
open scoped RealInnerProductSpace
open D5.S3.Arith.Lattices.Klartag
open D5.S3.Arith.Lattices.Klartag.Walk.Increments
open D5.S3.Arith.Lattices.Klartag.Walk.StoppedChain
open D5.S3.Arith.Lattices.Klartag.Drift.Stopped.DriftStopped
open D5.S3.Arith.Lattices.Klartag.Drift.LogDetMartingale

variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}

/-- **The drift charge**, exactly the bracket of `StoppedShortfall.logDet_stopped_ge_final`. -/
noncomputable def driftCharge (q : ι → EuclideanSpace ℝ (UT n)) (W : Finset ι)
    (A₀ : EuclideanSpace ℝ (UT n)) (cstep η r₀ c₃ κ ε : ℝ) (N K : ℕ)
    (ω : ℕ → EuclideanSpace ℝ (UT n)) : ℝ :=
  κ * ((1 + ε) * (∑ j ∈ Finset.range K, StepTruncVariance.sqTrunc cstep (η ^ 2) j ω)
        + (1 + 1 / ε) * (c₃ * η) ^ 2)
    + MidTerm.midCap q W A₀ (ChainSetup.step cstep) η r₀ c₃ N K ω

/-- The centring constant: the mean of the chi-square half only. -/
noncomputable def driftCen (cstep η c₃ κ ε : ℝ) (K : ℕ) : ℝ :=
  κ * ((1 + ε) * (∫ ω, (∑ j ∈ Finset.range K, StepTruncVariance.sqTrunc (n := n) cstep (η ^ 2) j ω)
          ∂(ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))))
        + (1 + 1 / ε) * (c₃ * η) ^ 2)

section Facts

variable {cstep η a₀ r₀ c₃ κ ε : ℝ} {N K : ℕ}

theorem integrable_driftCharge (hN : 1 ≤ N) (hη : 0 ≤ η)
    (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    (hA₀m : symMat A₀ = a₀ • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hr₀ : 0 ≤ r₀) (hc₃ : 0 ≤ c₃) (hlt : r₀ + c₃ * η < a₀) :
    Integrable (driftCharge q W A₀ cstep η r₀ c₃ κ ε N K)
      (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))) := by
  have hG := StepTruncVariance.integrable_sum_sqTrunc (n := n) (c := cstep)
    (cap := η ^ 2) (by positivity) K
  have hM := DriftChargeMoments.integrable_midCap (q := q) (W := W) (A₀ := A₀)
    (cstep := cstep) (N := N) hN hA₀ hq hne hA₀m hη hr₀ hc₃ hlt K
  exact (((hG.const_mul (1 + ε)).add (integrable_const _)).const_mul κ).add hM

/-- **The centred second moment.** -/
theorem integral_driftCharge_sub_cen_sq_le (hN : 1 ≤ N) (hη : 0 ≤ η)
    (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    (hA₀m : symMat A₀ = a₀ • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hr₀ : 0 ≤ r₀) (hc₃ : 0 ≤ c₃) (hlt : r₀ + c₃ * η < a₀) :
    ∫ ω, (driftCharge q W A₀ cstep η r₀ c₃ κ ε N K ω
          - driftCen (n := n) cstep η c₃ κ ε K) ^ 2
        ∂(ChainSetup.gaussPath (EuclideanSpace ℝ (UT n)))
      ≤ 2 * (κ * (1 + ε)) ^ 2 * ((K : ℝ) * (η ^ 2 / 2) ^ 2)
        + 2 * ((K : ℝ) * (cstep ^ 2 * ((n : ℝ) / (a₀ - (r₀ + c₃ * η)) ^ 2))) := by
  classical
  set P := ChainSetup.gaussPath (EuclideanSpace ℝ (UT n)) with hP
  set G : (ℕ → EuclideanSpace ℝ (UT n)) → ℝ :=
    fun ω => ∑ j ∈ Finset.range K, StepTruncVariance.sqTrunc (n := n) cstep (η ^ 2) j ω with hG
  set MC : (ℕ → EuclideanSpace ℝ (UT n)) → ℝ :=
    fun ω => MidTerm.midCap q W A₀ (ChainSetup.step cstep) η r₀ c₃ N K ω with hMC
  have hcap : (0 : ℝ) ≤ η ^ 2 := by positivity
  have hGi : Integrable G P := StepTruncVariance.integrable_sum_sqTrunc (c := cstep) hcap K
  have hGsq : Integrable (fun ω => (G ω - ∫ ω, G ω ∂P) ^ 2) P := by
    have hmem : MemLp G 2 P := by
      refine MemLp.of_bound hGi.aestronglyMeasurable ((K : ℝ) * η ^ 2) ?_
      filter_upwards with ω
      have hnn : (0 : ℝ) ≤ G ω := Finset.sum_nonneg fun j _ =>
        (StepTruncVariance.sqTrunc_mem_Icc (c := cstep) hcap j ω).1
      rw [Real.norm_eq_abs, abs_of_nonneg hnn, hG]
      calc ∑ j ∈ Finset.range K, StepTruncVariance.sqTrunc (n := n) cstep (η ^ 2) j ω
          ≤ ∑ _j ∈ Finset.range K, η ^ 2 :=
            Finset.sum_le_sum fun j _ =>
              (StepTruncVariance.sqTrunc_mem_Icc (c := cstep) hcap j ω).2
        _ = (K : ℝ) * η ^ 2 := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    exact (hmem.sub (memLp_const _)).integrable_sq
  have hMCsq : Integrable (fun ω => (MC ω) ^ 2) P :=
    DriftChargeMoments.integrable_midCap_sq (q := q) (W := W) (A₀ := A₀) (cstep := cstep)
      (N := N) hN hA₀ hq hne hA₀m hη hr₀ hc₃ hlt K

  have hpt : ∀ ω, (driftCharge q W A₀ cstep η r₀ c₃ κ ε N K ω
        - driftCen (n := n) cstep η c₃ κ ε K) ^ 2
      ≤ 2 * (κ * (1 + ε)) ^ 2 * (G ω - ∫ ω, G ω ∂P) ^ 2 + 2 * (MC ω) ^ 2 := by
    intro ω
    have heq : driftCharge q W A₀ cstep η r₀ c₃ κ ε N K ω
          - driftCen (n := n) cstep η c₃ κ ε K
        = (κ * (1 + ε)) * (G ω - ∫ ω, G ω ∂P) + MC ω := by
      rw [driftCharge, driftCen, hG, hMC]; ring
    rw [heq]
    nlinarith [sq_nonneg ((κ * (1 + ε)) * (G ω - ∫ ω, G ω ∂P) - MC ω)]
  have hdi : Integrable (fun ω => (driftCharge q W A₀ cstep η r₀ c₃ κ ε N K ω
      - driftCen (n := n) cstep η c₃ κ ε K) ^ 2) P := by
    refine Integrable.mono' ((hGsq.const_mul (2 * (κ * (1 + ε)) ^ 2)).add
      (hMCsq.const_mul 2)) ?_ ?_
    · exact ((integrable_driftCharge (q := q) (W := W) (A₀ := A₀) (κ := κ) (ε := ε)
        hN hη hA₀ hq hne hA₀m hr₀ hc₃ hlt).sub (integrable_const _)).aestronglyMeasurable.pow 2
    · filter_upwards with ω
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hpt ω
  have hmono : ∫ ω, (driftCharge q W A₀ cstep η r₀ c₃ κ ε N K ω
        - driftCen (n := n) cstep η c₃ κ ε K) ^ 2 ∂P
      ≤ ∫ ω, (2 * (κ * (1 + ε)) ^ 2 * (G ω - ∫ ω, G ω ∂P) ^ 2 + 2 * (MC ω) ^ 2) ∂P :=
    integral_mono hdi ((hGsq.const_mul _).add (hMCsq.const_mul 2)) hpt
  rw [integral_add (hGsq.const_mul _) (hMCsq.const_mul 2), integral_const_mul,
    integral_const_mul] at hmono

  have hvarG : ∫ ω, (G ω - ∫ ω, G ω ∂P) ^ 2 ∂P ≤ (K : ℝ) * (η ^ 2 / 2) ^ 2 := by
    have h := StepTruncVariance.variance_sum_sqTrunc_le (n := n) (c := cstep) hcap K
    rwa [variance_eq_integral hGi.aestronglyMeasurable.aemeasurable] at h
  have hMCb := DriftChargeMoments.integral_midCap_sq_le (q := q) (W := W) (A₀ := A₀)
    (cstep := cstep) (N := N) hN hA₀ hq hne hA₀m hη hr₀ hc₃ hlt K
  have hc0 : (0 : ℝ) ≤ 2 * (κ * (1 + ε)) ^ 2 := by positivity
  nlinarith [hmono, hvarG, hMCb, hc0]

end Facts

end D5.S3.Arith.Lattices.Klartag.Drift.DriftChargeTotal
