/- GID: D5/S3/Arith/Lattices/Klartag/Completion/TruncSumMean
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Completion/TruncSumMean
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform constants and completion of lattice packing. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Walk.StepSecondMoment
import D5.S3.Arith.Lattices.Klartag.Drift.DriftChargeTotal

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

namespace D5.S3.Arith.Lattices.Klartag.Completion.TruncSumMean

open MeasureTheory
open Finset
open Module
open D5.S3.Arith.Lattices.Klartag
open D5.S3.Arith.Lattices.Klartag.Walk.Increments
open D5.S3.Arith.Lattices.Klartag.State.RawDataInst2

variable {n : ℕ}

/-- **`E[G]` from below.**  `G = ∑_{k<K} min(‖ξ_k‖², cap)`, so the per-step bound sums. -/
theorem integral_sum_sqTrunc_ge {c cap : ℝ} (hcap : 0 < cap) (K : ℕ) :
    (K : ℝ) * (c ^ 2 * (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ)
        - 100 * (c ^ 2) ^ 2 * ((Fintype.card (UT n) : ℝ)) ^ 2 / cap)
      ≤ ∫ ω, (∑ j ∈ Finset.range K, StepTruncVariance.sqTrunc (n := n) c cap j ω)
          ∂(ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))) := by
  classical
  have hint : ∀ j ∈ Finset.range K,
      Integrable (StepTruncVariance.sqTrunc (n := n) c cap j)
        (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))) := by
    intro j _
    refine Integrable.mono' (integrable_const cap)
      (StepTruncVariance.measurable_sqTrunc c cap j).aestronglyMeasurable ?_
    filter_upwards with ω
    have h := StepTruncVariance.sqTrunc_mem_Icc (n := n) (c := c) hcap.le j ω
    rw [Real.norm_eq_abs, abs_of_nonneg h.1]; exact h.2
  rw [integral_finsetSum _ hint]
  calc (K : ℝ) * (c ^ 2 * (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ)
        - 100 * (c ^ 2) ^ 2 * ((Fintype.card (UT n) : ℝ)) ^ 2 / cap)
      = ∑ _j ∈ Finset.range K, (c ^ 2 * (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ)
          - 100 * (c ^ 2) ^ 2 * ((Fintype.card (UT n) : ℝ)) ^ 2 / cap) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ ∑ j ∈ Finset.range K, ∫ ω, StepTruncVariance.sqTrunc (n := n) c cap j ω
          ∂(ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))) :=
        Finset.sum_le_sum fun j _ => StepSecondMoment.integral_sqTrunc_ge hcap j

/-- **`driftCen` from below.**  The shape `hLb` consumes: the centre is at least
`κ(1+ε)` times the summed lower bound, the `(1+1/ε)(c₃η)²` piece being non-negative. -/
theorem driftCen_ge {c cap κ ε c₃ η : ℝ} (hcap : 0 < cap) (hκ : 0 ≤ κ) (hε : 0 < ε) (K : ℕ)
    (hcapeq : cap = η ^ 2) :
    κ * ((1 + ε) * ((K : ℝ) * (c ^ 2 * (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ)
          - 100 * (c ^ 2) ^ 2 * ((Fintype.card (UT n) : ℝ)) ^ 2 / cap)))
      ≤ DriftChargeTotal.driftCen (n := n) c η c₃ κ ε K := by
  subst hcapeq
  rw [DriftChargeTotal.driftCen]
  have hG := integral_sum_sqTrunc_ge (n := n) (c := c) hcap K
  have h1 : (0 : ℝ) ≤ 1 + ε := by linarith
  have hmul : (1 + ε) * ((K : ℝ) * (c ^ 2 * (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ)
        - 100 * (c ^ 2) ^ 2 * ((Fintype.card (UT n) : ℝ)) ^ 2 / η ^ 2))
      ≤ (1 + ε) * (∫ ω, (∑ j ∈ Finset.range K,
          StepTruncVariance.sqTrunc (n := n) c (η ^ 2) j ω)
        ∂(ChainSetup.gaussPath (EuclideanSpace ℝ (UT n)))) :=
    mul_le_mul_of_nonneg_left hG h1
  have hrest : (0 : ℝ) ≤ (1 + 1 / ε) * (c₃ * η) ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_left (by linarith : (1 + ε) * ((K : ℝ) * (c ^ 2
      * (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ)
      - 100 * (c ^ 2) ^ 2 * ((Fintype.card (UT n) : ℝ)) ^ 2 / η ^ 2))
    ≤ (1 + ε) * (∫ ω, (∑ j ∈ Finset.range K,
        StepTruncVariance.sqTrunc (n := n) c (η ^ 2) j ω)
      ∂(ChainSetup.gaussPath (EuclideanSpace ℝ (UT n)))) + (1 + 1 / ε) * (c₃ * η) ^ 2) hκ
  linarith

section Adopted

/-- `η² = 2·h·dim·n` at the adopted parameters. -/
theorem etaAdopted_sq (hn : 3 ≤ n) :
    DriftStopped6.etaAdopted n ^ 2
      = 2 * ParamsAdopted2.stepSizeAdopted2 n * (Fintype.card (UT n) : ℝ) * (n : ℝ) := by
  rw [DriftStopped6.etaAdopted]
  refine Real.sq_sqrt ?_
  have := (TailSideSetup2.stepSizeAdopted2_pos hn).le
  positivity

theorem cAdopted_sq (hn : 3 ≤ n) :
    D5.S3.Arith.Lattices.Klartag.cAdopted n ^ 2 = ParamsAdopted2.stepSizeAdopted2 n := by
  rw [D5.S3.Arith.Lattices.Klartag.cAdopted]
  exact Real.sq_sqrt (TailSideSetup2.stepSizeAdopted2_pos hn).le

/-- **`T·dim ≥ 8·log n`** — the drift scale, from below.  `horizon n = 16·log n/n²` and
`card (UT n) = n(n+1)/2`, so the product is `8·log n·(n+1)/n`.  With `κ ≥ 1/2` and `1 + ε ≥ 1`,
`driftCen_ge_adopted` then gives `driftCen ≥ 4·log n·(1 − 50/n)`, which is exactly what `hLb`
needs against the `−4·log n` on the other side. -/
theorem horizon_mul_card_ge (hn : 3 ≤ n) :
    8 * Real.log n ≤ ChainDrift.horizon n * (Fintype.card (UT n) : ℝ) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hlog : (1 : ℝ) ≤ Real.log n := ChainDrift.log_pos_of_three hn
  have hcard : (Fintype.card (UT n) : ℝ) = (n : ℝ) * ((n : ℝ) + 1) / 2 := by
    rw [ChainWiring.card_UT]
    obtain ⟨t, ht⟩ := Nat.even_mul_succ_self n
    have ht2 : n * (n + 1) = 2 * t := by omega
    rw [ht2, Nat.mul_div_cancel_left t (by norm_num)]
    have hcast : ((n : ℝ)) * ((n : ℝ) + 1) = 2 * (t : ℝ) := by
      have := congrArg (fun k : ℕ => (k : ℝ)) ht2
      push_cast at this
      linarith
    linarith
  rw [ChainDrift.horizon, hcard]
  have hkey : 16 * Real.log n / (n : ℝ) ^ 2 * ((n : ℝ) * ((n : ℝ) + 1) / 2)
      = 8 * Real.log n * (((n : ℝ) + 1) / (n : ℝ)) := by
    field_simp; ring
  rw [hkey]
  have hfrac : (1 : ℝ) ≤ ((n : ℝ) + 1) / (n : ℝ) := by
    rw [le_div_iff₀ hn0]; linarith
  nlinarith [hlog, hfrac]

/-- **`E[G]` from above**, the companion `hbudget` needs: the truncation only lowers, so
`∫ min(‖ξ_k‖², cap) ≤ ∫ ‖ξ_k‖² = c²·dim`, and summing gives `K·c²·dim = T·dim` at `K = N`. -/
theorem integral_sum_sqTrunc_le (_hn : 3 ≤ n) {c cap : ℝ} (hcap : 0 < cap) (K : ℕ) :
    ∫ ω, (∑ j ∈ Finset.range K, StepTruncVariance.sqTrunc (n := n) c cap j ω)
        ∂(ChainSetup.gaussPath (EuclideanSpace ℝ (UT n)))
      ≤ (K : ℝ) * (c ^ 2 * (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ)) := by
  classical
  have hint : ∀ j ∈ Finset.range K,
      Integrable (StepTruncVariance.sqTrunc (n := n) c cap j)
        (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))) := by
    intro j _
    refine Integrable.mono' (integrable_const cap)
      (StepTruncVariance.measurable_sqTrunc c cap j).aestronglyMeasurable ?_
    filter_upwards with ω
    have h := StepTruncVariance.sqTrunc_mem_Icc (n := n) (c := c) hcap.le j ω
    rw [Real.norm_eq_abs, abs_of_nonneg h.1]; exact h.2
  rw [integral_finsetSum _ hint]
  have hstep : ∀ j ∈ Finset.range K,
      ∫ ω, StepTruncVariance.sqTrunc (n := n) c cap j ω
          ∂(ChainSetup.gaussPath (EuclideanSpace ℝ (UT n)))
        ≤ c ^ 2 * (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ) := by
    intro j hj
    have h2i : Integrable (fun ω => ‖ChainSetup.step (ι := UT n) c j ω‖ ^ 2)
        (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))) :=
      ChainSetup.integrable_norm_sq_step c j
    have hmono := integral_mono (hint j hj) h2i
      (fun ω => StepTruncVariance.sqTrunc_le (n := n) (c := c) (cap := cap) j ω)
    rw [StepSecondMoment.integral_norm_step_sq] at hmono
    exact hmono
  calc ∑ j ∈ Finset.range K, ∫ ω, StepTruncVariance.sqTrunc (n := n) c cap j ω
        ∂(ChainSetup.gaussPath (EuclideanSpace ℝ (UT n)))
      ≤ ∑ _j ∈ Finset.range K, c ^ 2 * (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ) :=
        Finset.sum_le_sum hstep
    _ = (K : ℝ) * (c ^ 2 * (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end Adopted

end D5.S3.Arith.Lattices.Klartag.Completion.TruncSumMean
