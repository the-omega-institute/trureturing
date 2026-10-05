/- GID: D5/S3/Arith/Lattices/Klartag/Drift/DriftChargeMoments
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Drift/DriftChargeMoments
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Second order log determinant bounds and accumulated drift. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Walk.StoppedShortfall

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

namespace D5.S3.Arith.Lattices.Klartag.Drift.DriftChargeMoments

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

theorem integrable_midCap_sq {cstep η a₀ r₀ c₃ : ℝ} {N : ℕ} (hN : 1 ≤ N)
    (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    (hA₀m : symMat A₀ = a₀ • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hη : 0 ≤ η) (hr₀ : 0 ≤ r₀) (hc₃ : 0 ≤ c₃) (hlt : r₀ + c₃ * η < a₀) (K : ℕ) :
    Integrable (fun ω => (MidTerm.midCap q W A₀ (ChainSetup.step cstep) η r₀ c₃ N K ω) ^ 2)
      (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))) := by
  have hfun : (fun ω => (MidTerm.midCap q W A₀ (ChainSetup.step cstep) η r₀ c₃ N K ω) ^ 2)
      = fun ω => ∑ j ∈ Finset.range K,
          (mgIncr q W A₀ (ChainSetup.step cstep) η r₀ c₃ N j ω) ^ 2 := by
    funext ω; exact MidTerm.midCap_sq
  rw [hfun]
  exact integrable_finsetSum _ fun j _ =>
    integrable_mgIncr_sq (q := q) (W := W) (A₀ := A₀) (cstep := cstep) (N := N)
      hN hA₀ hq hne hA₀m hη hr₀ hc₃ hlt j

/-- **`∫ midCap² ≤ K·cstep²·n/m²`**, the same bound `variance_M_le` carries. -/
theorem integral_midCap_sq_le {cstep η a₀ r₀ c₃ : ℝ} {N : ℕ} (hN : 1 ≤ N)
    (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    (hA₀m : symMat A₀ = a₀ • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hη : 0 ≤ η) (hr₀ : 0 ≤ r₀) (hc₃ : 0 ≤ c₃) (hlt : r₀ + c₃ * η < a₀) (K : ℕ) :
    ∫ ω, (MidTerm.midCap q W A₀ (ChainSetup.step cstep) η r₀ c₃ N K ω) ^ 2
        ∂(ChainSetup.gaussPath (EuclideanSpace ℝ (UT n)))
      ≤ (K : ℝ) * (cstep ^ 2 * ((n : ℝ) / (a₀ - (r₀ + c₃ * η)) ^ 2)) := by
  have hfun : (fun ω => (MidTerm.midCap q W A₀ (ChainSetup.step cstep) η r₀ c₃ N K ω) ^ 2)
      = fun ω => ∑ j ∈ Finset.range K,
          (mgIncr q W A₀ (ChainSetup.step cstep) η r₀ c₃ N j ω) ^ 2 := by
    funext ω; exact MidTerm.midCap_sq
  rw [hfun, integral_finsetSum _ fun j _ =>
    integrable_mgIncr_sq (q := q) (W := W) (A₀ := A₀) (cstep := cstep) (N := N)
      hN hA₀ hq hne hA₀m hη hr₀ hc₃ hlt j]
  calc ∑ j ∈ Finset.range K, ∫ ω, (mgIncr q W A₀ (ChainSetup.step cstep) η r₀ c₃ N j ω) ^ 2
        ∂(ChainSetup.gaussPath (EuclideanSpace ℝ (UT n)))
      ≤ ∑ _j ∈ Finset.range K, cstep ^ 2 * ((n : ℝ) / (a₀ - (r₀ + c₃ * η)) ^ 2) :=
        Finset.sum_le_sum fun j _ =>
          integral_mgIncr_sq_le (q := q) (W := W) (A₀ := A₀) (cstep := cstep) (N := N)
            hN hA₀ hq hne hA₀m hη hr₀ hc₃ hlt j
    _ = (K : ℝ) * (cstep ^ 2 * ((n : ℝ) / (a₀ - (r₀ + c₃ * η)) ^ 2)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- `midCap` itself is integrable: `√x ≤ (1 + x)/2`. -/
theorem integrable_midCap {cstep η a₀ r₀ c₃ : ℝ} {N : ℕ} (hN : 1 ≤ N)
    (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    (hA₀m : symMat A₀ = a₀ • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hη : 0 ≤ η) (hr₀ : 0 ≤ r₀) (hc₃ : 0 ≤ c₃) (hlt : r₀ + c₃ * η < a₀) (K : ℕ) :
    Integrable (fun ω => MidTerm.midCap q W A₀ (ChainSetup.step cstep) η r₀ c₃ N K ω)
      (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))) := by
  have hsq := integrable_midCap_sq (q := q) (W := W) (A₀ := A₀) (cstep := cstep) (N := N)
    hN hA₀ hq hne hA₀m hη hr₀ hc₃ hlt K
  have hmeas : AEStronglyMeasurable
      (fun ω => MidTerm.midCap q W A₀ (ChainSetup.step cstep) η r₀ c₃ N K ω)
      (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))) := by
    have h1 : AEStronglyMeasurable
        (fun ω => Real.sqrt ((MidTerm.midCap q W A₀ (ChainSetup.step cstep) η r₀ c₃ N K ω) ^ 2))
        (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))) :=
      Real.continuous_sqrt.comp_aestronglyMeasurable hsq.aestronglyMeasurable
    have h2 : (fun ω => Real.sqrt
          ((MidTerm.midCap q W A₀ (ChainSetup.step cstep) η r₀ c₃ N K ω) ^ 2))
        = fun ω => MidTerm.midCap q W A₀ (ChainSetup.step cstep) η r₀ c₃ N K ω := by
      funext ω; exact Real.sqrt_sq MidTerm.midCap_nonneg
    rw [h2] at h1
    exact h1
  refine Integrable.mono' ((integrable_const (1 : ℝ)).add hsq) hmeas ?_
  filter_upwards with ω
  have h0 : 0 ≤ MidTerm.midCap q W A₀ (ChainSetup.step cstep) η r₀ c₃ N K ω :=
    MidTerm.midCap_nonneg
  have hkey : (0 : ℝ) ≤ (MidTerm.midCap q W A₀ (ChainSetup.step cstep) η r₀ c₃ N K ω) ^ 2
      - 2 * (MidTerm.midCap q W A₀ (ChainSetup.step cstep) η r₀ c₃ N K ω) + 1 := by
    nlinarith [sq_nonneg (MidTerm.midCap q W A₀ (ChainSetup.step cstep) η r₀ c₃ N K ω - 1)]
  simp only [Pi.add_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  nlinarith [hkey, h0, sq_nonneg (MidTerm.midCap q W A₀ (ChainSetup.step cstep) η r₀ c₃ N K ω)]

end D5.S3.Arith.Lattices.Klartag.Drift.DriftChargeMoments
