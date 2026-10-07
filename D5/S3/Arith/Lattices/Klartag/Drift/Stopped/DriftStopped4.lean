/- GID: D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped4
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped4
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Stopped log determinant drift and integrability estimates. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Drift.Stopped.DriftStopped2
import D5.S3.Arith.Lattices.Klartag.State.PaddedLawSetup
import D5.S3.Arith.Lattices.Klartag.Tail.TailAtStep
import D5.S3.Arith.Lattices.Klartag.Walk.ChainWalk
import D5.S3.Arith.Lattices.Klartag.State.StateInvariant4
import D5.S3.Arith.Lattices.Klartag.Contact.ContactIntegrated

open D5.S3.Arith.Lattices.Klartag.Completion
open D5.S3.Arith.Lattices.Klartag.Construction
open D5.S3.Arith.Lattices.Klartag.Contact
open D5.S3.Arith.Lattices.Klartag.Drift
open D5.S3.Arith.Lattices.Klartag.Drift.Stopped
open D5.S3.Arith.Lattices.Klartag.Gaussian
open D5.S3.Arith.Lattices.Klartag.State
open D5.S3.Arith.Lattices.Klartag.Walk

namespace D5.S3.Arith.Lattices.Klartag.Drift.Stopped.DriftStopped4

open MeasureTheory
open Matrix
open Finset
open Module
open D5.S3.Arith.Lattices.Klartag
open D5.S3.Arith.Lattices.Klartag.Walk.Increments
open D5.S3.Arith.Lattices.Klartag.Walk.StoppedChain
open D5.S3.Arith.Lattices.Klartag.Drift.Stopped.DriftStopped
open D5.S3.Arith.Lattices.Klartag.Drift.Stopped.DriftStopped2
open scoped RealInnerProductSpace

variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι] {Ω : Type*} [MeasurableSpace Ω]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}
  {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)}

/-- `C₁ = c + √(dim)/m`: the second moment enters with the drift's quadratic coefficient, the
first with the bound on `‖V k‖`. -/
noncomputable def C₁ (n : ℕ) (m c : ℝ) : ℝ := c + Real.sqrt n / m

theorem C₁_nonneg {m c : ℝ} (hc : 0 ≤ c) (hm : 0 < m) : 0 ≤ C₁ n m c := by
  rw [C₁]; positivity

/-- **The two cases, kept apart.**  Each summand vanishes outside its own case, so the first sums
by the freeze count and the second by the disjointness of `{τ = k+1}`. -/
theorem stoppedErr_split {η a₀ r₀ c₃ c : ℝ} {N : ℕ} (hN : 1 ≤ N) (hc : 0 ≤ c)
    (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    (hA₀m : symMat A₀ = a₀ • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hη : 0 ≤ η) (hr₀ : 0 ≤ r₀) (hc₃ : 0 ≤ c₃) (hlt : r₀ + c₃ * η < a₀)
    (k : ℕ) (ω : Ω) :
    stoppedErr q W A₀ ξ η r₀ c₃ c N k ω
      ≤ (if k + 1 ≤ tau q W A₀ ξ η r₀ c₃ N ω - 1 then ChainWiring.chainErr q W A₀ ξ k ω else 0)
        + (if k < tau q W A₀ ξ η r₀ c₃ N ω ∧ ¬ (k + 1 ≤ tau q W A₀ ξ η r₀ c₃ N ω - 1) then
            C₁ n (a₀ - (r₀ + c₃ * η)) c * (‖ξ k ω‖ + ‖ξ k ω‖ ^ 2) else 0) := by
  have hm : 0 < a₀ - (r₀ + c₃ * η) := by linarith
  have hC : 0 ≤ C₁ n (a₀ - (r₀ + c₃ * η)) c := C₁_nonneg hc hm
  by_cases h1 : k + 1 ≤ tau q W A₀ ξ η r₀ c₃ N ω - 1
  · rw [if_pos h1, if_neg (by tauto), stoppedErr, if_pos h1]
    simp
  · by_cases h2 : k < tau q W A₀ ξ η r₀ c₃ N ω
    · rw [if_neg h1, if_pos ⟨h2, h1⟩, zero_add]
      refine le_trans (stoppedErr_mid_le hN hc hA₀ hq hne hA₀m hη hr₀ hc₃ hlt h1 h2) ?_
      have hx0 : (0 : ℝ) ≤ ‖ξ k ω‖ := norm_nonneg _
      have hx2 : (0 : ℝ) ≤ ‖ξ k ω‖ ^ 2 := sq_nonneg _
      have hVle : Real.sqrt n / (a₀ - (r₀ + c₃ * η)) ≤ C₁ n (a₀ - (r₀ + c₃ * η)) c := by
        rw [C₁]; linarith
      have hcle : c ≤ C₁ n (a₀ - (r₀ + c₃ * η)) c := by
        rw [C₁]
        have : (0 : ℝ) ≤ Real.sqrt n / (a₀ - (r₀ + c₃ * η)) := by positivity
        linarith
      nlinarith [hx0, hx2, hVle, hcle]
    · rw [if_neg h1, if_neg (by tauto), stoppedErr, if_neg h1, if_neg h2]
      simp

def MaximalHyp2 (ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)) (P : Measure Ω) (N : ℕ) (B : ℝ) : Prop :=
  ∀ f : Ω → ℕ, (∀ ω, f ω < N) →
    Integrable (fun ω => ‖ξ (f ω) ω‖) P → Integrable (fun ω => ‖ξ (f ω) ω‖ ^ 2) P →
    ∫ ω, ‖ξ (f ω) ω‖ ∂P ≤ B ∧ ∫ ω, ‖ξ (f ω) ω‖ ^ 2 ∂P ≤ B

theorem maximalHyp2_of (ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)) (P : Measure Ω) (N : ℕ) {B : ℝ}
    (h : MaximalHyp2 ξ P N B) {f : Ω → ℕ} (hf : ∀ ω, f ω < N)
    (h1 : Integrable (fun ω => ‖ξ (f ω) ω‖) P) (h2 : Integrable (fun ω => ‖ξ (f ω) ω‖ ^ 2) P) :
    ∫ ω, (‖ξ (f ω) ω‖ + ‖ξ (f ω) ω‖ ^ 2) ∂P ≤ 2 * B := by
  obtain ⟨ha, hb⟩ := h f hf h1 h2
  rw [integral_add h1 h2]
  linarith

def MaximalAtAdopted (P : Measure Ω) (ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)) (B : ℝ) : Prop :=
  MaximalHyp2 ξ P (ParamsAdopted2.numStepsAdopted2 n) B

/-- **The numeric side condition** the value of `B` closes: the middle case's total, `C₁·2B`, must
fit the slack the existence step has.  With `C₁ ≤ 3n` and `B ≈ n^{−3.5}` this is `≈ 6 n^{−2.5}`. -/
def SlackHyp (n : ℕ) (m c B slack : ℝ) : Prop := C₁ n m c * (2 * B) ≤ slack

end D5.S3.Arith.Lattices.Klartag.Drift.Stopped.DriftStopped4
