/- GID: D5/S3/Arith/Lattices/Klartag/Drift/DriftAccumulated
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Drift/DriftAccumulated
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Second order log determinant bounds and accumulated drift. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Walk.ChainErrBudget
import D5.S3.Arith.Lattices.Klartag.Completion.GoodPathBounds
import D5.S3.Arith.Lattices.Klartag.Completion.GoodPathLight
import D5.S3.Arith.Lattices.Klartag.Drift.Stopped.DriftStopped6d
import D5.S3.Arith.Lattices.Klartag.Completion.TerminalRatio

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

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

namespace D5.S3.Arith.Lattices.Klartag.Drift.DriftAccumulated

open MeasureTheory
open Matrix
open Finset
open Module
open scoped NNReal RealInnerProductSpace
open D5.S3.Arith.Lattices.Klartag
open D5.S3.Arith.Lattices.Klartag.Walk.Increments
open D5.S3.Arith.Lattices.Klartag.Walk.StoppedChain
open D5.S3.Arith.Lattices.Klartag.Drift.Stopped.DriftStopped
open D5.S3.Arith.Lattices.Klartag.Drift.Stopped.DriftInputsStopped
open D5.S3.Arith.Lattices.Klartag.State.StateInvariant

section Good

variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι] {Ω : Type*} [m0 : MeasurableSpace Ω]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}
  {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)}

/-- **`DriftStopped5.sum_good_le` with the freeze count removed.**  The indicator restricts the sum
to `k < τ ω − 1`, i.e. to `Finset.range (min m (τ ω − 1))`, and that index is `< τ ω`; so a single
prefix-sum bound at one index replaces "`dim E` freezes, each costing `ε`". -/
theorem sum_good_le_of_prefix {η r₀ c₃ E : ℝ} {N m : ℕ} {ω : Ω} (hN : 1 ≤ N)
    (hr₀ : 0 ≤ r₀) (hc₃ : 0 ≤ c₃)
    (hpre : ∀ K, K < tau q W A₀ ξ η r₀ c₃ N ω →
      ∑ k ∈ Finset.range K, ChainWiring.chainErr q W A₀ ξ k ω ≤ E) :
    ∑ k ∈ Finset.range m,
        (if k + 1 ≤ tau q W A₀ ξ η r₀ c₃ N ω - 1
          then ChainWiring.chainErr q W A₀ ξ k ω else 0)
      ≤ E := by
  classical
  have hτ1 : 1 ≤ tau q W A₀ ξ η r₀ c₃ N ω :=
    one_le_tau (q := q) (W := W) (A₀ := A₀) (ξ := ξ) (η := η) (r₀ := r₀) (c₃ := c₃) hN hr₀ hc₃ ω
  have h1 : ∑ k ∈ Finset.range m,
        (if k + 1 ≤ tau q W A₀ ξ η r₀ c₃ N ω - 1
          then ChainWiring.chainErr q W A₀ ξ k ω else 0)
      = ∑ k ∈ (Finset.range m).filter
          (fun k => k + 1 ≤ tau q W A₀ ξ η r₀ c₃ N ω - 1),
          ChainWiring.chainErr q W A₀ ξ k ω :=
    (Finset.sum_filter _ _).symm
  have h2 : (Finset.range m).filter (fun k => k + 1 ≤ tau q W A₀ ξ η r₀ c₃ N ω - 1)
      = Finset.range (min m (tau q W A₀ ξ η r₀ c₃ N ω - 1)) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, lt_min_iff]
    omega
  rw [h1, h2]
  exact hpre _ (by omega)

/-- **`DriftStopped5.sum_stoppedErr_le` with the accumulated total.**  Only the good-range summand
changes; the middle case is still one increment read at `τ − 1`. -/
theorem sum_stoppedErr_le_acc {η a₀ r₀ c₃ c E : ℝ} {N m : ℕ} {ω : Ω} (hN : 1 ≤ N) (hc : 0 ≤ c)
    (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    (hA₀m : symMat A₀ = a₀ • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hη : 0 ≤ η) (hr₀ : 0 ≤ r₀) (hc₃ : 0 ≤ c₃) (hlt : r₀ + c₃ * η < a₀)
    (hpre : ∀ K, K < tau q W A₀ ξ η r₀ c₃ N ω →
      ∑ k ∈ Finset.range K, ChainWiring.chainErr q W A₀ ξ k ω ≤ E) :
    ∑ k ∈ Finset.range m, stoppedErr q W A₀ ξ η r₀ c₃ c N k ω
      ≤ E + DriftStopped4.C₁ n (a₀ - (r₀ + c₃ * η)) c
          * (‖ξ (tau q W A₀ ξ η r₀ c₃ N ω - 1) ω‖
              + ‖ξ (tau q W A₀ ξ η r₀ c₃ N ω - 1) ω‖ ^ 2) := by
  classical
  have hm : 0 < a₀ - (r₀ + c₃ * η) := by linarith
  have hC : 0 ≤ DriftStopped4.C₁ n (a₀ - (r₀ + c₃ * η)) c := DriftStopped4.C₁_nonneg hc hm
  have hτ1 : 1 ≤ tau q W A₀ ξ η r₀ c₃ N ω :=
    one_le_tau (q := q) (W := W) (A₀ := A₀) (ξ := ξ) (η := η) (r₀ := r₀) (c₃ := c₃) hN hr₀ hc₃ ω
  have hsplit : ∀ k, stoppedErr q W A₀ ξ η r₀ c₃ c N k ω
      ≤ (if k + 1 ≤ tau q W A₀ ξ η r₀ c₃ N ω - 1
          then ChainWiring.chainErr q W A₀ ξ k ω else 0)
        + (if k < tau q W A₀ ξ η r₀ c₃ N ω ∧ ¬ (k + 1 ≤ tau q W A₀ ξ η r₀ c₃ N ω - 1) then
            DriftStopped4.C₁ n (a₀ - (r₀ + c₃ * η)) c * (‖ξ k ω‖ + ‖ξ k ω‖ ^ 2) else 0) := fun k =>
    DriftStopped4.stoppedErr_split hN hc hA₀ hq hne hA₀m hη hr₀ hc₃ hlt k ω
  refine le_trans (Finset.sum_le_sum fun k _ => hsplit k) ?_
  rw [Finset.sum_add_distrib]
  refine add_le_add (sum_good_le_of_prefix hN hr₀ hc₃ hpre) ?_
  rw [DriftStopped5.sum_mid_eq (q := q) (W := W) (A₀ := A₀) (ξ := ξ)
    (fun k => DriftStopped4.C₁ n (a₀ - (r₀ + c₃ * η)) c * (‖ξ k ω‖ + ‖ξ k ω‖ ^ 2)) hτ1]
  split
  · exact le_rfl
  · have hpos : (0 : ℝ) ≤ DriftStopped4.C₁ n (a₀ - (r₀ + c₃ * η)) c
        * (‖ξ (tau q W A₀ ξ η r₀ c₃ N ω - 1) ω‖
            + ‖ξ (tau q W A₀ ξ η r₀ c₃ N ω - 1) ω‖ ^ 2) := by positivity
    linarith

end Good

section Integral

variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι] {Ω : Type*} [m0 : MeasurableSpace Ω]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}
  {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)}
variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- **`DriftStopped6.integral_sum_stoppedErr_le` with the accumulated total.** -/
theorem integral_sum_stoppedErr_le_acc (ℱ : Filtration ℕ m0)
    {η a₀ r₀ c₃ c E B : ℝ} {N m : ℕ}
    (hG : ∀ k, MeasurableSet[ℱ k] (stateGood q W A₀ ξ η r₀ c₃ k))
    (hN : 1 ≤ N) (hc : 0 ≤ c) (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    (hA₀m : symMat A₀ = a₀ • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hη : 0 ≤ η) (hr₀ : 0 ≤ r₀) (hc₃ : 0 ≤ c₃) (hlt : r₀ + c₃ * η < a₀)
    (hpre : ∀ ω : Ω, ∀ K, K < tau q W A₀ ξ η r₀ c₃ N ω →
      ∑ k ∈ Finset.range K, ChainWiring.chainErr q W A₀ ξ k ω ≤ E)
    (hsum : Integrable
      (fun ω => ∑ k ∈ Finset.range m, stoppedErr q W A₀ ξ η r₀ c₃ c N k ω) P)
    (hmax : DriftStopped4.MaximalHyp2 ξ P N B) (hidx : DriftStopped5.IntegrableAtIndex P ξ N) :
    ∫ ω, (∑ k ∈ Finset.range m, stoppedErr q W A₀ ξ η r₀ c₃ c N k ω) ∂P
      ≤ E + DriftStopped4.C₁ n (a₀ - (r₀ + c₃ * η)) c * (2 * B) := by
  have hmeasf : Measurable (fun ω => tau q W A₀ ξ η r₀ c₃ N ω - 1) :=
    DriftStopped5.measurable_tau_sub_one ℱ hG N
  have hltN : ∀ ω, tau q W A₀ ξ η r₀ c₃ N ω - 1 < N := by
    intro ω
    have := tau_le (q := q) (W := W) (A₀ := A₀) (ξ := ξ) (η := η) (r₀ := r₀) (c₃ := c₃)
      (N := N) ω
    omega
  obtain ⟨hi1, hi2⟩ := hidx _ hmeasf hltN
  have hm : 0 < a₀ - (r₀ + c₃ * η) := by linarith
  have hC : 0 ≤ DriftStopped4.C₁ n (a₀ - (r₀ + c₃ * η)) c := DriftStopped4.C₁_nonneg hc hm
  have hrhsInt : Integrable (fun ω => E
      + DriftStopped4.C₁ n (a₀ - (r₀ + c₃ * η)) c
        * (‖ξ (tau q W A₀ ξ η r₀ c₃ N ω - 1) ω‖
            + ‖ξ (tau q W A₀ ξ η r₀ c₃ N ω - 1) ω‖ ^ 2)) P :=
    (integrable_const _).add ((hi1.add hi2).const_mul _)
  have hmono := integral_mono hsum hrhsInt (fun ω =>
    sum_stoppedErr_le_acc hN hc hA₀ hq hne hA₀m hη hr₀ hc₃ hlt (hpre ω))
  have hEq : ∫ ω, (E
        + DriftStopped4.C₁ n (a₀ - (r₀ + c₃ * η)) c
          * (‖ξ (tau q W A₀ ξ η r₀ c₃ N ω - 1) ω‖
              + ‖ξ (tau q W A₀ ξ η r₀ c₃ N ω - 1) ω‖ ^ 2)) ∂P
      = E + DriftStopped4.C₁ n (a₀ - (r₀ + c₃ * η)) c
          * ∫ ω, (‖ξ (tau q W A₀ ξ η r₀ c₃ N ω - 1) ω‖
              + ‖ξ (tau q W A₀ ξ η r₀ c₃ N ω - 1) ω‖ ^ 2) ∂P :=
    DriftStopped6.integral_affine (hi1.add hi2)
  rw [hEq] at hmono
  have hmaxb := DriftStopped4.maximalHyp2_of ξ P N hmax hltN hi1 hi2
  nlinarith [hmono, hmaxb, hC]

/-- **`DriftStopped6.sum_integral_stoppedErr_le` with the accumulated total** — the shape
`ChainDrift.drift_bound` consumes. -/
theorem sum_integral_stoppedErr_le_acc (ℱ : Filtration ℕ m0)
    {η a₀ r₀ c₃ c E B : ℝ} {N m : ℕ}
    (hG : ∀ k, MeasurableSet[ℱ k] (stateGood q W A₀ ξ η r₀ c₃ k))
    (hN : 1 ≤ N) (hc : 0 ≤ c) (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    (hA₀m : symMat A₀ = a₀ • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hη : 0 ≤ η) (hr₀ : 0 ≤ r₀) (hc₃ : 0 ≤ c₃) (hlt : r₀ + c₃ * η < a₀)
    (hpre : ∀ ω : Ω, ∀ K, K < tau q W A₀ ξ η r₀ c₃ N ω →
      ∑ k ∈ Finset.range K, ChainWiring.chainErr q W A₀ ξ k ω ≤ E)
    (hint : ∀ k ∈ Finset.range m, Integrable (stoppedErr q W A₀ ξ η r₀ c₃ c N k) P)
    (hmax : DriftStopped4.MaximalHyp2 ξ P N B) (hidx : DriftStopped5.IntegrableAtIndex P ξ N) :
    ∑ k ∈ Finset.range m, ∫ ω, stoppedErr q W A₀ ξ η r₀ c₃ c N k ω ∂P
      ≤ E + DriftStopped4.C₁ n (a₀ - (r₀ + c₃ * η)) c * (2 * B) := by
  rw [← integral_finsetSum _ hint]
  exact integral_sum_stoppedErr_le_acc ℱ hG hN hc hA₀ hq hne hA₀m hη hr₀ hc₃ hlt hpre
    (integrable_finsetSum _ hint) hmax hidx

/-- **`DriftStopped6.drift_bound_stopped_maximal` with the accumulated total.**  This is a
*re-instantiation*: `DriftStopped6.drift_bound_stopped` already takes the error total `E` as an
input, so only the argument supplied for it changes. -/
theorem drift_bound_stopped_acc {ℱ : Filtration ℕ m0}
    {η a₀ r₀ c₃ c κ E B S : ℝ} {N m : ℕ}
    (hin : ChainDrift.DriftInputs P ⇑ℱ (stoppedLogDet q W A₀ ξ η r₀ c₃ N)
      (DriftStopped6.stoppedFreeDim q W A₀ ξ η r₀ c₃ N)
      (errCond P ⇑ℱ q W A₀ ξ η r₀ c₃ c N) κ m)
    (hG : ∀ k, MeasurableSet[ℱ k] (stateGood q W A₀ ξ η r₀ c₃ k))
    (hκ : 0 ≤ κ)
    (hS : S ≤ ∑ k ∈ Finset.range m, ∫ ω,
      DriftStopped6.stoppedFreeDim q W A₀ ξ η r₀ c₃ N k ω ∂P)
    (hN : 1 ≤ N) (hc : 0 ≤ c) (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    (hA₀m : symMat A₀ = a₀ • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hη : 0 ≤ η) (hr₀ : 0 ≤ r₀) (hc₃ : 0 ≤ c₃) (hlt : r₀ + c₃ * η < a₀)
    (hpre : ∀ ω : Ω, ∀ K, K < tau q W A₀ ξ η r₀ c₃ N ω →
      ∑ k ∈ Finset.range K, ChainWiring.chainErr q W A₀ ξ k ω ≤ E)
    (hint : ∀ k ∈ Finset.range m, Integrable (stoppedErr q W A₀ ξ η r₀ c₃ c N k) P)
    (hmax : DriftStopped4.MaximalHyp2 ξ P N B) (hidx : DriftStopped5.IntegrableAtIndex P ξ N) :
    ∫ ω, stoppedLogDet q W A₀ ξ η r₀ c₃ N m ω ∂P
      ≤ ∫ ω, stoppedLogDet q W A₀ ξ η r₀ c₃ N 0 ω ∂P - κ * S
        + (E + DriftStopped4.C₁ n (a₀ - (r₀ + c₃ * η)) c * (2 * B)) :=
  DriftStopped6.drift_bound_stopped hin hκ hS
    (sum_integral_stoppedErr_le_acc ℱ hG hN hc hA₀ hq hne hA₀m hη hr₀ hc₃ hlt hpre hint hmax hidx)

end Integral

section At

variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}

/-- **`GoodPathBounds.driftRHS` with the error total free.**  `driftRHS n A₀ c₃ ε S` is
`driftRHS_acc n A₀ c₃ (dim E · ε) S` definitionally (`driftRHS_eq`). -/
noncomputable def driftRHS_acc (n : ℕ) (A₀ : EuclideanSpace ℝ (UT n)) (c₃ E S : ℝ) : ℝ :=
  ChainWiring.logDet A₀ - (GoodPathBounds.cqAt n c₃ * D5.S3.Arith.Lattices.Klartag.cAdopted n ^ 2) * S
    + (E + DriftStopped4.C₁ n (GoodPathBounds.mAt n c₃) (GoodPathBounds.cqAt n c₃)
        * (2 * D5.S3.Arith.Lattices.Klartag.B_adopted n))

/-- **`GoodPathBounds.drift_bound_at` with the accumulated total** — `hε`/`hbd` replaced by the
prefix-sum hypothesis, `dim E · ε` by `E`.  Everything else is the frozen proof. -/
theorem drift_bound_at_acc (hn : 2073600 ≤ n) {c₃ E S : ℝ} {m : ℕ}
    (hc₃0 : 0 ≤ c₃) (hc₃η : c₃ * DriftStopped6.etaAdopted n ≤ 1 / 4)
    (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    (hA₀m : symMat A₀ = a0C n • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hinterr : ∀ k, Integrable
      (stoppedErr q W A₀ (ChainSetup.step (D5.S3.Arith.Lattices.Klartag.cAdopted n))
        (DriftStopped6.etaAdopted n) (DriftStopped6.r0Adopted n) c₃ (GoodPathBounds.cqAt n c₃)
        (ParamsAdopted2.numStepsAdopted2 n) k)
      (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))))
    (hS : S ≤ ∑ k ∈ Finset.range m, ∫ ω,
      DriftStopped6.stoppedFreeDim q W A₀ (ChainSetup.step (D5.S3.Arith.Lattices.Klartag.cAdopted n))
        (DriftStopped6.etaAdopted n) (DriftStopped6.r0Adopted n) c₃
        (ParamsAdopted2.numStepsAdopted2 n) k ω
      ∂(ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))))
    (hpre : ∀ ω, ∀ K, K < tau q W A₀ (ChainSetup.step (D5.S3.Arith.Lattices.Klartag.cAdopted n))
        (DriftStopped6.etaAdopted n) (DriftStopped6.r0Adopted n) c₃
        (ParamsAdopted2.numStepsAdopted2 n) ω →
      ∑ k ∈ Finset.range K, ChainWiring.chainErr q W A₀
        (ChainSetup.step (D5.S3.Arith.Lattices.Klartag.cAdopted n)) k ω ≤ E) :
    ∫ ω, stoppedLogDet q W A₀ (ChainSetup.step (D5.S3.Arith.Lattices.Klartag.cAdopted n))
        (DriftStopped6.etaAdopted n) (DriftStopped6.r0Adopted n) c₃
        (ParamsAdopted2.numStepsAdopted2 n) m ω
        ∂(ChainSetup.gaussPath (EuclideanSpace ℝ (UT n)))
      ≤ ∫ ω, stoppedLogDet q W A₀ (ChainSetup.step (D5.S3.Arith.Lattices.Klartag.cAdopted n))
          (DriftStopped6.etaAdopted n) (DriftStopped6.r0Adopted n) c₃
          (ParamsAdopted2.numStepsAdopted2 n) 0 ω
          ∂(ChainSetup.gaussPath (EuclideanSpace ℝ (UT n)))
        - (GoodPathBounds.cqAt n c₃ * D5.S3.Arith.Lattices.Klartag.cAdopted n ^ 2) * S
        + (E + DriftStopped4.C₁ n (GoodPathBounds.mAt n c₃) (GoodPathBounds.cqAt n c₃)
            * (2 * D5.S3.Arith.Lattices.Klartag.B_adopted n)) := by
  have hn3 : 3 ≤ n := by omega
  have hN : 1 ≤ ParamsAdopted2.numStepsAdopted2 n := by
    have := D5.S3.Arith.Lattices.Klartag.three_le_numStepsAdopted2 hn3; omega
  have hG : ∀ k, MeasurableSet[ChainSetup.filtration (F := EuclideanSpace ℝ (UT n)) k]
      (stateGood q W A₀ (ChainSetup.step (D5.S3.Arith.Lattices.Klartag.cAdopted n))
        (DriftStopped6.etaAdopted n) (DriftStopped6.r0Adopted n) c₃ k) :=
    fun k => measurableSet_stateGood_step _ _ _ _ k
  have hlt := GoodPathBounds.lt_a0C_of_mAt hn hc₃η
  have hcq0 := GoodPathBounds.cqAt_nonneg hn hc₃η hc₃0
  have hκ : (0 : ℝ) ≤ GoodPathBounds.cqAt n c₃ * D5.S3.Arith.Lattices.Klartag.cAdopted n ^ 2 := by positivity
  have hrec := driftInputs_stopped (q := q) (W := W) (A₀ := A₀) (m := m) hN hA₀ hq hne hA₀m
    (DriftStopped7.etaAdopted_nonneg (n := n)) (DriftStopped7.r0Adopted_nonneg (n := n)) hc₃0 hlt
    (le_of_eq (by rw [GoodPathBounds.deltaAt, GoodPathBounds.mAt]))
    (GoodPathBounds.deltaAt_nonneg hn hc₃η) (GoodPathBounds.deltaAt_lt_one hn hc₃η)
    (by rw [GoodPathBounds.cqAt, GoodPathBounds.MAt]) hinterr
  exact drift_bound_stopped_acc
    (ℱ := ChainSetup.filtration (F := EuclideanSpace ℝ (UT n)))
    hrec hG hκ hS hN hcq0 hA₀ hq hne hA₀m
    (DriftStopped7.etaAdopted_nonneg (n := n)) (DriftStopped7.r0Adopted_nonneg (n := n))
    hc₃0 hlt hpre (fun k _ => hinterr k)
    (D5.S3.Arith.Lattices.Klartag.maximalAtAdopted_adopted hn3)
    (D5.S3.Arith.Lattices.Klartag.integrableAtIndex_adopted hn3)

end At

section Assembly

variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}

noncomputable def EaccAt (n : ℕ) (c₃ : ℝ) : ℝ := ChainErrBudget.epsAt n c₃

theorem EaccAt_eq (n : ℕ) (c₃ : ℝ) :
    EaccAt n c₃ = c₃ * (DriftStopped6.etaAdopted n / GoodPathBounds.mAt n c₃) := rfl

/-- **The prefix-sum hypothesis, discharged.**  `ChainErrBudget.sum_chainErr_le_of_lt_tau` gives
`|C_K|·η/m`; `stateGood K` (available because `K < τ`) gives `|C_K| ≤ c₃`. -/
theorem sum_chainErr_le_c3 {Ω : Type*} [MeasurableSpace Ω] {xs : ι → (Fin n → ℝ)}
    {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)} {η a₀ r₀ c₃ : ℝ} {N K : ℕ} {ω : Ω}
    (hA₀ : A₀ ∈ Chain.kSet (fun i => ChainWiring.qUT (xs i)) W)
    (hA₀m : symMat A₀ = a₀ • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hη : 0 ≤ η) (hr₀ : 0 ≤ r₀) (hc₃ : 0 ≤ c₃)
    (hlt : r₀ + c₃ * η < a₀) (hδ1 : c₃ * η < a₀ - (r₀ + c₃ * η))
    (hK : K < tau (fun i => ChainWiring.qUT (xs i)) W A₀ ξ η r₀ c₃ N ω) :
    ∑ k ∈ Finset.range K,
        ChainWiring.chainErr (fun i => ChainWiring.qUT (xs i)) W A₀ ξ k ω
      ≤ c₃ * (η / (a₀ - (r₀ + c₃ * η))) := by
  refine le_trans
    (ChainErrBudget.sum_chainErr_le_of_lt_tau hA₀ hA₀m hη hr₀ hc₃ hlt hδ1 hK) ?_
  obtain ⟨-, -, hcnt⟩ := stateGood_of_lt_tau (N := N)
    (q := fun i => ChainWiring.qUT (xs i)) (W := W) (A₀ := A₀) (ξ := ξ)
    (η := η) (r₀ := r₀) (c₃ := c₃) hK
  have hm : 0 < a₀ - (r₀ + c₃ * η) := by linarith
  exact mul_le_mul_of_nonneg_right hcnt (by positivity)

end Assembly

section GoodPathFree

open D5.S3.Arith.Lattices.Klartag.Construction.ConstructionA
open D5.S3.Arith.Lattices.Klartag.Construction.Tiling
open D5.S3.Arith.Lattices.Klartag.State.PaddedLawSetupR
open D5.S3.Arith.Lattices.Klartag.State.RawDataInst2R
open D5.S3.Arith.Lattices.Klartag.State.RawDataInst2

variable {p m : ℕ} {α C' : ℝ} {g : Fin (m + 1) → ZMod p}

end GoodPathFree

section Numbers

end Numbers

end D5.S3.Arith.Lattices.Klartag.Drift.DriftAccumulated
