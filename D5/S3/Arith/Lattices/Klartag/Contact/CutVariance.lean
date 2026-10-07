/- GID: D5/S3/Arith/Lattices/Klartag/Contact/CutVariance
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Contact/CutVariance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Contact profile counts and accumulated projection dimension. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Drift.DriftAccumulated
import D5.S3.Arith.Lattices.Klartag.Completion.Theorem2R4
import D5.S3.Arith.Lattices.Klartag.Completion.GoodPathBounds
import D5.S3.Arith.Lattices.Klartag.Completion.FinalDischarge
import D5.S3.Arith.Lattices.Klartag.Completion.GoodPathVar

set_option linter.unusedSectionVars false

open D5.S3.Arith.Lattices.Klartag.Completion
open D5.S3.Arith.Lattices.Klartag.Construction
open D5.S3.Arith.Lattices.Klartag.Contact
open D5.S3.Arith.Lattices.Klartag.Drift
open D5.S3.Arith.Lattices.Klartag.Drift.Stopped
open D5.S3.Arith.Lattices.Klartag.Gaussian
open D5.S3.Arith.Lattices.Klartag.Lemma43R
open D5.S3.Arith.Lattices.Klartag.Lemma43R2
open D5.S3.Arith.Lattices.Klartag.Lemma43R3
open D5.S3.Arith.Lattices.Klartag.State
open D5.S3.Arith.Lattices.Klartag.Tail
open D5.S3.Arith.Lattices.Klartag.Walk

namespace D5.S3.Arith.Lattices.Klartag.Contact.CutVariance

open MeasureTheory
open Matrix
open Finset
open Module
open D5.S3.Arith.Lattices.Klartag
open D5.S3.Arith.Lattices.Klartag.Walk.Increments
open D5.S3.Arith.Lattices.Klartag.Walk.StoppedChain
open D5.S3.Arith.Lattices.Klartag.Drift.Stopped.DriftStopped
open D5.S3.Arith.Lattices.Klartag.Drift.Stopped.DriftStopped5
open D5.S3.Arith.Lattices.Klartag.Drift.Stopped.DriftInputsStopped
open D5.S3.Arith.Lattices.Klartag.Completion.GoodPathBounds
open D5.S3.Arith.Lattices.Klartag.Drift.DriftAccumulated
open scoped NNReal RealInnerProductSpace

section Cut

variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}

theorem goodPathCut_var (hn : 2073600 ≤ n) {c₃ ε E S L b s pcnt r : ℝ} {K : ℕ} (hr : 0 < r)
    (hKN : K < ParamsAdopted2.numStepsAdopted2 n)
    (hc₃0 : 0 ≤ c₃) (hc₃η : c₃ * DriftStopped6.etaAdopted n ≤ 1 / 4)
    (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    (hA₀m : symMat A₀ = a0C n • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hε : 0 ≤ ε)
    (hbdabs : ChainErrBudget.StoppedErrBudget q W A₀
      (ChainSetup.step (D5.S3.Arith.Lattices.Klartag.cAdopted n)) (DriftStopped6.etaAdopted n)
      (DriftStopped6.r0Adopted n) c₃ (ParamsAdopted2.numStepsAdopted2 n) ε)
    (hpre : ∀ ω, ∀ J, J < tau q W A₀ (ChainSetup.step (D5.S3.Arith.Lattices.Klartag.cAdopted n))
        (DriftStopped6.etaAdopted n) (DriftStopped6.r0Adopted n) c₃
        (ParamsAdopted2.numStepsAdopted2 n) ω →
      ∑ k ∈ Finset.range J, ChainWiring.chainErr q W A₀
        (ChainSetup.step (D5.S3.Arith.Lattices.Klartag.cAdopted n)) k ω ≤ E)
    (hS : S ≤ ∑ k ∈ Finset.range K, ∫ ω,
      DriftStopped6.stoppedFreeDim q W A₀ (ChainSetup.step (D5.S3.Arith.Lattices.Klartag.cAdopted n))
        (DriftStopped6.etaAdopted n) (DriftStopped6.r0Adopted n) c₃
        (ParamsAdopted2.numStepsAdopted2 n) k ω
      ∂(ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))))
    (hcnt : (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))).real
        (StateInvariant4.countGood q W A₀ (ChainSetup.step (D5.S3.Arith.Lattices.Klartag.cAdopted n))
          K c₃)ᶜ ≤ pcnt)
    (hshort : ∫ ω, max (L - stoppedLogDet q W A₀
        (ChainSetup.step (D5.S3.Arith.Lattices.Klartag.cAdopted n)) (DriftStopped6.etaAdopted n)
        (DriftStopped6.r0Adopted n) c₃ (ParamsAdopted2.numStepsAdopted2 n) K ω) 0
      ∂(ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))) ≤ s)
    (hLb : L < b)
    (hbudget : (driftRHS_acc n A₀ c₃ E S - L + s) / (b - L)
      + GoodPathBounds.failTotal n pcnt < 1) :
    ∃ ω, ω ∈ GoodPathBounds.goodCut r (ChainSetup.coord 0)
        (ChainSetup.step (D5.S3.Arith.Lattices.Klartag.cAdopted n)) (6 * r * 1 * Real.sqrt n)
        (ParamsAdopted2.numStepsAdopted2 n) (DriftStopped6.etaAdopted n) q W A₀
        (DriftStopped6.r0Adopted n) c₃ K ∧
      ChainWiring.logDet (Chain.chain q W A₀
        (ChainSetup.step (D5.S3.Arith.Lattices.Klartag.cAdopted n)) K ω).1 ≤ b := by
  have hn3 : 3 ≤ n := by omega
  have hN : 1 ≤ ParamsAdopted2.numStepsAdopted2 n := by omega
  have hξm : ∀ j, Measurable (ChainSetup.step (ι := UT n) (D5.S3.Arith.Lattices.Klartag.cAdopted n) j) :=
    fun j => ChainSetup.measurable_step _ j
  have hG : ∀ k, MeasurableSet[ChainSetup.filtration (F := EuclideanSpace ℝ (UT n)) k]
      (stateGood q W A₀ (ChainSetup.step (D5.S3.Arith.Lattices.Klartag.cAdopted n))
        (DriftStopped6.etaAdopted n) (DriftStopped6.r0Adopted n) c₃ k) :=
    fun k => measurableSet_stateGood_step _ _ _ _ k
  have hτ : Measurable (tau q W A₀ (ChainSetup.step (D5.S3.Arith.Lattices.Klartag.cAdopted n))
      (DriftStopped6.etaAdopted n) (DriftStopped6.r0Adopted n) c₃
      (ParamsAdopted2.numStepsAdopted2 n)) :=
    DriftStopped5.measurable_tau (ChainSetup.filtration (F := EuclideanSpace ℝ (UT n))) hG _
  have hlt := GoodPathBounds.lt_a0C_of_mAt hn hc₃η
  have hinterr := fun k => ChainErrBudget.integrable_stoppedErr_of_stopped
    (q := q) (W := W) (A₀ := A₀) (cq := GoodPathBounds.cqAt n c₃) (ε := ε) hN hA₀ hq hne hA₀m
    (DriftStopped7.etaAdopted_nonneg (n := n)) (DriftStopped7.r0Adopted_nonneg (n := n))
    hc₃0 hlt (GoodPathBounds.cqAt_nonneg hn hc₃η hc₃0) hε hτ hbdabs k
  have hdrift := drift_bound_at_acc (q := q) (W := W) (A₀ := A₀) (m := K)
    hn hc₃0 hc₃η hA₀ hq hne hA₀m hinterr hS hpre
  have hzero : ∫ ω, stoppedLogDet q W A₀ (ChainSetup.step (D5.S3.Arith.Lattices.Klartag.cAdopted n))
        (DriftStopped6.etaAdopted n) (DriftStopped6.r0Adopted n) c₃
        (ParamsAdopted2.numStepsAdopted2 n) 0 ω
        ∂(ChainSetup.gaussPath (EuclideanSpace ℝ (UT n)))
      = ChainWiring.logDet A₀ := by
    simp only [GoodPathBounds.stoppedLogDet_zero]; simp
  rw [hzero] at hdrift
  have hfail : (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))).real
      (GoodPathBounds.goodCut r (ChainSetup.coord 0)
        (ChainSetup.step (D5.S3.Arith.Lattices.Klartag.cAdopted n)) (6 * r * 1 * Real.sqrt n)
        (ParamsAdopted2.numStepsAdopted2 n) (DriftStopped6.etaAdopted n) q W A₀
        (DriftStopped6.r0Adopted n) c₃ K)ᶜ ≤ GoodPathBounds.failTotal n pcnt := by
    refine le_trans (GoodPathBounds.measureReal_compl_goodCut_le _ _ _ _ _ _ _ _) ?_
    rw [GoodPathBounds.failTotal]
    have h1 := GoodPathBounds.chainGood_failure (n := n) hn3 hr
    have h2 := GoodPathBounds.accGood_failure (q := q) (W := W) (A₀ := A₀) hn3
    linarith [hcnt]
  obtain ⟨ω, hb, hω⟩ := GoodPathVar.exists_mem_of_variance
    (DriftStopped6.measurable_stoppedLogDet hξm hτ K)
    (DriftStopped6.integrable_stoppedLogDet hN hξm hτ hA₀ hq hne hA₀m
      (DriftStopped7.etaAdopted_nonneg (n := n)) (DriftStopped7.r0Adopted_nonneg (n := n))
      hc₃0 hlt K)
    (L := L) (B := driftRHS_acc n A₀ c₃ E S) (s := s)
    hdrift hshort
    (GoodPathBounds.measurableSet_goodCut hξm (ChainSetup.measurable_coord 0) _ _ _ _ _ _ _)
    hfail hLb hbudget
  refine ⟨ω, hω, ?_⟩
  rwa [GoodPathBounds.stoppedLogDet_eq_of_lt_tau
    (GoodPathBounds.lt_tau_of_goodCut hω hKN)] at hb

theorem stateTriple_of_cut_var (hn : 2073600 ≤ n) {c₃ ε E S L b s pcnt r : ℝ} {K : ℕ} (hr : 0 < r)
    (hKN : K < ParamsAdopted2.numStepsAdopted2 n)
    (hc₃0 : 0 ≤ c₃) (hc₃η : c₃ * DriftStopped6.etaAdopted n ≤ 1 / 4)
    (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    (hA₀m : symMat A₀ = a0C n • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hε : 0 ≤ ε)
    (hbdabs : ChainErrBudget.StoppedErrBudget q W A₀
      (ChainSetup.step (D5.S3.Arith.Lattices.Klartag.cAdopted n)) (DriftStopped6.etaAdopted n)
      (DriftStopped6.r0Adopted n) c₃ (ParamsAdopted2.numStepsAdopted2 n) ε)
    (hpre : ∀ ω, ∀ J, J < tau q W A₀ (ChainSetup.step (D5.S3.Arith.Lattices.Klartag.cAdopted n))
        (DriftStopped6.etaAdopted n) (DriftStopped6.r0Adopted n) c₃
        (ParamsAdopted2.numStepsAdopted2 n) ω →
      ∑ k ∈ Finset.range J, ChainWiring.chainErr q W A₀
        (ChainSetup.step (D5.S3.Arith.Lattices.Klartag.cAdopted n)) k ω ≤ E)
    (hS : S ≤ ∑ k ∈ Finset.range K, ∫ ω,
      DriftStopped6.stoppedFreeDim q W A₀ (ChainSetup.step (D5.S3.Arith.Lattices.Klartag.cAdopted n))
        (DriftStopped6.etaAdopted n) (DriftStopped6.r0Adopted n) c₃
        (ParamsAdopted2.numStepsAdopted2 n) k ω
      ∂(ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))))
    (hcnt : (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))).real
        (StateInvariant4.countGood q W A₀ (ChainSetup.step (D5.S3.Arith.Lattices.Klartag.cAdopted n))
          K c₃)ᶜ ≤ pcnt)
    (hshort : ∫ ω, max (L - stoppedLogDet q W A₀
        (ChainSetup.step (D5.S3.Arith.Lattices.Klartag.cAdopted n)) (DriftStopped6.etaAdopted n)
        (DriftStopped6.r0Adopted n) c₃ (ParamsAdopted2.numStepsAdopted2 n) K ω) 0
      ∂(ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))) ≤ s)
    (hLb : L < b)
    (hbudget : (driftRHS_acc n A₀ c₃ E S - L + s) / (b - L)
      + GoodPathBounds.failTotal n pcnt < 1) :
    ∃ (A : EuclideanSpace ℝ (UT n)) (M : ℝ), A ∈ Chain.kSet q W ∧
      Discharge.StateBounds (symMat A) (GoodPathBounds.mAt n c₃) M ∧
      ChainWiring.logDet A ≤ b := by
  obtain ⟨ω, hω, hlog⟩ := goodPathCut_var hn hr hKN hc₃0 hc₃η hA₀ hq hne hA₀m hε hbdabs hpre
    hS hcnt hshort hLb hbudget
  exact ⟨(Chain.chain q W A₀ (ChainSetup.step (D5.S3.Arith.Lattices.Klartag.cAdopted n)) K ω).1,
    GoodPathBounds.MAt n c₃, Chain.chain_fst_mem_kSet hA₀ hq hne K ω,
    GoodPathBounds.stateBounds_goodCut hA₀ hq hne hA₀m
      (DriftStopped7.etaAdopted_nonneg (n := n)) (DriftStopped7.r0Adopted_nonneg (n := n))
      hc₃0 (GoodPathBounds.lt_a0C_of_mAt hn hc₃η) hω hKN, hlog⟩

end Cut

section Supply

open D5.S3.Arith.Lattices.Klartag.Completion.Theorem2R4
open D5.S3.Arith.Lattices.Klartag.State.RawDataInst2
open D5.S3.Arith.Lattices.Klartag.Construction.ConstructionA
open D5.S3.Arith.Lattices.Klartag.Construction.Tiling
open D5.S3.Arith.Lattices.Klartag.Completion.FinalDischarge

end Supply

end D5.S3.Arith.Lattices.Klartag.Contact.CutVariance
