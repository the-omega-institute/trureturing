/- GID: D5/S3/Arith/Lattices/Klartag/Completion/GoodPathBounds
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Completion/GoodPathBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform constants and completion of lattice packing. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Completion.GoodPathCore

open D5.S3.Arith.Lattices.Klartag.Completion
open D5.S3.Arith.Lattices.Klartag.Construction
open D5.S3.Arith.Lattices.Klartag.Contact
open D5.S3.Arith.Lattices.Klartag.Drift
open D5.S3.Arith.Lattices.Klartag.Drift.Stopped
open D5.S3.Arith.Lattices.Klartag.Gaussian
open D5.S3.Arith.Lattices.Klartag.State
open D5.S3.Arith.Lattices.Klartag.Tail
open D5.S3.Arith.Lattices.Klartag.Walk

namespace D5.S3.Arith.Lattices.Klartag.Completion.GoodPathBounds

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
open D5.S3.Arith.Lattices.Klartag.State.StateInvariant
open scoped NNReal RealInnerProductSpace

section GoodPath

open D5.S3.Arith.Lattices.Klartag.Construction.ConstructionA
open D5.S3.Arith.Lattices.Klartag.Construction.Tiling
open D5.S3.Arith.Lattices.Klartag.State.PaddedLawSetupR
open D5.S3.Arith.Lattices.Klartag.State.RawDataInst2R
open D5.S3.Arith.Lattices.Klartag.State.RawDataInst2

variable {p m : ℕ} {α R C' : ℝ} {g : Fin (m + 1) → ZMod p}

end GoodPath

section GoodPathFree

open D5.S3.Arith.Lattices.Klartag.Construction.ConstructionA
open D5.S3.Arith.Lattices.Klartag.Construction.Tiling
open D5.S3.Arith.Lattices.Klartag.State.PaddedLawSetupR
open D5.S3.Arith.Lattices.Klartag.State.RawDataInst2R
open D5.S3.Arith.Lattices.Klartag.State.RawDataInst2

variable {p m : ℕ} {α C' : ℝ} {g : Fin (m + 1) → ZMod p}

end GoodPathFree

section FreeTotal

variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι] {Ω : Type*} [MeasurableSpace Ω]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}
  {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)}

theorem free_ge_of_lt_tau {η r₀ c₃ : ℝ} {N k : ℕ} (ω : Ω)
    (hω : k < tau q W A₀ ξ η r₀ c₃ N ω) :
    (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ) - ((Chain.chain q W A₀ ξ k ω).2.card : ℝ)
      ≤ DriftStopped6.stoppedFreeDim q W A₀ ξ η r₀ c₃ N k ω := by
  have hrep : DriftStopped6.stoppedFreeDim q W A₀ ξ η r₀ c₃ N k ω
      = ((Chain.freeDim q W A₀ ξ k ω : ℕ) : ℝ) := by
    rw [DriftStopped6.stoppedFreeDim_eq, if_pos hω]
  rw [hrep, Chain.freeDim]
  have h := Chain.finrank_freeSub_ge_card q (Chain.chain q W A₀ ξ k ω).2
  have hcast : ((finrank ℝ (EuclideanSpace ℝ (UT n))
      - (Chain.chain q W A₀ ξ k ω).2.card : ℕ) : ℝ)
      ≤ ((finrank ℝ (Chain.freeSub q (Chain.chain q W A₀ ξ k ω).2) : ℕ) : ℝ) := by
    exact_mod_cast h
  have hsub : (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ)
      - ((Chain.chain q W A₀ ξ k ω).2.card : ℝ)
      ≤ ((finrank ℝ (EuclideanSpace ℝ (UT n))
          - (Chain.chain q W A₀ ξ k ω).2.card : ℕ) : ℝ) := by
    by_cases hle : finrank ℝ (EuclideanSpace ℝ (UT n)) ≤ (Chain.chain q W A₀ ξ k ω).2.card
    · rw [Nat.sub_eq_zero_of_le hle]
      have : (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ)
          ≤ ((Chain.chain q W A₀ ξ k ω).2.card : ℝ) := by exact_mod_cast hle
      push_cast
      linarith
    · rw [Nat.cast_sub (by omega : (Chain.chain q W A₀ ξ k ω).2.card
        ≤ finrank ℝ (EuclideanSpace ℝ (UT n)))]
  linarith

variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- **`hS`, derived.**  `GoodPathLight.sum_free_ge_cut` at `Nfun := stoppedFreeDim`,
`Cset := C_k`, `Good k := {k < τ}`, `dd := dim E`, with the contact total rewritten by
`ContactIntegrated.integrated_count_eq` into `(1/h)·∑_{W} intWeight` and bounded by the light
contact. -/
theorem hS_of_intWeight {η r₀ c₃ hstep Θ : ℝ} {N m : ℕ} (hstep0 : 0 < hstep)
    (hξ : ∀ j, Measurable (ξ j)) (hτ : Measurable (tau q W A₀ ξ η r₀ c₃ N))
    (hlight : ∑ x ∈ W, ContactIntegrated.intWeight P
        (fun k ω => (Chain.chain q W A₀ ξ k ω).2) hstep m x ≤ Θ) :
    (m : ℝ) * (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ) - Θ / hstep
        - (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ)
          * ∑ k ∈ Finset.range m, P.real {ω | k < tau q W A₀ ξ η r₀ c₃ N ω}ᶜ
      ≤ ∑ k ∈ Finset.range m, ∫ ω,
          DriftStopped6.stoppedFreeDim q W A₀ ξ η r₀ c₃ N k ω ∂P := by
  classical
  set dd : ℝ := (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ) with hdd
  have hcut := GoodPathLight.sum_free_ge_cut (μ := P)
    (Cset := fun k ω => (Chain.chain q W A₀ ξ k ω).2)
    (Nfun := fun k => DriftStopped6.stoppedFreeDim q W A₀ ξ η r₀ c₃ N k)
    (Good := fun k => {ω | k < tau q W A₀ ξ η r₀ c₃ N ω}) dd m
    (fun k _ ω hω => free_ge_of_lt_tau ω hω)
    (fun k _ ω => by rw [DriftStopped6.stoppedFreeDim]; positivity)
    (by rw [hdd]; positivity)
    (fun k => hτ (measurableSet_Ioi (a := k)))
    (fun k _ => DriftStopped6.integrable_stoppedFreeDim hξ hτ k)
    (fun k _ => StateInvariant4.integrable_card_chain hξ k)
  have hsplit : ∑ k ∈ Finset.range m,
        (dd - ∫ ω, ((Chain.chain q W A₀ ξ k ω).2.card : ℝ) ∂P
          - dd * P.real {ω | k < tau q W A₀ ξ η r₀ c₃ N ω}ᶜ)
      = (m : ℝ) * dd - (∑ k ∈ Finset.range m, ∫ ω, ((Chain.chain q W A₀ ξ k ω).2.card : ℝ) ∂P)
        - dd * ∑ k ∈ Finset.range m, P.real {ω | k < tau q W A₀ ξ η r₀ c₃ N ω}ᶜ := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
      Finset.mul_sum, nsmul_eq_mul]
  rw [hsplit] at hcut
  have hint : ∑ k ∈ Finset.range m,
      hstep * ∫ ω, ((Chain.chain q W A₀ ξ k ω).2.card : ℝ) ∂P
      = ∑ x ∈ W, ContactIntegrated.intWeight P
          (fun k ω => (Chain.chain q W A₀ ξ k ω).2) hstep m x :=
    ContactIntegrated.integrated_count_eq P W _ hstep m
      (fun k ω => Chain.chain_snd_subset_window k ω)
      (fun k x _ => Chain.measurableSet_mem_active hξ k x)
  have hpull : ∑ k ∈ Finset.range m,
      hstep * ∫ ω, ((Chain.chain q W A₀ ξ k ω).2.card : ℝ) ∂P
      = hstep * ∑ k ∈ Finset.range m, ∫ ω, ((Chain.chain q W A₀ ξ k ω).2.card : ℝ) ∂P := by
    rw [Finset.mul_sum]
  have hle : hstep * ∑ k ∈ Finset.range m,
      ∫ ω, ((Chain.chain q W A₀ ξ k ω).2.card : ℝ) ∂P ≤ Θ := by
    rw [← hpull, hint]; exact hlight
  have hdiv : ∑ k ∈ Finset.range m, ∫ ω, ((Chain.chain q W A₀ ξ k ω).2.card : ℝ) ∂P
      ≤ Θ / hstep := by
    rw [le_div_iff₀ hstep0, mul_comm]; exact hle
  linarith

end FreeTotal

section Cut

variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι] {Ω : Type*} [MeasurableSpace Ω]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}
  {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)}

def goodCut (r : ℝ) (Wacc : Ω → EuclideanSpace ℝ (UT n))
    (ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)) (thr : ℝ) (N : ℕ) (η : ℝ)
    (q : ι → EuclideanSpace ℝ (UT n)) (W : Finset ι) (A₀ : EuclideanSpace ℝ (UT n))
    (r₀ c₃ : ℝ) (K : ℕ) : Set Ω :=
  StepGlue.chainGood r Wacc ξ thr N η ∩ StateInvariant.accGood q W A₀ ξ N r₀
    ∩ StateInvariant4.countGood q W A₀ ξ K c₃

theorem measureReal_compl_goodCut_le {P : Measure Ω} [IsProbabilityMeasure P]
    (r : ℝ) (Wacc : Ω → EuclideanSpace ℝ (UT n)) (thr : ℝ) (N : ℕ) (η r₀ c₃ : ℝ) (K : ℕ) :
    P.real (goodCut r Wacc ξ thr N η q W A₀ r₀ c₃ K)ᶜ
      ≤ P.real (StepGlue.chainGood r Wacc ξ thr N η)ᶜ
        + P.real (StateInvariant.accGood q W A₀ ξ N r₀)ᶜ
        + P.real (StateInvariant4.countGood q W A₀ ξ K c₃)ᶜ := by
  have hset : (goodCut r Wacc ξ thr N η q W A₀ r₀ c₃ K)ᶜ
      = ((StepGlue.chainGood r Wacc ξ thr N η)ᶜ
          ∪ (StateInvariant.accGood q W A₀ ξ N r₀)ᶜ)
        ∪ (StateInvariant4.countGood q W A₀ ξ K c₃)ᶜ := by
    rw [goodCut, Set.compl_inter, Set.compl_inter]
  rw [hset]
  refine le_trans (measureReal_union_le _ _) ?_
  have := measureReal_union_le (μ := P) (StepGlue.chainGood r Wacc ξ thr N η)ᶜ
    (StateInvariant.accGood q W A₀ ξ N r₀)ᶜ
  linarith

theorem measurableSet_goodCut (hξ : ∀ j, Measurable (ξ j))
    {Wacc : Ω → EuclideanSpace ℝ (UT n)} (hW : Measurable Wacc) (r thr : ℝ) (N : ℕ)
    (η r₀ c₃ : ℝ) (K : ℕ) :
    MeasurableSet (goodCut r Wacc ξ thr N η q W A₀ r₀ c₃ K) :=
  ((measurableSet_goodEventUT hW r thr).inter (measurableSet_stepGood hξ N η)).inter
    (measurableSet_accGood hξ N r₀) |>.inter (measurableSet_countGood hξ K c₃)

/-- On `goodCut` the state conditions hold at **every** index up to `K`. -/
theorem stateGood_of_goodCut {r : ℝ} {Wacc : Ω → EuclideanSpace ℝ (UT n)} {thr : ℝ} {N : ℕ}
    {η r₀ c₃ : ℝ} {K : ℕ} {ω : Ω} (hω : ω ∈ goodCut r Wacc ξ thr N η q W A₀ r₀ c₃ K)
    (hKN : K < N) {j : ℕ} (hj : j ≤ K) :
    ω ∈ stateGood q W A₀ ξ η r₀ c₃ j :=
  ⟨fun i hi => hω.1.1.2 i (by omega), hω.1.2 j (by omega),
    StateInvariant4.card_le_of_countGood hω.2 hj⟩

/-- Hence the stopping time has not fired by `K`. -/
theorem lt_tau_of_goodCut {r : ℝ} {Wacc : Ω → EuclideanSpace ℝ (UT n)} {thr : ℝ} {N : ℕ}
    {η r₀ c₃ : ℝ} {K : ℕ} {ω : Ω} (hω : ω ∈ goodCut r Wacc ξ thr N η q W A₀ r₀ c₃ K)
    (hKN : K < N) : K < tau q W A₀ ξ η r₀ c₃ N ω := by
  by_contra hcon
  push Not at hcon
  rcases tauOf_le_iff.1 hcon with ⟨j, hjK, hjN, hmem⟩ | hNK
  · exact hmem (stateGood_of_goodCut hω hKN hjK)
  · omega

/-- **`StateBounds` at index `K` on `goodCut`** — `StateInvariant4.stateBounds_wired'`'s proof with
the count taken at `K` directly instead of transported from `N`. -/
theorem stateBounds_goodCut {r : ℝ} {Wacc : Ω → EuclideanSpace ℝ (UT n)} {thr : ℝ} {N : ℕ}
    {η a₀ r₀ c₃ : ℝ} {K : ℕ} {ω : Ω}
    (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    (hA₀m : symMat A₀ = a₀ • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hη : 0 ≤ η) (hr₀ : 0 ≤ r₀) (hc₃ : 0 ≤ c₃) (hlt : r₀ + c₃ * η < a₀)
    (hω : ω ∈ goodCut r Wacc ξ thr N η q W A₀ r₀ c₃ K) (hKN : K < N) :
    Discharge.StateBounds (symMat (Chain.chain q W A₀ ξ K ω).1)
      (a₀ - (r₀ + c₃ * η)) (a₀ + (r₀ + c₃ * η)) := by
  have hstep : ∀ j, j < K → ‖StateInvariant.gaussStep q W A₀ ξ j ω‖ ≤ η := fun j hj =>
    le_trans (Submodule.norm_starProjection_apply_le _ _) (hω.1.1.2 j (by omega))
  have hlift : ‖StateInvariant.liftSum q W A₀ ξ K ω‖ ≤ c₃ * η := by
    refine le_trans (LiftBound.norm_liftSum_le_card hA₀ hq hne hη K ω hstep) ?_
    exact mul_le_mul_of_nonneg_right hω.2 hη
  exact LiftBound.stateBounds_of_chain_count hA₀ hq hne hA₀m hr₀ (by positivity)
    (hω.1.2 K hKN) hlift hlt

theorem stoppedLogDet_eq_of_lt_tau {η r₀ c₃ : ℝ} {N k : ℕ} {ω : Ω}
    (hlt : k < tau q W A₀ ξ η r₀ c₃ N ω) :
    stoppedLogDet q W A₀ ξ η r₀ c₃ N k ω
      = ChainWiring.logDet (Chain.chain q W A₀ ξ k ω).1 := by
  rw [stoppedLogDet, stoppedState, min_eq_left (by omega)]

end Cut

section CutAssembly

variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}

end CutAssembly

end D5.S3.Arith.Lattices.Klartag.Completion.GoodPathBounds
