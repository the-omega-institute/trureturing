/- GID: D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftInputsStopped
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftInputsStopped
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Stopped log determinant drift and integrability estimates. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Drift.Stopped.DriftStopped6
import D5.S3.Arith.Lattices.Klartag.Drift.Stopped.DriftStopped2
import D5.S3.Arith.Lattices.Klartag.Gaussian.GaussianMaximal3
import D5.S3.Arith.Lattices.Klartag.Drift.Stopped.DriftStopped7

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open D5.S3.Arith.Lattices.Klartag.Completion
open D5.S3.Arith.Lattices.Klartag.Construction
open D5.S3.Arith.Lattices.Klartag.Contact
open D5.S3.Arith.Lattices.Klartag.Drift
open D5.S3.Arith.Lattices.Klartag.Drift.Stopped
open D5.S3.Arith.Lattices.Klartag.Gaussian
open D5.S3.Arith.Lattices.Klartag.State
open D5.S3.Arith.Lattices.Klartag.Tail
open D5.S3.Arith.Lattices.Klartag.Walk

namespace D5.S3.Arith.Lattices.Klartag.Drift.Stopped.DriftInputsStopped

open MeasureTheory
open Matrix
open Finset
open Module
open D5.S3.Arith.Lattices.Klartag
open D5.S3.Arith.Lattices.Klartag.Walk.Increments
open D5.S3.Arith.Lattices.Klartag.Walk.StoppedChain
open D5.S3.Arith.Lattices.Klartag.Drift.Stopped.DriftStopped
open D5.S3.Arith.Lattices.Klartag.Drift.Stopped.DriftStopped5
open scoped NNReal RealInnerProductSpace

theorem measurable_ringInverse : Measurable (Ring.inverse : ℝ → ℝ) := by
  have h : (Ring.inverse : ℝ → ℝ) = fun x => x⁻¹ := by
    funext x; exact Ring.inverse_eq_inv x
  rw [h]; exact measurable_inv

theorem measurable_matInv_entry {N : ℕ} {α : Type*} (mα : MeasurableSpace α)
    {f : α → Matrix (Fin N) (Fin N) ℝ}
    (hf : ∀ i j, Measurable[mα] fun a => f a i j) (i j : Fin N) :
    Measurable[mα] fun a => ((f a)⁻¹) i j := by
  letI : MeasurableSpace α := mα
  have hdet : Measurable fun a => (f a).det := by
    simp only [Matrix.det_apply]
    refine Finset.measurable_sum _ fun σ _ => ?_
    exact (Finset.measurable_prod _ fun i _ => hf (σ i) i).const_smul _
  have hadj : Measurable fun a => (f a).adjugate i j := by
    simp only [Matrix.adjugate_apply, Matrix.det_apply]
    refine Finset.measurable_sum _ fun σ _ => ?_
    refine Measurable.const_smul ?_ _
    refine Finset.measurable_prod _ fun r _ => ?_
    simp only [Matrix.updateRow_apply]
    exact Measurable.ite (MeasurableSet.const _) measurable_const (hf (σ r) r)
  have h : (fun a => ((f a)⁻¹) i j)
      = fun a => Ring.inverse (f a).det * (f a).adjugate i j := by
    funext a; rw [Matrix.inv_def]; simp
  rw [h]
  exact (measurable_ringInverse.comp hdet).mul hadj

section Coords

/-- A map into `EuclideanSpace` is measurable as soon as every coordinate is. -/
theorem measurable_toLp_of_coords {Ω' : Type*} (mΩ : MeasurableSpace Ω') {κ : Type*} [Fintype κ]
    {g : Ω' → κ → ℝ} (hg : ∀ p, Measurable[mΩ] fun ω => g ω p) :
    Measurable[mΩ] fun ω => (WithLp.toLp 2 (g ω) : EuclideanSpace ℝ κ) := by
  letI : MeasurableSpace Ω' := mΩ
  exact (WithLp.measurable_toLp 2 (κ → ℝ)).comp (measurable_pi_iff.mpr hg)

end Coords

section Adapted

variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι] {Ω : Type*} [m0 : MeasurableSpace Ω]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}
  {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)}

attribute [local instance] D5.S3.Arith.Lattices.Klartag.Walk.Chain.instMeasurableSpaceFinset
attribute [local instance] D5.S3.Arith.Lattices.Klartag.Walk.Chain.instMeasurableSingletonFinset

theorem measurable_chain_fil (ℱ : Filtration ℕ m0)
    (hξa : ∀ j, Measurable[ℱ (j + 1)] (ξ j)) (k : ℕ) :
    Measurable[ℱ k] fun ω => Chain.chain q W A₀ ξ k ω :=
  Chain.measurable_chain (m := ⇑ℱ) ℱ.mono' hξa k

theorem measurable_chain_fst_fil (ℱ : Filtration ℕ m0)
    (hξa : ∀ j, Measurable[ℱ (j + 1)] (ξ j)) (k : ℕ) :
    Measurable[ℱ k] fun ω => (Chain.chain q W A₀ ξ k ω).1 :=
  measurable_fst.comp (measurable_chain_fil ℱ hξa k)

theorem measurableSet_active_eq_fil (ℱ : Filtration ℕ m0)
    (hξa : ∀ j, Measurable[ℱ (j + 1)] (ξ j)) (k : ℕ) (c : Finset ι) :
    MeasurableSet[ℱ k] {ω | (Chain.chain q W A₀ ξ k ω).2 = c} := by
  have h : Measurable[ℱ k] fun ω => (Chain.chain q W A₀ ξ k ω).2 :=
    measurable_snd.comp (measurable_chain_fil ℱ hξa k)
  exact h (measurableSet_singleton c)

/-- Entries of `symMat A_k` are `ℱ k`-measurable. -/
theorem measurable_symMat_chain_entry (ℱ : Filtration ℕ m0)
    (hξa : ∀ j, Measurable[ℱ (j + 1)] (ξ j)) (k : ℕ) (i j : Fin n) :
    Measurable[ℱ k] fun ω => symMat (Chain.chain q W A₀ ξ k ω).1 i j := by
  simp only [symMat_apply]
  exact Measurable.const_mul
    (((PiLp.continuous_apply 2 (fun _ : UT n => ℝ) (up i j)).measurable).comp
      (measurable_chain_fst_fil ℱ hξa k)) _

/-- `V`'s raw value `matToUT (symMat A_k)⁻¹` is `ℱ k`-measurable. -/
theorem measurable_matToUT_inv_chain (ℱ : Filtration ℕ m0)
    (hξa : ∀ j, Measurable[ℱ (j + 1)] (ξ j)) (k : ℕ) :
    Measurable[ℱ k] fun ω =>
      Discharge.matToUT (symMat (Chain.chain q W A₀ ξ k ω).1)⁻¹ := by
  have hrep : (fun ω => Discharge.matToUT (symMat (Chain.chain q W A₀ ξ k ω).1)⁻¹)
      = fun ω => (WithLp.toLp 2 (fun p : UT n =>
          ((symMat (Chain.chain q W A₀ ξ k ω).1)⁻¹) p.1.1 p.1.2 / cc p)) := rfl
  rw [hrep]
  exact measurable_toLp_of_coords (ℱ k)
    (fun p => (measurable_matInv_entry (ℱ k) (measurable_symMat_chain_entry ℱ hξa k)
      p.1.1 p.1.2).div_const _)

/-- `{τ ≤ j}` is `ℱ j`-measurable. -/
theorem measurableSet_tau_le (ℱ : Filtration ℕ m0) {η r₀ c₃ : ℝ}
    (hG : ∀ k, MeasurableSet[ℱ k] (stateGood q W A₀ ξ η r₀ c₃ k)) (N j : ℕ) :
    MeasurableSet[ℱ j] {ω | tau q W A₀ ξ η r₀ c₃ N ω ≤ j} := by
  have h := isStoppingTime_tau ℱ hG N j
  simpa using h

/-- `{k < τ}` is `ℱ k`-measurable — this is the cut `stoppedV` and `stoppedSub` are taken at. -/
theorem measurableSet_lt_tau (ℱ : Filtration ℕ m0) {η r₀ c₃ : ℝ}
    (hG : ∀ k, MeasurableSet[ℱ k] (stateGood q W A₀ ξ η r₀ c₃ k)) (N k : ℕ) :
    MeasurableSet[ℱ k] {ω | k < tau q W A₀ ξ η r₀ c₃ N ω} := by
  have h := (measurableSet_tau_le ℱ hG N k).compl
  have hset : {ω | tau q W A₀ ξ η r₀ c₃ N ω ≤ k}ᶜ
      = {ω | k < tau q W A₀ ξ η r₀ c₃ N ω} := by
    ext ω; simp [Set.mem_compl_iff, not_le]
  rwa [hset] at h

/-- The fibres of the freeze index `min k (τ − 1)` are `ℱ k`-measurable. -/
theorem measurableSet_freezeIdx_eq (ℱ : Filtration ℕ m0) {η r₀ c₃ : ℝ}
    (hG : ∀ k, MeasurableSet[ℱ k] (stateGood q W A₀ ξ η r₀ c₃ k)) {N : ℕ} (hN : 1 ≤ N)
    (hr₀ : 0 ≤ r₀) (hc₃ : 0 ≤ c₃) (k j : ℕ) :
    MeasurableSet[ℱ k] {ω | min k (tau q W A₀ ξ η r₀ c₃ N ω - 1) = j} := by
  classical
  have hone : ∀ ω, 1 ≤ tau q W A₀ ξ η r₀ c₃ N ω := fun ω => one_le_tau hN hr₀ hc₃ ω
  rcases lt_trichotomy j k with hjk | hjk | hjk
  · have hset : {ω | min k (tau q W A₀ ξ η r₀ c₃ N ω - 1) = j}
        = {ω | tau q W A₀ ξ η r₀ c₃ N ω ≤ j + 1} \ {ω | tau q W A₀ ξ η r₀ c₃ N ω ≤ j} := by
      ext ω
      have := hone ω
      simp only [Set.mem_ofPred_eq, Set.mem_sdiff]
      omega
    rw [hset]
    exact (ℱ.mono (by omega : j + 1 ≤ k) _ (measurableSet_tau_le ℱ hG N (j + 1))).diff
      (ℱ.mono (by omega : j ≤ k) _ (measurableSet_tau_le ℱ hG N j))
  · subst hjk
    have hset : {ω | min j (tau q W A₀ ξ η r₀ c₃ N ω - 1) = j}
        = {ω | tau q W A₀ ξ η r₀ c₃ N ω ≤ j}ᶜ ∪ (if j = 0 then Set.univ else ∅) := by
      ext ω
      have := hone ω
      by_cases hj : j = 0
      · subst hj; simp
      · rw [if_neg hj]
        simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_compl_iff, Set.mem_empty_iff_false,
          or_false]
        omega
    rw [hset]
    refine MeasurableSet.union (measurableSet_tau_le ℱ hG N j).compl ?_
    by_cases hj : j = 0
    · rw [if_pos hj]; exact @MeasurableSet.univ Ω (ℱ j)
    · rw [if_neg hj]; exact @MeasurableSet.empty Ω (ℱ j)
  · have hset : {ω | min k (tau q W A₀ ξ η r₀ c₃ N ω - 1) = j} = (∅ : Set Ω) := by
      ext ω; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]; omega
    rw [hset]
    exact @MeasurableSet.empty Ω (ℱ k)

/-- **`hVm`**: each coordinate of the stopped `V` is `ℱ k`-measurable. -/
theorem stronglyMeasurable_stoppedV_coord (ℱ : Filtration ℕ m0)
    (hξa : ∀ j, Measurable[ℱ (j + 1)] (ξ j)) {η r₀ c₃ : ℝ}
    (hG : ∀ k, MeasurableSet[ℱ k] (stateGood q W A₀ ξ η r₀ c₃ k)) (N k : ℕ) (p : UT n) :
    StronglyMeasurable[ℱ k] fun ω => stoppedV q W A₀ ξ η r₀ c₃ N k ω p := by
  classical
  have hlt : MeasurableSet[ℱ k] {ω | k < tau q W A₀ ξ η r₀ c₃ N ω} :=
    measurableSet_lt_tau ℱ hG N k
  have hact : ∀ c : Finset ι, MeasurableSet[ℱ k] {ω | (Chain.chain q W A₀ ξ k ω).2 = c} :=
    fun c => measurableSet_active_eq_fil ℱ hξa k c
  have hinv : Measurable[ℱ k] fun ω =>
      Discharge.matToUT (symMat (Chain.chain q W A₀ ξ k ω).1)⁻¹ :=
    measurable_matToUT_inv_chain ℱ hξa k
  have hrep : (fun ω => stoppedV q W A₀ ξ η r₀ c₃ N k ω p)
      = fun ω => if k < tau q W A₀ ξ η r₀ c₃ N ω then
          (∑ c ∈ W.powerset, if (Chain.chain q W A₀ ξ k ω).2 = c then
            ((Chain.freeSub q c).starProjection
              (Discharge.matToUT (symMat (Chain.chain q W A₀ ξ k ω).1)⁻¹)) p else 0)
        else 0 := by
    funext ω
    by_cases h : k < tau q W A₀ ξ η r₀ c₃ N ω
    · rw [stoppedV, if_pos h, if_pos h,
        Finset.sum_ite_eq W.powerset (Chain.chain q W A₀ ξ k ω).2
          (fun c => ((Chain.freeSub q c).starProjection
            (Discharge.matToUT (symMat (Chain.chain q W A₀ ξ k ω).1)⁻¹)) p),
        if_pos (Finset.mem_powerset.2 (Chain.chain_snd_subset_window k ω))]
    · rw [stoppedV, if_neg h, if_neg h]
      simp
  letI : MeasurableSpace Ω := ℱ k
  refine Measurable.stronglyMeasurable ?_
  rw [hrep]
  refine Measurable.ite hlt ?_ measurable_const
  refine Finset.measurable_sum _ fun c _ => ?_
  refine Measurable.ite (hact c) ?_ measurable_const
  exact ((PiLp.continuous_apply 2 (fun _ : UT n => ℝ) p).measurable.comp
    (Chain.freeSub q c).starProjection.continuous.measurable).comp hinv

/-- **`hKm`**: the projection matrix of the stopped free subspace is `ℱ k`-measurable, entrywise. -/
theorem stronglyMeasurable_stoppedSub_coeff (ℱ : Filtration ℕ m0)
    (hξa : ∀ j, Measurable[ℱ (j + 1)] (ξ j)) {η r₀ c₃ : ℝ}
    (hG : ∀ k, MeasurableSet[ℱ k] (stateGood q W A₀ ξ η r₀ c₃ k)) (N k : ℕ) (p p' : UT n) :
    StronglyMeasurable[ℱ k] fun ω =>
      ((stoppedSub q W A₀ ξ η r₀ c₃ N k ω).starProjection
        (EuclideanSpace.single p (1 : ℝ))) p' := by
  classical
  have hlt : MeasurableSet[ℱ k] {ω | k < tau q W A₀ ξ η r₀ c₃ N ω} :=
    measurableSet_lt_tau ℱ hG N k
  have hact : ∀ c : Finset ι, MeasurableSet[ℱ k] {ω | (Chain.chain q W A₀ ξ k ω).2 = c} :=
    fun c => measurableSet_active_eq_fil ℱ hξa k c
  have hrep : (fun ω => ((stoppedSub q W A₀ ξ η r₀ c₃ N k ω).starProjection
        (EuclideanSpace.single p (1 : ℝ))) p')
      = fun ω => if k < tau q W A₀ ξ η r₀ c₃ N ω then
          (∑ c ∈ W.powerset, if (Chain.chain q W A₀ ξ k ω).2 = c then
            ((Chain.freeSub q c).starProjection (EuclideanSpace.single p (1 : ℝ))) p' else 0)
        else 0 := by
    funext ω
    by_cases h : k < tau q W A₀ ξ η r₀ c₃ N ω
    · rw [stoppedSub, if_pos h, if_pos h,
        Finset.sum_ite_eq W.powerset (Chain.chain q W A₀ ξ k ω).2
          (fun c => ((Chain.freeSub q c).starProjection
            (EuclideanSpace.single p (1 : ℝ))) p'),
        if_pos (Finset.mem_powerset.2 (Chain.chain_snd_subset_window k ω))]
    · rw [stoppedSub, if_neg h, if_neg h, Submodule.starProjection_bot]
      simp
  letI : MeasurableSpace Ω := ℱ k
  refine Measurable.stronglyMeasurable ?_
  rw [hrep]
  refine Measurable.ite hlt ?_ measurable_const
  refine Finset.measurable_sum _ fun c _ => ?_
  exact Measurable.ite (hact c) measurable_const measurable_const

/-- **`hDm`**: the stopped log-determinant is `ℱ k`-measurable.  `min k (τ − 1)` lands in
`{0, …, k}` and the chain is adapted, so this is a finite sum of `ℱ k`-branches. -/
theorem stronglyMeasurable_stoppedLogDet (ℱ : Filtration ℕ m0)
    (hξa : ∀ j, Measurable[ℱ (j + 1)] (ξ j)) {η r₀ c₃ : ℝ}
    (hG : ∀ k, MeasurableSet[ℱ k] (stateGood q W A₀ ξ η r₀ c₃ k)) {N : ℕ} (hN : 1 ≤ N)
    (hr₀ : 0 ≤ r₀) (hc₃ : 0 ≤ c₃) (k : ℕ) :
    StronglyMeasurable[ℱ k] (stoppedLogDet q W A₀ ξ η r₀ c₃ N k) := by
  classical
  have hfib : ∀ j, MeasurableSet[ℱ k] {ω | min k (tau q W A₀ ξ η r₀ c₃ N ω - 1) = j} :=
    fun j => measurableSet_freezeIdx_eq ℱ hG hN hr₀ hc₃ k j
  have hlog : ∀ j, j ≤ k →
      Measurable[ℱ k] fun ω => ChainWiring.logDet (Chain.chain q W A₀ ξ j ω).1 := by
    intro j hjk
    have hj' : Measurable[ℱ j] fun ω => ChainWiring.logDet (Chain.chain q W A₀ ξ j ω).1 :=
      Real.measurable_log.comp
        ((DriftStopped6.continuous_symMat_det (n := n)).measurable.comp
          (measurable_chain_fst_fil ℱ hξa j))
    exact hj'.mono (ℱ.mono hjk) le_rfl
  have hrep : stoppedLogDet q W A₀ ξ η r₀ c₃ N k
      = fun ω => ∑ j ∈ Finset.range (k + 1),
          if min k (tau q W A₀ ξ η r₀ c₃ N ω - 1) = j
            then ChainWiring.logDet (Chain.chain q W A₀ ξ j ω).1 else 0 := by
    funext ω
    rw [Finset.sum_ite_eq (Finset.range (k + 1)) (min k (tau q W A₀ ξ η r₀ c₃ N ω - 1))
      (fun j => ChainWiring.logDet (Chain.chain q W A₀ ξ j ω).1),
      if_pos (Finset.mem_range.2 (by omega))]
    rfl
  letI : MeasurableSpace Ω := ℱ k
  refine Measurable.stronglyMeasurable ?_
  rw [hrep]
  refine Finset.measurable_sum _ fun j hj => ?_
  exact Measurable.ite (hfib j) (hlog j (by have := Finset.mem_range.1 hj; omega))
    measurable_const

theorem measurable_gaussStep_fil (ℱ : Filtration ℕ m0)
    (hξa : ∀ j, Measurable[ℱ (j + 1)] (ξ j)) (j : ℕ) :
    Measurable[ℱ (j + 1)] (StateInvariant.gaussStep q W A₀ ξ j) := by
  classical
  have hact : ∀ c : Finset ι, MeasurableSet[ℱ (j + 1)] {ω | (Chain.chain q W A₀ ξ j ω).2 = c} :=
    fun c => ℱ.mono (Nat.le_succ j) _ (measurableSet_active_eq_fil ℱ hξa j c)
  have hξj : Measurable[ℱ (j + 1)] (ξ j) := hξa j
  have hrep : StateInvariant.gaussStep q W A₀ ξ j
      = fun ω => ∑ c ∈ W.powerset,
          if (Chain.chain q W A₀ ξ j ω).2 = c
            then (Chain.freeSub q c).starProjection (ξ j ω) else 0 := by
    funext ω
    rw [StateInvariant.gaussStep,
      Finset.sum_ite_eq W.powerset (Chain.chain q W A₀ ξ j ω).2
        (fun c => (Chain.freeSub q c).starProjection (ξ j ω)),
      if_pos (Finset.mem_powerset.2 (Chain.chain_snd_subset_window j ω))]
  letI : MeasurableSpace Ω := ℱ (j + 1)
  rw [hrep]
  refine Finset.measurable_sum _ fun c _ => ?_
  exact Measurable.ite (hact c)
    ((Chain.freeSub q c).starProjection.continuous.measurable.comp hξj) measurable_const

theorem measurable_gaussSum_fil (ℱ : Filtration ℕ m0)
    (hξa : ∀ j, Measurable[ℱ (j + 1)] (ξ j)) (k : ℕ) :
    Measurable[ℱ k] (StateInvariant.gaussSum q W A₀ ξ k) := by
  have hstep : ∀ j, j < k → Measurable[ℱ k] (StateInvariant.gaussStep q W A₀ ξ j) :=
    fun j hj => (measurable_gaussStep_fil ℱ hξa j).mono (ℱ.mono (by omega)) le_rfl
  letI : MeasurableSpace Ω := ℱ k
  show Measurable fun ω => ∑ j ∈ Finset.range k, StateInvariant.gaussStep q W A₀ ξ j ω
  exact Finset.measurable_sum _ fun j hj => hstep j (Finset.mem_range.1 hj)

/-- **`hG`, the hypothesis every stopped-chain theorem carries and nobody proves.** -/
theorem measurableSet_stateGood_fil (ℱ : Filtration ℕ m0)
    (hξa : ∀ j, Measurable[ℱ (j + 1)] (ξ j)) {η r₀ c₃ : ℝ} (k : ℕ) :
    MeasurableSet[ℱ k] (stateGood q W A₀ ξ η r₀ c₃ k) := by
  classical
  have hacc : Measurable[ℱ k] fun ω =>
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (symMat (StateInvariant.gaussSum q W A₀ ξ k ω))‖ := by
    have hmk : (fun ω =>
        ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (symMat (StateInvariant.gaussSum q W A₀ ξ k ω))‖)
        = fun ω => ‖Matrix.toEuclideanCLM (𝕜 := ℝ)
            (mkMat (coordVec 1 (StateInvariant.gaussSum q W A₀ ξ k ω)))‖ := by
      funext ω
      rw [← smul_symMat_eq_mkMat 1 (StateInvariant.gaussSum q W A₀ ξ k ω), one_smul]
    rw [hmk]
    exact (measurable_opNorm_mkMat (n := n)).comp
      ((measurable_coordVec (n := n) 1).comp (measurable_gaussSum_fil ℱ hξa k))
  have hcard : Measurable[ℱ k] fun ω => ((Chain.chain q W A₀ ξ k ω).2.card : ℝ) :=
    (measurable_from_top (f := fun c : Finset ι => (c.card : ℝ))).comp
      (measurable_snd.comp (measurable_chain_fil ℱ hξa k))
  have hstep : ∀ j, j < k → MeasurableSet[ℱ k] {ω | ‖ξ j ω‖ ≤ η} := by
    intro j hj
    have h : MeasurableSet[ℱ (j + 1)] {ω | ‖ξ j ω‖ ≤ η} := by
      letI : MeasurableSpace Ω := ℱ (j + 1)
      exact measurableSet_le (hξa j).norm measurable_const
    exact ℱ.mono (by omega) _ h
  have hrep : stateGood q W A₀ ξ η r₀ c₃ k
      = (⋂ j ∈ {j : ℕ | j < k}, {ω | ‖ξ j ω‖ ≤ η})
        ∩ ({ω | ‖Matrix.toEuclideanCLM (𝕜 := ℝ)
              (symMat (StateInvariant.gaussSum q W A₀ ξ k ω))‖ ≤ r₀}
          ∩ {ω | ((Chain.chain q W A₀ ξ k ω).2.card : ℝ) ≤ c₃}) := by
    ext ω
    simp only [stateGood, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [hrep]
  refine MeasurableSet.inter ?_ (MeasurableSet.inter ?_ ?_)
  · exact MeasurableSet.biInter (Set.to_countable _) fun j hj => hstep j hj
  · exact measurableSet_le hacc measurable_const
  · exact measurableSet_le hcard measurable_const

end Adapted

section CondStep

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

theorem condExp_step_le_cond {ℱ : MeasurableSpace Ω} (hℱ : ℱ ≤ m0) [SigmaFinite (μ.trim hℱ)]
    {Dk Dk1 Nk errk tr quad : Ω → ℝ} {κ : ℝ}
    (hpt : ∀ᵐ ω ∂μ, Dk1 ω ≤ Dk ω + tr ω - quad ω + errk ω)
    (hDkm : StronglyMeasurable[ℱ] Dk)
    (iDk1 : Integrable Dk1 μ) (iDk : Integrable Dk μ) (itr : Integrable tr μ)
    (iquad : Integrable quad μ) (ierr : Integrable errk μ)
    (h2 : μ[tr|ℱ] =ᵐ[μ] 0)
    (h3 : μ[quad|ℱ] =ᵐ[μ] fun ω => κ * Nk ω) :
    μ[Dk1|ℱ] ≤ᵐ[μ] fun ω => Dk ω - κ * Nk ω + (μ[errk|ℱ]) ω := by
  have iSum : Integrable (fun ω => Dk ω + tr ω - quad ω + errk ω) μ :=
    ((iDk.add itr).sub iquad).add ierr
  have hmono := condExp_mono (m := ℱ) iDk1 iSum hpt
  have hexp : μ[fun ω => Dk ω + tr ω - quad ω + errk ω|ℱ]
      =ᵐ[μ] fun ω => Dk ω - κ * Nk ω + (μ[errk|ℱ]) ω := by
    have e1 : μ[fun ω => Dk ω + tr ω - quad ω + errk ω|ℱ]
        =ᵐ[μ] μ[fun ω => Dk ω + tr ω - quad ω|ℱ] + μ[errk|ℱ] :=
      condExp_add ((iDk.add itr).sub iquad) ierr ℱ
    have e2 : μ[fun ω => Dk ω + tr ω - quad ω|ℱ]
        =ᵐ[μ] μ[fun ω => Dk ω + tr ω|ℱ] - μ[quad|ℱ] :=
      condExp_sub (iDk.add itr) iquad ℱ
    have e3 : μ[fun ω => Dk ω + tr ω|ℱ] =ᵐ[μ] μ[Dk|ℱ] + μ[tr|ℱ] := condExp_add iDk itr ℱ
    have hD : μ[Dk|ℱ] = Dk := condExp_of_stronglyMeasurable hℱ hDkm iDk
    filter_upwards [e1, e2, e3, h2, h3] with ω a1 a2 a3 a2' a3'
    simp only [Pi.add_apply, Pi.sub_apply] at a1 a2 a3
    rw [a1, a2, a3, hD]
    simp only [Pi.zero_apply] at a2' ⊢
    rw [a2', a3']
    ring
  filter_upwards [hmono, hexp] with ω hm he
  rw [← he]
  exact hm

end CondStep

section Path

variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}

/-- **The increment is adapted**: `ξ_j = c • coord j` is `natFil (j+1)`-measurable. -/
theorem measurable_step_natFil (c : ℝ) (j : ℕ) :
    Measurable[ChainSetup.natFil (F := EuclideanSpace ℝ (UT n)) (j + 1)]
      (ChainSetup.step (ι := UT n) c j) :=
  (ChainSetup.measurable_coord_natFil j).const_smul c

/-- **`hG` on the path space**, for the chain's own increment: no longer a hypothesis. -/
theorem measurableSet_stateGood_step (cstep η r₀ c₃ : ℝ) (k : ℕ) :
    MeasurableSet[ChainSetup.filtration (F := EuclideanSpace ℝ (UT n)) k]
      (stateGood q W A₀ (ChainSetup.step cstep) η r₀ c₃ k) :=
  measurableSet_stateGood_fil _ (fun j => measurable_step_natFil cstep j) k

/-- Each coordinate of the stopped `V` inherits `DriftStopped2.norm_stoppedV_le`'s bound. -/
theorem abs_stoppedV_coord_le {Ω : Type*} [MeasurableSpace Ω]
    {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)} {η a₀ r₀ c₃ : ℝ} {N : ℕ} (hN : 1 ≤ N)
    (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    (hA₀m : symMat A₀ = a₀ • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hη : 0 ≤ η) (hr₀ : 0 ≤ r₀) (hc₃ : 0 ≤ c₃) (hlt : r₀ + c₃ * η < a₀)
    (k : ℕ) (ω : Ω) (p : UT n) :
    ‖stoppedV q W A₀ ξ η r₀ c₃ N k ω p‖ ≤ Real.sqrt n / (a₀ - (r₀ + c₃ * η)) :=
  le_trans (ChainSetup.norm_coord_le _ p)
    (DriftStopped2.norm_stoppedV_le hN hA₀ hq hne hA₀m hη hr₀ hc₃ hlt k ω)

/-- **The `step` field of `ChainDrift.DriftInputs` for the stopped chain.**  `hpt_stopped` is the
pointwise inequality; H2 (`StepInputs2.condExp_inner_eq_zero`) kills `⟪V_k, ξ_k⟫`; H3
(`StepInputs2.condExp_norm_starProjection_sq`) turns the quadratic term into
`c·v·dim K_k = (c·cstep²)·stoppedFreeDim`; and `condExp_step_le_cond` puts `errCond` — the
conditional representative — in the conclusion. -/
theorem driftInputs_step_stopped {cstep η a₀ r₀ c₃ δ cq : ℝ} {N : ℕ}
    (hN : 1 ≤ N) (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    (hA₀m : symMat A₀ = a₀ • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hη : 0 ≤ η) (hr₀ : 0 ≤ r₀) (hc₃ : 0 ≤ c₃) (hlt : r₀ + c₃ * η < a₀)
    (hδ : η / (a₀ - (r₀ + c₃ * η)) ≤ δ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hcq : cq = 1 / (2 * (a₀ + (r₀ + c₃ * η)) ^ 2 * (1 + δ) ^ 2))
    (hinterr : ∀ k, Integrable
      (stoppedErr q W A₀ (ChainSetup.step cstep) η r₀ c₃ cq N k)
      (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))))
    (k : ℕ) :
    (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n)))[
        stoppedLogDet q W A₀ (ChainSetup.step cstep) η r₀ c₃ N (k + 1)
        | ChainSetup.filtration (F := EuclideanSpace ℝ (UT n)) k]
      ≤ᵐ[ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))] fun ω =>
        stoppedLogDet q W A₀ (ChainSetup.step cstep) η r₀ c₃ N k ω
          - (cq * cstep ^ 2)
              * DriftStopped6.stoppedFreeDim q W A₀ (ChainSetup.step cstep) η r₀ c₃ N k ω
          + errCond (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n)))
              (⇑(ChainSetup.filtration (F := EuclideanSpace ℝ (UT n))))
              q W A₀ (ChainSetup.step cstep) η r₀ c₃ cq N k ω := by
  classical
  subst hcq
  have hG : ∀ k, MeasurableSet[ChainSetup.filtration (F := EuclideanSpace ℝ (UT n)) k]
      (stateGood q W A₀ (ChainSetup.step cstep) η r₀ c₃ k) :=
    fun k => measurableSet_stateGood_step cstep η r₀ c₃ k
  have hξa : ∀ j, Measurable[ChainSetup.filtration (F := EuclideanSpace ℝ (UT n)) (j + 1)]
      (ChainSetup.step (ι := UT n) cstep j) := fun j => measurable_step_natFil cstep j
  have hξm : ∀ j, Measurable (ChainSetup.step (ι := UT n) cstep j) :=
    fun j => ChainSetup.measurable_step cstep j
  have hτ : Measurable (tau q W A₀ (ChainSetup.step cstep) η r₀ c₃ N) :=
    measurable_tau (ChainSetup.filtration (F := EuclideanSpace ℝ (UT n))) hG N

  have hVm : ∀ p : UT n, StronglyMeasurable[
      ChainSetup.filtration (F := EuclideanSpace ℝ (UT n)) k]
      fun ω => stoppedV q W A₀ (ChainSetup.step cstep) η r₀ c₃ N k ω p :=
    fun p => stronglyMeasurable_stoppedV_coord _ hξa hG N k p
  have hKm : ∀ p p' : UT n, StronglyMeasurable[
      ChainSetup.filtration (F := EuclideanSpace ℝ (UT n)) k]
      fun ω => ((stoppedSub q W A₀ (ChainSetup.step cstep) η r₀ c₃ N k ω).starProjection
        (EuclideanSpace.single p (1 : ℝ))) p' :=
    fun p p' => stronglyMeasurable_stoppedSub_coeff _ hξa hG N k p p'
  have hDm : ∀ j, StronglyMeasurable[
      ChainSetup.filtration (F := EuclideanSpace ℝ (UT n)) j]
      (stoppedLogDet q W A₀ (ChainSetup.step cstep) η r₀ c₃ N j) :=
    fun j => stronglyMeasurable_stoppedLogDet _ hξa hG hN hr₀ hc₃ j

  have hintV : ∀ p : UT n, Integrable (fun ω =>
      stoppedV q W A₀ (ChainSetup.step cstep) η r₀ c₃ N k ω p * ChainSetup.step cstep k ω p)
      (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))) := by
    intro p
    exact (ChainSetup.integrable_step_apply cstep k p).bdd_mul
      (c := Real.sqrt n / (a₀ - (r₀ + c₃ * η)))
      ((hVm p).mono (ChainSetup.natFil_le k)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω =>
        abs_stoppedV_coord_le hN hA₀ hq hne hA₀m hη hr₀ hc₃ hlt k ω p)
  have hintK : ∀ p p' : UT n, Integrable (fun ω =>
      ((stoppedSub q W A₀ (ChainSetup.step cstep) η r₀ c₃ N k ω).starProjection
          (EuclideanSpace.single p (1 : ℝ))) p'
        * (ChainSetup.step cstep k ω p * ChainSetup.step cstep k ω p'))
      (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))) := by
    intro p p'
    exact ChainSetup.integrable_bddCoeff_mul cstep k p p'
      ((hKm p p').mono (ChainSetup.natFil_le k)).aestronglyMeasurable
      (fun ω => ChainSetup.abs_starProjection_single_le_one _ p p')
  have hdecomp : (fun ω => ⟪stoppedV q W A₀ (ChainSetup.step cstep) η r₀ c₃ N k ω,
        ChainSetup.step cstep k ω⟫)
      = fun ω => ∑ p : UT n,
          stoppedV q W A₀ (ChainSetup.step cstep) η r₀ c₃ N k ω p
            * ChainSetup.step cstep k ω p := by
    funext ω
    simp [PiLp.inner_apply, mul_comm]
  have itr : Integrable (fun ω => ⟪stoppedV q W A₀ (ChainSetup.step cstep) η r₀ c₃ N k ω,
      ChainSetup.step cstep k ω⟫) (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))) := by
    rw [hdecomp]
    exact integrable_finsetSum _ fun p _ => hintV p
  have hquadrep : (fun ω => ‖(stoppedSub q W A₀ (ChainSetup.step cstep) η r₀ c₃ N k ω).starProjection
        (ChainSetup.step cstep k ω)‖ ^ 2)
      = fun ω => ∑ p : UT n, ∑ p' : UT n,
          ((stoppedSub q W A₀ (ChainSetup.step cstep) η r₀ c₃ N k ω).starProjection
            (EuclideanSpace.single p (1 : ℝ))) p'
            * (ChainSetup.step cstep k ω p * ChainSetup.step cstep k ω p') :=
    funext fun ω => StepInputs2.norm_starProjection_sq_eq _ _
  have iquad : Integrable (fun ω =>
      (1 / (2 * (a₀ + (r₀ + c₃ * η)) ^ 2 * (1 + δ) ^ 2))
        * ‖(stoppedSub q W A₀ (ChainSetup.step cstep) η r₀ c₃ N k ω).starProjection
            (ChainSetup.step cstep k ω)‖ ^ 2)
      (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))) := by
    refine Integrable.const_mul ?_ _
    rw [hquadrep]
    exact integrable_finsetSum _ fun p _ =>
      integrable_finsetSum _ fun p' _ => hintK p p'
  have iD : ∀ j, Integrable (stoppedLogDet q W A₀ (ChainSetup.step cstep) η r₀ c₃ N j)
      (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))) := fun j =>
    DriftStopped6.integrable_stoppedLogDet hN hξm hτ hA₀ hq hne hA₀m hη hr₀ hc₃ hlt j

  have h2 : (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n)))[
      fun ω => ⟪stoppedV q W A₀ (ChainSetup.step cstep) η r₀ c₃ N k ω,
        ChainSetup.step cstep k ω⟫
      | ChainSetup.filtration (F := EuclideanSpace ℝ (UT n)) k]
      =ᵐ[ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))] 0 :=
    StepInputs2.condExp_inner_eq_zero (ChainSetup.natFil_le k) hVm (hξm k)
      (ChainSetup.indep_step_natFil cstep k)
      (fun p => StepInputs2.integral_coord_eq_zero (hξm k)
        (fun r => ChainSetup.step_coord_law cstep k r) p)
      (fun p => ChainSetup.integrable_step_apply cstep k p) hintV

  have h3 : (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n)))[
      fun ω => (1 / (2 * (a₀ + (r₀ + c₃ * η)) ^ 2 * (1 + δ) ^ 2))
        * ‖(stoppedSub q W A₀ (ChainSetup.step cstep) η r₀ c₃ N k ω).starProjection
            (ChainSetup.step cstep k ω)‖ ^ 2
      | ChainSetup.filtration (F := EuclideanSpace ℝ (UT n)) k]
      =ᵐ[ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))] fun ω =>
        ((1 / (2 * (a₀ + (r₀ + c₃ * η)) ^ 2 * (1 + δ) ^ 2)) * cstep ^ 2)
          * DriftStopped6.stoppedFreeDim q W A₀ (ChainSetup.step cstep) η r₀ c₃ N k ω := by
    have hbase := StepInputs2.condExp_norm_starProjection_sq
      (K := fun ω => stoppedSub q W A₀ (ChainSetup.step cstep) η r₀ c₃ N k ω)
      (ξ := ChainSetup.step cstep k) (v := Real.toNNReal (cstep ^ 2))
      (hξm k) (ChainSetup.step_coord_indep cstep k)
      (fun p => ChainSetup.step_coord_law cstep k p)
      (fun p p' => ChainSetup.integrable_step_mul cstep k p p') hintK
      (ChainSetup.natFil_le k) hKm (ChainSetup.indep_step_natFil cstep k)
    have hsmul := condExp_smul (μ := ChainSetup.gaussPath (EuclideanSpace ℝ (UT n)))
      (1 / (2 * (a₀ + (r₀ + c₃ * η)) ^ 2 * (1 + δ) ^ 2))
      (fun ω => ‖(stoppedSub q W A₀ (ChainSetup.step cstep) η r₀ c₃ N k ω).starProjection
        (ChainSetup.step cstep k ω)‖ ^ 2)
      (ChainSetup.filtration (F := EuclideanSpace ℝ (UT n)) k)
    have hv : ((Real.toNNReal (cstep ^ 2) : ℝ≥0) : ℝ) = cstep ^ 2 :=
      Real.coe_toNNReal _ (sq_nonneg cstep)
    filter_upwards [hsmul, hbase] with ω hω1 hω2
    have hstep : ((ChainSetup.gaussPath (EuclideanSpace ℝ (UT n)))[
        fun ω => (1 / (2 * (a₀ + (r₀ + c₃ * η)) ^ 2 * (1 + δ) ^ 2))
          * ‖(stoppedSub q W A₀ (ChainSetup.step cstep) η r₀ c₃ N k ω).starProjection
              (ChainSetup.step cstep k ω)‖ ^ 2
        | ChainSetup.filtration (F := EuclideanSpace ℝ (UT n)) k]) ω
        = (1 / (2 * (a₀ + (r₀ + c₃ * η)) ^ 2 * (1 + δ) ^ 2))
          * ((ChainSetup.gaussPath (EuclideanSpace ℝ (UT n)))[
            fun ω => ‖(stoppedSub q W A₀ (ChainSetup.step cstep) η r₀ c₃ N k ω).starProjection
              (ChainSetup.step cstep k ω)‖ ^ 2
            | ChainSetup.filtration (F := EuclideanSpace ℝ (UT n)) k]) ω := hω1
    have hω2' : ((ChainSetup.gaussPath (EuclideanSpace ℝ (UT n)))[
        fun ω => ‖(stoppedSub q W A₀ (ChainSetup.step cstep) η r₀ c₃ N k ω).starProjection
          (ChainSetup.step cstep k ω)‖ ^ 2
        | ChainSetup.filtration (F := EuclideanSpace ℝ (UT n)) k]) ω
        = ((Real.toNNReal (cstep ^ 2) : ℝ≥0) : ℝ)
            * (finrank ℝ (stoppedSub q W A₀ (ChainSetup.step cstep) η r₀ c₃ N k ω) : ℝ) := hω2
    rw [hstep, hω2', hv, DriftStopped6.stoppedFreeDim]
    ring
  exact condExp_step_le_cond (ChainSetup.natFil_le k)
    (Filter.Eventually.of_forall fun ω =>
      hpt_stopped hN hA₀ hq hne hA₀m hη hr₀ hc₃ hlt hδ hδ0 hδ1 k ω)
    (hDm k) (iD (k + 1)) (iD k) itr iquad (hinterr k) h2 h3

end Path

section Record

variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}

theorem driftInputs_stopped {cstep η a₀ r₀ c₃ δ cq : ℝ} {N m : ℕ}
    (hN : 1 ≤ N) (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    (hA₀m : symMat A₀ = a₀ • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hη : 0 ≤ η) (hr₀ : 0 ≤ r₀) (hc₃ : 0 ≤ c₃) (hlt : r₀ + c₃ * η < a₀)
    (hδ : η / (a₀ - (r₀ + c₃ * η)) ≤ δ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hcq : cq = 1 / (2 * (a₀ + (r₀ + c₃ * η)) ^ 2 * (1 + δ) ^ 2))
    (hinterr : ∀ k, Integrable
      (stoppedErr q W A₀ (ChainSetup.step cstep) η r₀ c₃ cq N k)
      (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n)))) :
    ChainDrift.DriftInputs (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n)))
      (⇑(ChainSetup.filtration (F := EuclideanSpace ℝ (UT n))))
      (stoppedLogDet q W A₀ (ChainSetup.step cstep) η r₀ c₃ N)
      (DriftStopped6.stoppedFreeDim q W A₀ (ChainSetup.step cstep) η r₀ c₃ N)
      (errCond (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n)))
        (⇑(ChainSetup.filtration (F := EuclideanSpace ℝ (UT n))))
        q W A₀ (ChainSetup.step cstep) η r₀ c₃ cq N)
      (cq * cstep ^ 2) m := by
  have hG : ∀ k, MeasurableSet[ChainSetup.filtration (F := EuclideanSpace ℝ (UT n)) k]
      (stateGood q W A₀ (ChainSetup.step cstep) η r₀ c₃ k) :=
    fun k => measurableSet_stateGood_step cstep η r₀ c₃ k
  exact
    { le := fun k => ChainSetup.natFil_le k
      step := fun k _ =>
        driftInputs_step_stopped hN hA₀ hq hne hA₀m hη hr₀ hc₃ hlt hδ hδ0 hδ1 hcq hinterr k
      intD := fun k _ =>
        DriftStopped6.integrable_stoppedLogDet hN (fun j => ChainSetup.measurable_step cstep j)
          (measurable_tau (ChainSetup.filtration (F := EuclideanSpace ℝ (UT n))) hG N)
          hA₀ hq hne hA₀m hη hr₀ hc₃ hlt k
      intN := fun k _ =>
        DriftStopped6.integrable_stoppedFreeDim (fun j => ChainSetup.measurable_step cstep j)
          (measurable_tau (ChainSetup.filtration (F := EuclideanSpace ℝ (UT n))) hG N) k
      interr := fun _k _ => integrable_errCond _ }

end Record

section Adopted

variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}

/-- `η ≤ 1/4` at the adopted parameters: `c₃ = n²` is at least `1`, so `DriftStopped7.c3_mul_eta_le`
bounds `η` itself. -/
theorem etaAdopted_le_quarter (hn : 2073600 ≤ n) : DriftStopped6.etaAdopted n ≤ 1 / 4 := by
  have h := DriftStopped7.c3_mul_eta_le hn
  have he0 : (0 : ℝ) ≤ DriftStopped6.etaAdopted n := DriftStopped7.etaAdopted_nonneg (n := n)
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  rw [DriftStopped6.c3Adopted] at h
  nlinarith

end Adopted

section Capstone

variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}

end Capstone

end D5.S3.Arith.Lattices.Klartag.Drift.Stopped.DriftInputsStopped
