/- GID: D5/S3/Arith/Lattices/Klartag/Completion/GoodPathCore
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Completion/GoodPathCore
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform constants and completion of lattice packing. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.State.StateSupply
import D5.S3.Arith.Lattices.Klartag.Contact.ThetaTight
import D5.S3.Arith.Lattices.Klartag.Completion.GoodPathLight

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

noncomputable def mAt (n : ℕ) (c₃ : ℝ) : ℝ :=
  a0C n - (DriftStopped6.r0Adopted n + c₃ * DriftStopped6.etaAdopted n)
noncomputable def MAt (n : ℕ) (c₃ : ℝ) : ℝ :=
  a0C n + (DriftStopped6.r0Adopted n + c₃ * DriftStopped6.etaAdopted n)
noncomputable def deltaAt (n : ℕ) (c₃ : ℝ) : ℝ := DriftStopped6.etaAdopted n / mAt n c₃
noncomputable def cqAt (n : ℕ) (c₃ : ℝ) : ℝ :=
  1 / (2 * MAt n c₃ ^ 2 * (1 + deltaAt n c₃) ^ 2)

section Consts
variable {n : ℕ} {c₃ : ℝ}

theorem half_le_mAt (hn : 2073600 ≤ n) (hc₃ : c₃ * DriftStopped6.etaAdopted n ≤ 1 / 4) :
    (1 : ℝ) / 2 ≤ mAt n c₃ := by
  have h1 := DriftStopped7.one_le_a0C (n := n) (by omega)
  have h2 := DriftStopped7.r0Adopted_le hn
  rw [mAt]; linarith

theorem one_le_MAt (hn : 2073600 ≤ n) (hc₃0 : 0 ≤ c₃) : (1 : ℝ) ≤ MAt n c₃ := by
  have h1 := DriftStopped7.one_le_a0C (n := n) (by omega)
  have h2 : 0 ≤ DriftStopped6.r0Adopted n := DriftStopped7.r0Adopted_nonneg
  have h3 : 0 ≤ c₃ * DriftStopped6.etaAdopted n :=
    mul_nonneg hc₃0 (DriftStopped7.etaAdopted_nonneg (n := n))
  rw [MAt]; linarith

theorem lt_a0C_of_mAt (hn : 2073600 ≤ n) (hc₃ : c₃ * DriftStopped6.etaAdopted n ≤ 1 / 4) :
    DriftStopped6.r0Adopted n + c₃ * DriftStopped6.etaAdopted n < a0C n := by
  have h := half_le_mAt hn hc₃; rw [mAt] at h; linarith

theorem deltaAt_nonneg (hn : 2073600 ≤ n) (hc₃ : c₃ * DriftStopped6.etaAdopted n ≤ 1 / 4) :
    0 ≤ deltaAt n c₃ := by
  have h := half_le_mAt hn hc₃
  rw [deltaAt]
  exact div_nonneg (DriftStopped7.etaAdopted_nonneg (n := n)) (by linarith)

theorem deltaAt_lt_one (hn : 2073600 ≤ n) (hc₃ : c₃ * DriftStopped6.etaAdopted n ≤ 1 / 4) :
    deltaAt n c₃ < 1 := by
  have hm := half_le_mAt hn hc₃
  have he := etaAdopted_le_quarter hn
  rw [deltaAt, div_lt_one (by linarith)]; linarith

theorem two_le_cqAt_den (hn : 2073600 ≤ n) (hc₃ : c₃ * DriftStopped6.etaAdopted n ≤ 1 / 4)
    (hc₃0 : 0 ≤ c₃) : (2 : ℝ) ≤ 2 * MAt n c₃ ^ 2 * (1 + deltaAt n c₃) ^ 2 := by
  have hM := one_le_MAt hn hc₃0
  have hd := deltaAt_nonneg hn hc₃
  have hM2 : (1 : ℝ) ≤ MAt n c₃ ^ 2 := by nlinarith
  have hd2 : (1 : ℝ) ≤ (1 + deltaAt n c₃) ^ 2 := by nlinarith
  nlinarith

theorem cqAt_nonneg (hn : 2073600 ≤ n) (hc₃ : c₃ * DriftStopped6.etaAdopted n ≤ 1 / 4)
    (hc₃0 : 0 ≤ c₃) : 0 ≤ cqAt n c₃ := by
  have h := two_le_cqAt_den hn hc₃ hc₃0
  rw [cqAt]; exact div_nonneg zero_le_one (by linarith)

end Consts

section Meas

variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι] {Ω : Type*} [m0 : MeasurableSpace Ω]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}
  {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)}

/-- The constant filtration, so the `ℱ`-relative lemmas of `DriftInputsStopped` give their ambient
forms with no second proof. -/
def constFil (m0 : MeasurableSpace Ω) : Filtration ℕ m0 where
  seq := fun _ => m0
  mono' := monotone_const
  le' := fun _ => le_rfl

theorem measurable_gaussStep (hξ : ∀ j, Measurable (ξ j)) (j : ℕ) :
    Measurable (StateInvariant.gaussStep q W A₀ ξ j) :=
  measurable_gaussStep_fil (constFil m0) (fun i => hξ i) j

theorem measurable_preState (hξ : ∀ j, Measurable (ξ j)) (k : ℕ) :
    Measurable (ChainWiring.preState q W A₀ ξ k) :=
  (Chain.measurable_chain_fst hξ k).add (measurable_gaussStep hξ k)

theorem measurable_logDet {α : Type*} [MeasurableSpace α] {f : α → EuclideanSpace ℝ (UT n)}
    (hf : Measurable f) : Measurable fun a => ChainWiring.logDet (f a) :=
  Real.measurable_log.comp ((DriftStopped6.continuous_symMat_det (n := n)).measurable.comp hf)

theorem measurable_chainErr (hξ : ∀ j, Measurable (ξ j)) (k : ℕ) :
    Measurable (ChainWiring.chainErr q W A₀ ξ k) := by
  have hpre := measurable_preState (q := q) (W := W) (A₀ := A₀) hξ k
  have hlift : Measurable fun ω => Chain.lift q W (ChainWiring.preState q W A₀ ξ k ω) :=
    (Chain.measurable_lift q W).comp hpre
  exact (measurable_logDet hlift).sub (measurable_logDet hpre)

theorem measurable_stoppedV_coord (hξ : ∀ j, Measurable (ξ j)) {η r₀ c₃ : ℝ} (N k : ℕ)
    (p : UT n) :
    Measurable fun ω => stoppedV q W A₀ ξ η r₀ c₃ N k ω p := by
  have hG : ∀ j, MeasurableSet[constFil m0 j] (stateGood q W A₀ ξ η r₀ c₃ j) := by
    intro j
    exact measurableSet_stateGood_fil (constFil m0) (fun i => hξ i) j
  exact (stronglyMeasurable_stoppedV_coord (constFil m0) (fun i => hξ i) hG N k p).measurable

theorem measurable_stoppedErr (hξ : ∀ j, Measurable (ξ j)) {η r₀ c₃ cq : ℝ} {N : ℕ}
    (hτ : Measurable (tau q W A₀ ξ η r₀ c₃ N)) (k : ℕ) :
    Measurable (stoppedErr q W A₀ ξ η r₀ c₃ cq N k) := by
  classical
  have hinner : Measurable fun ω => ⟪stoppedV q W A₀ ξ η r₀ c₃ N k ω, ξ k ω⟫ := by
    have hrep : (fun ω => ⟪stoppedV q W A₀ ξ η r₀ c₃ N k ω, ξ k ω⟫)
        = fun ω => ∑ p : UT n, stoppedV q W A₀ ξ η r₀ c₃ N k ω p * ξ k ω p := by
      funext ω; simp [PiLp.inner_apply, mul_comm]
    rw [hrep]
    exact Finset.measurable_sum _ fun p _ =>
      (measurable_stoppedV_coord hξ N k p).mul
        (((PiLp.continuous_apply 2 (fun _ : UT n => ℝ) p).measurable).comp (hξ k))
  have hmid : Measurable fun ω =>
      cq * ‖(Chain.freeSub q (Chain.chain q W A₀ ξ k ω).2).starProjection (ξ k ω)‖ ^ 2
        - ⟪stoppedV q W A₀ ξ η r₀ c₃ N k ω, ξ k ω⟫ :=
    (((measurable_gaussStep hξ k).norm.pow_const 2).const_mul cq).sub hinner
  have hs1 : MeasurableSet {ω | k + 1 ≤ tau q W A₀ ξ η r₀ c₃ N ω - 1} :=
    (hτ.sub_const 1) (measurableSet_Ici (a := k + 1))
  have hs2 : MeasurableSet {ω | k < tau q W A₀ ξ η r₀ c₃ N ω} :=
    hτ (measurableSet_Ioi (a := k))
  exact Measurable.ite hs1 (measurable_chainErr hξ k)
    (Measurable.ite hs2 hmid measurable_const)

end Meas

section Int

variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}

theorem integrable_norm_step (c : ℝ) (k : ℕ) :
    Integrable (fun ω : ℕ → EuclideanSpace ℝ (UT n) => ‖ChainSetup.step c k ω‖)
      (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))) := by
  have hdom : Integrable (fun ω : ℕ → EuclideanSpace ℝ (UT n) =>
      1 + ‖ChainSetup.step c k ω‖ ^ 2) (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))) :=
    (integrable_const (1 : ℝ)).add (ChainSetup.integrable_norm_sq_step c k)
  refine Integrable.mono' hdom
    ((ChainSetup.measurable_step c k).norm.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  nlinarith [norm_nonneg (ChainSetup.step c k ω), sq_nonneg (‖ChainSetup.step c k ω‖ - 1)]

end Int

section Drift

variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}

end Drift

section Fail

variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}

theorem etaAdopted_pos (hn : 3 ≤ n) : 0 < DriftStopped6.etaAdopted n := by
  have h1 : (0 : ℝ) < ParamsAdopted2.stepSizeAdopted2 n := D5.S3.Arith.Lattices.Klartag.stepSizeAdopted2_pos hn
  have h2 : (0 : ℝ) < (Fintype.card (UT n) : ℝ) := by
    exact_mod_cast D5.S3.Arith.Lattices.Klartag.card_UT_pos hn
  have h3 : (0 : ℝ) < (n : ℝ) := by
    have : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  rw [DriftStopped6.etaAdopted]
  exact Real.sqrt_pos.2 (by positivity)

/-- `v = c² = h` at the adopted step scale. -/
theorem coe_v_adopted (hn : 3 ≤ n) :
    ((Real.toNNReal (D5.S3.Arith.Lattices.Klartag.cAdopted n ^ 2) : ℝ≥0) : ℝ)
      = ParamsAdopted2.stepSizeAdopted2 n := by
  rw [Real.coe_toNNReal _ (sq_nonneg _), D5.S3.Arith.Lattices.Klartag.cAdopted,
    Real.sq_sqrt (D5.S3.Arith.Lattices.Klartag.stepSizeAdopted2_pos hn).le]

/-- **The per-step tail is exactly `e^{−n}`** — the adopted `η = √(2hdn)` is chosen for it. -/
theorem step_tail_exponent (hn : 3 ≤ n) :
    -(DriftStopped6.etaAdopted n ^ 2 / (Fintype.card (UT n) : ℝ))
        / (2 * ((Real.toNNReal (D5.S3.Arith.Lattices.Klartag.cAdopted n ^ 2) : ℝ≥0) : ℝ)) = -(n : ℝ) := by
  have hh : (0 : ℝ) < ParamsAdopted2.stepSizeAdopted2 n := D5.S3.Arith.Lattices.Klartag.stepSizeAdopted2_pos hn
  have hd : (0 : ℝ) < (Fintype.card (UT n) : ℝ) := by
    exact_mod_cast D5.S3.Arith.Lattices.Klartag.card_UT_pos hn
  have hsq : DriftStopped6.etaAdopted n ^ 2
      = 2 * ParamsAdopted2.stepSizeAdopted2 n * (Fintype.card (UT n) : ℝ) * (n : ℝ) := by
    rw [DriftStopped6.etaAdopted, Real.sq_sqrt (by positivity)]
  rw [hsq, coe_v_adopted hn]
  field_simp

theorem chainGood_failure (hn : 3 ≤ n) {r : ℝ} (hr : 0 < r) :
    (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))).real
        (StepGlue.chainGood r (ChainSetup.coord 0)
          (ChainSetup.step (D5.S3.Arith.Lattices.Klartag.cAdopted n)) (6 * r * 1 * Real.sqrt n)
          (ParamsAdopted2.numStepsAdopted2 n) (DriftStopped6.etaAdopted n))ᶜ
      ≤ (33 * (n : ℝ) ^ 9 * Real.log n + 4) * Real.exp (-(n : ℝ)) := by
  have hbase := StepGlue.measureReal_compl_chainGood_le
    (P := ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))) (n := n) hr
    (ChainSetup.measurable_coord 0) (ChainSetup.map_coord 0)
    (ξ := ChainSetup.step (D5.S3.Arith.Lattices.Klartag.cAdopted n))
    (v := Real.toNNReal (D5.S3.Arith.Lattices.Klartag.cAdopted n ^ 2))
    (fun k p => ChainSetup.step_coord_law (D5.S3.Arith.Lattices.Klartag.cAdopted n) k p)
    (etaAdopted_pos hn) (ParamsAdopted2.numStepsAdopted2 n) 1 le_rfl
  refine StateInvariant2.failure_le2 hn ?_
  refine le_trans hbase (le_of_eq ?_)
  rw [step_tail_exponent hn]
  norm_num

/-- **The `accGood` failure bound.**  The adopted `r₀ = 24√(log n/n)` is exactly
`6·√(N·h)·√n`, so the GOE tail closes at `s = 1` with equality. -/
theorem accGood_thr (hn : 3 ≤ n) :
    6 * (Real.sqrt (ParamsAdopted2.numStepsAdopted2 n) * D5.S3.Arith.Lattices.Klartag.cAdopted n) * 1
        * Real.sqrt n ≤ DriftStopped6.r0Adopted n := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hlog : (0 : ℝ) ≤ Real.log n := le_trans (by norm_num) (ChainDrift.log_pos_of_three hn)
  have hNh := ParamsAdopted2.numStepsAdopted2_mul_stepSizeAdopted2 hn
  have hprod : Real.sqrt (ParamsAdopted2.numStepsAdopted2 n) * D5.S3.Arith.Lattices.Klartag.cAdopted n
      = Real.sqrt (ChainDrift.horizon n) := by
    rw [D5.S3.Arith.Lattices.Klartag.cAdopted, ← Real.sqrt_mul (by positivity), hNh]
  have hhor : Real.sqrt (ChainDrift.horizon n) = 4 * Real.sqrt (Real.log n) / (n : ℝ) := by
    rw [ChainDrift.horizon, Real.sqrt_div' _ (by positivity), show (16 : ℝ) * Real.log n
      = 4 ^ 2 * Real.log n by norm_num, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by norm_num), show ((n : ℝ) ^ 2) = (n : ℝ) ^ 2 from rfl,
      Real.sqrt_sq hn0.le]
  have hr0 : DriftStopped6.r0Adopted n = 24 * (Real.sqrt (Real.log n) / Real.sqrt n) := by
    rw [DriftStopped6.r0Adopted, Real.sqrt_div' _ hn0.le]
  rw [hprod, hhor, hr0]
  have hsq : Real.sqrt n * Real.sqrt n = (n : ℝ) := Real.mul_self_sqrt hn0.le
  have hspos : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.2 hn0
  rw [le_iff_eq_or_lt]
  left
  field_simp
  nlinarith [hsq, hspos, Real.sqrt_nonneg (Real.log n)]

theorem accGood_failure (hn : 3 ≤ n) :
    (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))).real
        (accGood q W A₀ (ChainSetup.step (D5.S3.Arith.Lattices.Klartag.cAdopted n))
          (ParamsAdopted2.numStepsAdopted2 n) (DriftStopped6.r0Adopted n))ᶜ
      ≤ ((ParamsAdopted2.numStepsAdopted2 n : ℕ) : ℝ)
          * (2 * (4 * Real.exp (-(1 ^ 2 * (n : ℝ))))) :=
  StateInvariant4.measureReal_compl_accGood_le' (D5.S3.Arith.Lattices.Klartag.cAdopted_pos hn)
    DriftStopped7.r0Adopted_nonneg le_rfl
    (fun k => ChainSetup.measurable_step (D5.S3.Arith.Lattices.Klartag.cAdopted n) k)
    (ChainSetup.iIndepFun_step (D5.S3.Arith.Lattices.Klartag.cAdopted n))
    (fun j => ChainSetup.map_step (D5.S3.Arith.Lattices.Klartag.cAdopted n) j) (accGood_thr hn)

end Fail

section Bounds

variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι] {Ω : Type*} [m0 : MeasurableSpace Ω]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}
  {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)}

theorem stoppedLogDet_zero {η r₀ c₃ : ℝ} {N : ℕ} (ω : Ω) :
    stoppedLogDet q W A₀ ξ η r₀ c₃ N 0 ω = ChainWiring.logDet A₀ := by
  rw [stoppedLogDet, stoppedState, Nat.zero_min, Chain.chain_zero]

end Bounds

section Existence

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **The two-event pigeonhole**, self-contained: `DriftStopped6.exists_mem_inter_of_one_lt` is
stated inside a section whose chain variables are not determined by its statement, so applying it
leaves `IsProbabilityMeasure` stuck on a metavariable. -/
theorem exists_mem_inter_of_one_lt' {G S : Set Ω} (hS : MeasurableSet S)
    (h : 1 < P.real G + P.real S) : ∃ ω, ω ∈ G ∧ ω ∈ S := by
  by_contra hcon
  have hcon : ∀ ω, ω ∈ G → ω ∉ S := fun ω hg hs => hcon ⟨ω, hg, hs⟩
  have hdisj : AEDisjoint P G S := by
    have hempty : G ∩ S = (∅ : Set Ω) := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
      exact hcon ω
    rw [AEDisjoint, hempty]
    simp
  have hadd : P.real (G ∪ S) = P.real G + P.real S :=
    measureReal_union₀ hS.nullMeasurableSet hdisj (measure_ne_top P G) (measure_ne_top P S)
  have hle : P.real (G ∪ S) ≤ 1 := measureReal_le_one
  linarith

end Existence

section MeasSets

variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι] {Ω : Type*} [m0 : MeasurableSpace Ω]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}
  {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)}

theorem measurable_gaussSum (hξ : ∀ j, Measurable (ξ j)) (k : ℕ) :
    Measurable (StateInvariant.gaussSum q W A₀ ξ k) :=
  measurable_gaussSum_fil (constFil m0) (fun i => hξ i) k

/-- The operator norm of `r • symMat` is measurable — `Increments.measurable_opNorm_mkMat`
through `Increments.smul_symMat_eq_mkMat`. -/
theorem measurable_opNorm_smul_symMat {α : Type*} [MeasurableSpace α] (r : ℝ)
    {f : α → EuclideanSpace ℝ (UT n)} (hf : Measurable f) :
    Measurable fun a => ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (r • symMat (f a))‖ := by
  have hmk : (fun a => ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (r • symMat (f a))‖)
      = fun a => ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (mkMat (coordVec r (f a)))‖ := by
    funext a; rw [smul_symMat_eq_mkMat r (f a)]
  rw [hmk]
  exact (measurable_opNorm_mkMat (n := n)).comp ((measurable_coordVec (n := n) r).comp hf)

theorem measurable_opNorm_symMat {α : Type*} [MeasurableSpace α]
    {f : α → EuclideanSpace ℝ (UT n)} (hf : Measurable f) :
    Measurable fun a => ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (symMat (f a))‖ := by
  have h := measurable_opNorm_smul_symMat (1 : ℝ) hf
  simpa using h

theorem measurableSet_goodEventUT {Wacc : Ω → EuclideanSpace ℝ (UT n)} (hW : Measurable Wacc)
    (r thr : ℝ) : MeasurableSet (StepInputs.goodEventUT r Wacc thr) :=
  measurableSet_le (measurable_opNorm_smul_symMat r hW) measurable_const

theorem measurableSet_stepGood (hξ : ∀ j, Measurable (ξ j)) (N : ℕ) (η : ℝ) :
    MeasurableSet (StepInputs2.stepGood ξ N η) := by
  have hrep : StepInputs2.stepGood ξ N η = ⋂ k ∈ {k : ℕ | k < N}, {ω | ‖ξ k ω‖ ≤ η} := by
    ext ω
    simp only [StepInputs2.stepGood, Set.mem_ofPred_eq, Set.mem_iInter]
  rw [hrep]
  exact MeasurableSet.biInter (Set.to_countable _)
    fun k _ => measurableSet_le (hξ k).norm measurable_const

theorem measurableSet_accGood (hξ : ∀ j, Measurable (ξ j)) (N : ℕ) (r₀ : ℝ) :
    MeasurableSet (StateInvariant.accGood q W A₀ ξ N r₀) := by
  have hrep : StateInvariant.accGood q W A₀ ξ N r₀
      = ⋂ k ∈ {k : ℕ | k < N},
        {ω | ‖Matrix.toEuclideanCLM (𝕜 := ℝ)
          (symMat (StateInvariant.gaussSum q W A₀ ξ k ω))‖ ≤ r₀} := by
    ext ω
    simp only [StateInvariant.accGood, Set.mem_ofPred_eq, Set.mem_iInter]
  rw [hrep]
  exact MeasurableSet.biInter (Set.to_countable _)
    fun k _ => measurableSet_le (measurable_opNorm_symMat (measurable_gaussSum hξ k))
      measurable_const

theorem measurableSet_countGood (hξ : ∀ j, Measurable (ξ j)) (N : ℕ) (c₃ : ℝ) :
    MeasurableSet (StateInvariant4.countGood q W A₀ ξ N c₃) :=
  measurableSet_le (StateInvariant4.measurable_card_chain hξ N) measurable_const

end MeasSets

section Assembly

variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}

/-- The three failure probabilities, summed. -/
noncomputable def failTotal (n : ℕ) (pcnt : ℝ) : ℝ :=
  (33 * (n : ℝ) ^ 9 * Real.log n + 4) * Real.exp (-(n : ℝ))
    + ((ParamsAdopted2.numStepsAdopted2 n : ℕ) : ℝ)
        * (2 * (4 * Real.exp (-((1 : ℝ) ^ 2 * (n : ℝ))))) + pcnt

end Assembly

end D5.S3.Arith.Lattices.Klartag.Completion.GoodPathBounds
