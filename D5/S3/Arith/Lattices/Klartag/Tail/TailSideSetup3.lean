/- GID: D5/S3/Arith/Lattices/Klartag/Tail/TailSideSetup3
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Tail/TailSideSetup3
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Lattice tail bounds along the matrix walk. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Tail.TailSideSetup2
import D5.S3.Arith.Lattices.Klartag.State.PaddedLawSetupR
import D5.S3.Arith.Lattices.Klartag.Construction.LatticeDataR
import D5.S3.Arith.Lattices.Klartag.State.RawDataInst2R

set_option linter.unusedSectionVars false

open D5.S3.Arith.Lattices.Klartag.Completion
open D5.S3.Arith.Lattices.Klartag.Construction
open D5.S3.Arith.Lattices.Klartag.Contact
open D5.S3.Arith.Lattices.Klartag.Drift
open D5.S3.Arith.Lattices.Klartag.Drift.Stopped
open D5.S3.Arith.Lattices.Klartag.Gaussian
open D5.S3.Arith.Lattices.Klartag.State
open D5.S3.Arith.Lattices.Klartag.Tail
open D5.S3.Arith.Lattices.Klartag.Walk

namespace D5.S3.Arith.Lattices.Klartag.Tail.TailSideSetup3

open MeasureTheory
open ProbabilityTheory
open Finset
open scoped ENNReal NNReal RealInnerProductSpace
open D5.S3.Arith.Lattices.Klartag
open D5.S3.Arith.Lattices.Klartag.Walk.Increments
open D5.S3.Arith.Lattices.Klartag.Walk.ChainSetup
open D5.S3.Arith.Lattices.Klartag.State.PaddedLawSetup
open D5.S3.Arith.Lattices.Klartag.Tail.TailSideSetup
open D5.S3.Arith.Lattices.Klartag.Tail.TailSideSetup2
open D5.S3.Arith.Lattices.Klartag.State.PaddedLawSetupR
open D5.S3.Arith.Lattices.Klartag.Construction.Tiling
open D5.S3.Arith.Lattices.Klartag.Construction.Section5
open D5.S3.Arith.Lattices.Klartag.Construction.ConstructionA

noncomputable section

/-- **`TailSideHyp` from the initial gap alone.**  `TailSideSetup2.tailSideHyp_of_rawData`'s proof
with `hraw.hA₀` and `hraw.hr` replaced by hypotheses — no window, and no new mathematics. -/
theorem tailSideHyp_of_gap {n : ℕ} {α : ℝ}
    {q : (Fin n → ℤ) → EuclideanSpace ℝ (UT n)} {W : Finset (Fin n → ℤ)}
    {A₀ : EuclideanSpace ℝ (UT n)}
    (hA₀ : ∀ y ∈ W, (1 : ℝ) < ⟪A₀, q y⟫) (hr : ∀ y ∈ W, 0 < α * ‖toE n y‖)
    (hnd : NormData n α q W A₀) (hn : 3 ≤ n) :
    TailSideHyp n (Real.sqrt (ParamsAdopted2.stepSizeAdopted2 n)) α q W A₀ := by
  classical
  intro k hk hk0 y hy
  set h : ℝ := ParamsAdopted2.stepSizeAdopted2 n with hh
  set c : ℝ := Real.sqrt h with hcdef
  have hh0 : 0 < h := stepSizeAdopted2_pos hn
  have hc0 : 0 < c := Real.sqrt_pos.2 hh0
  have hcsq : c ^ 2 = h := Real.sq_sqrt hh0.le
  have hqy : q y ≠ 0 := by
    intro hz
    have := hA₀ y hy
    rw [hz, inner_zero_right] at this
    linarith
  have hqn : (0 : ℝ) < ‖q y‖ := norm_pos_iff.2 hqy
  set u : ℝ := α * ‖toE n y‖ with hudef
  have hu0 : 0 < u := hr y hy
  have hqu : ‖q y‖ = u ^ 2 := hnd.hnorm y hy
  set M : ℕ → (ℕ → EuclideanSpace ℝ (UT n)) → ℝ :=
    fun i ω => ‖q y‖⁻¹ * constraintM q W A₀ (step c) y i ω with hMdef
  have hstepm : ∀ j, Measurable (step (ι := UT n) c j) := fun j => measurable_step c j
  have hMm : ∀ i, Measurable (M i) := fun i =>
    (measurable_constraintM hstepm y i).const_mul _
  have hM : ∀ i ω, M (i + 1) ω - M i ω
      = c * ⟪ω i, dirOf q W A₀ c y i (restr i ω)⟫ := by
    intro i ω
    have hps := pureWalk_succ_sub (q := q) (W := W) (A₀ := A₀) (ξ := step c) y i ω
    have hdiff : M (i + 1) ω - M i ω
        = ‖q y‖⁻¹ * (pureWalk q W A₀ (step c) y (i + 1) ω - pureWalk q W A₀ (step c) y i ω) := by
      show ‖q y‖⁻¹ * (pureWalk q W A₀ (step c) y (i + 1) ω - 1)
        - ‖q y‖⁻¹ * (pureWalk q W A₀ (step c) y i ω - 1) = _
      ring
    rw [hdiff, hps, dirOf_restr, real_inner_smul_right]
    show ‖q y‖⁻¹ * ⟪c • ω i, (Chain.freeSub q
      (Chain.chain q W A₀ (step c) i ω).2).starProjection (q y)⟫ = _
    rw [real_inner_smul_left]
    ring
  have hzero : ∀ ω, M 0 ω = a0C n - (u ^ 2)⁻¹ := by
    intro ω
    show ‖q y‖⁻¹ * (⟪A₀, q y⟫ - 1) = _
    have huu : (u : ℝ) ≠ 0 := ne_of_gt hu0
    rw [hnd.hinner y hy, hqu]
    field_simp
    ring
  have hM₀ : 0 < a0C n - (u ^ 2)⁻¹ := by
    have hgap := chain_hgap (q := q) (W := W) (A₀ := A₀) (ξ := step c) (hA₀ y hy)
      (fun _ => 0)
    have : 0 < M 0 (fun _ => 0) := mul_pos (inv_pos.2 hqn) hgap
    rwa [hzero] at this
  have ht : 0 < (k : ℝ) * h := by
    have : (0 : ℝ) < (k : ℝ) := by
      have : 0 < k := Nat.pos_of_ne_zero hk0
      exact_mod_cast this
    positivity
  have hv : ((k • Real.toNNReal (c ^ 2) : ℝ≥0) : ℝ) = (k : ℝ) * h * 1 ^ 2 := by
    rw [nsmul_eq_mul, NNReal.coe_mul, hcsq, Real.coe_toNNReal _ hh0.le]
    simp
  have hset : {ω : ℕ → EuclideanSpace ℝ (UT n) |
        ∃ i ≤ k, constraintM q W A₀ (step c) y i ω ≤ 0}
      = {ω | ∃ i ≤ k, M i ω ≤ 0} :=
    (hitSet_smul (M := constraintM q W A₀ (step c) y) (inv_pos.2 hqn) k).symm
  rw [hset]
  exact tail_of_increments hc0 (by omega) (fun i => measurable_dirOf c y i)
    (fun i z => norm_dirOf_le hqy c i z) hMm hM ht hM₀ hzero hv
theorem tailSideHyp_of_rawDataR {p n : ℕ} {α R : ℝ}
    {q : (Fin n → ℤ) → EuclideanSpace ℝ (UT n)} {W : Finset (Fin n → ℤ)}
    {A₀ : EuclideanSpace ℝ (UT n)}
    (hraw : RawDataR p n α R q W A₀) (hnd : NormData n α q W A₀) (hn : 3 ≤ n) :
    TailSideHypR n (Real.sqrt (ParamsAdopted2.stepSizeAdopted2 n)) α q W A₀ :=
  tailSideHyp_of_gap hraw.hA₀ hraw.hr hnd hn

end

end D5.S3.Arith.Lattices.Klartag.Tail.TailSideSetup3
