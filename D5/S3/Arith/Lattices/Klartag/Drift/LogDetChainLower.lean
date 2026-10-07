/- GID: D5/S3/Arith/Lattices/Klartag/Drift/LogDetChainLower
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Drift/LogDetChainLower
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Second order log determinant bounds and accumulated drift. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Drift.LogDetLowerSharp

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

namespace D5.S3.Arith.Lattices.Klartag.Drift.LogDetChainLower

open MeasureTheory
open Matrix
open Finset
open Module
open scoped RealInnerProductSpace
open D5.S3.Arith.Lattices.Klartag
open D5.S3.Arith.Lattices.Klartag.Walk.Increments

section SymMat

variable {n : ℕ}

theorem symMat_add (x y : EuclideanSpace ℝ (UT n)) :
    symMat (x + y) = symMat x + symMat y := by
  ext i j
  simp only [symMat_apply, Matrix.add_apply]
  simp [mul_add]

theorem symMat_isHermitian (x : EuclideanSpace ℝ (UT n)) : (symMat x).IsHermitian :=
  Matrix.isHermitian_iff_isSymm.2 (symMat_isSymm x)

/-- **`symMat` is a Frobenius isometry**: `∑ᵢⱼ (symMat x)ᵢⱼ² = ‖x‖²`. -/
theorem frobenius_symMat (x : EuclideanSpace ℝ (UT n)) :
    ∑ i, ∑ j, (symMat x i j) ^ 2 = ‖x‖ ^ 2 := by
  have h := sum_symMat_mul_eq_inner x x
  have h2 : ∑ i, ∑ j, symMat x i j * symMat x i j = ∑ i, ∑ j, (symMat x i j) ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [sq]
  rw [h2] at h
  rw [h, real_inner_self_eq_norm_sq]

end SymMat

section Step

variable {n : ℕ}

/-- **`LogDetLowerSharp.log_det_add_ge_sharp_of_stateBounds`, in `EuclideanSpace` coordinates.** -/
theorem logDet_add_ge {A H : EuclideanSpace ℝ (UT n)} {m M r : ℝ}
    (hSB : Discharge.StateBounds (symMat A) m M) (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2)
    (hop : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (symMat H)‖ ≤ r * m) :
    ChainWiring.logDet A + ((symMat A)⁻¹ * symMat H).trace
        - ((1 / 2 + 2 * r) / m ^ 2) * ‖H‖ ^ 2
      ≤ ChainWiring.logDet (A + H) := by
  have hmain := LogDetLowerSharp.log_det_add_ge_sharp_of_stateBounds hSB
    (symMat_isHermitian H) hr0 hr hop
  rw [ChainWiring.logDet, ChainWiring.logDet, symMat_add, ← frobenius_symMat H]
  exact hmain

end Step

section Chain

variable {n : ℕ} {ι : Type*} [DecidableEq ι] {Ω : Type*}
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}
  {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)}

/-- **The one-step increment** `H_j = A_{j+1} − A_j`.  By `StateInvariant.preState_eq` and
`StateInvariant.liftStep` it is `gaussStep_j + liftStep_j`. -/
noncomputable def incr (q : ι → EuclideanSpace ℝ (UT n)) (W : Finset ι)
    (A₀ : EuclideanSpace ℝ (UT n)) (ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)) (j : ℕ) (ω : Ω) :
    EuclideanSpace ℝ (UT n) :=
  (Chain.chain q W A₀ ξ (j + 1) ω).1 - (Chain.chain q W A₀ ξ j ω).1

theorem chain_succ_eq_add (j : ℕ) (ω : Ω) :
    (Chain.chain q W A₀ ξ (j + 1) ω).1
      = (Chain.chain q W A₀ ξ j ω).1 + incr q W A₀ ξ j ω := by
  rw [incr]; abel

/-- **`incr = gaussStep + liftStep`** — the split the martingale and the drift read. -/
theorem incr_eq (j : ℕ) (ω : Ω) :
    incr q W A₀ ξ j ω
      = StateInvariant.gaussStep q W A₀ ξ j ω + StateInvariant.liftStep q W A₀ ξ j ω := by
  rw [incr, StateInvariant.liftStep, StateInvariant.preState_eq]
  abel

/-- **The pathwise lower bound on the chain's log-determinant.**  Pure telescoping: the hypotheses
are the state bounds at every index below `K` and a per-step operator-norm ceiling, both of which
`goodCut` supplies. -/
theorem logDet_chain_ge {m M r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2) {ω : Ω} :
    ∀ K : ℕ,
      (∀ j, j < K → Discharge.StateBounds (symMat (Chain.chain q W A₀ ξ j ω).1) m M) →
      (∀ j, j < K → ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (symMat (incr q W A₀ ξ j ω))‖ ≤ r * m) →
      ChainWiring.logDet A₀
          + ∑ j ∈ Finset.range K,
              (((symMat (Chain.chain q W A₀ ξ j ω).1)⁻¹ * symMat (incr q W A₀ ξ j ω)).trace
                - ((1 / 2 + 2 * r) / m ^ 2) * ‖incr q W A₀ ξ j ω‖ ^ 2)
        ≤ ChainWiring.logDet (Chain.chain q W A₀ ξ K ω).1 := by
  intro K
  induction K with
  | zero => intro _ _; simp [Chain.chain_zero]
  | succ K ih =>
    intro hSB hop
    have ihK := ih (fun j hj => hSB j (by omega)) (fun j hj => hop j (by omega))
    have hstep := logDet_add_ge (A := (Chain.chain q W A₀ ξ K ω).1)
      (H := incr q W A₀ ξ K ω) (hSB K (by omega)) hr0 hr (hop K (by omega))
    rw [← chain_succ_eq_add] at hstep
    rw [Finset.sum_range_succ]
    linarith

end Chain

section Split

variable {n : ℕ} {ι : Type*} [DecidableEq ι] {Ω : Type*}
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}
  {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)}

/-- **The bound in the shape `ShortfallBound.shortfall_le` consumes**: `X ≥ c + M − D` with
`c = logDet A₀`, `M` the trace sum and `D` the Frobenius sum scaled by `κ`. -/
theorem logDet_chain_ge_split {m M r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2) {ω : Ω} (K : ℕ)
    (hSB : ∀ j, j < K → Discharge.StateBounds (symMat (Chain.chain q W A₀ ξ j ω).1) m M)
    (hop : ∀ j, j < K →
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (symMat (incr q W A₀ ξ j ω))‖ ≤ r * m) :
    ChainWiring.logDet A₀
        + (∑ j ∈ Finset.range K,
            ((symMat (Chain.chain q W A₀ ξ j ω).1)⁻¹ * symMat (incr q W A₀ ξ j ω)).trace)
        - ((1 / 2 + 2 * r) / m ^ 2)
            * (∑ j ∈ Finset.range K, ‖incr q W A₀ ξ j ω‖ ^ 2)
      ≤ ChainWiring.logDet (Chain.chain q W A₀ ξ K ω).1 := by
  have h := logDet_chain_ge (q := q) (W := W) (A₀ := A₀) (ξ := ξ) (m := m) (M := M) hr0 hr
    (ω := ω) K hSB hop
  have hsplit : ∑ j ∈ Finset.range K,
        (((symMat (Chain.chain q W A₀ ξ j ω).1)⁻¹ * symMat (incr q W A₀ ξ j ω)).trace
          - ((1 / 2 + 2 * r) / m ^ 2) * ‖incr q W A₀ ξ j ω‖ ^ 2)
      = (∑ j ∈ Finset.range K,
          ((symMat (Chain.chain q W A₀ ξ j ω).1)⁻¹ * symMat (incr q W A₀ ξ j ω)).trace)
        - ((1 / 2 + 2 * r) / m ^ 2) * (∑ j ∈ Finset.range K, ‖incr q W A₀ ξ j ω‖ ^ 2) := by
    rw [Finset.sum_sub_distrib, Finset.mul_sum]
  rw [hsplit] at h
  linarith

/-- **The Frobenius sum, dominated by the unprojected steps plus the lift.**  `‖a + b‖² ≤
(1+ε)‖a‖² + (1+1/ε)‖b‖²`, and `‖gaussStep_j‖ ≤ ‖ξ_j‖` because it is an orthogonal projection. -/
theorem norm_incr_sq_le {ε : ℝ} (hε : 0 < ε) (j : ℕ) (ω : Ω) :
    ‖incr q W A₀ ξ j ω‖ ^ 2
      ≤ (1 + ε) * ‖StateInvariant.gaussStep q W A₀ ξ j ω‖ ^ 2
        + (1 + 1 / ε) * ‖StateInvariant.liftStep q W A₀ ξ j ω‖ ^ 2 := by
  rw [incr_eq]
  set a := StateInvariant.gaussStep q W A₀ ξ j ω
  set b := StateInvariant.liftStep q W A₀ ξ j ω
  have hexp : ‖a + b‖ ^ 2 = ‖a‖ ^ 2 + 2 * ⟪a, b⟫ + ‖b‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
      ← real_inner_self_eq_norm_sq, inner_add_add_self, real_inner_comm b a]
    ring
  have hcs : ⟪a, b⟫ ≤ ‖a‖ * ‖b‖ := real_inner_le_norm a b
  have hamgm : 2 * (‖a‖ * ‖b‖) ≤ ε * ‖a‖ ^ 2 + (1 / ε) * ‖b‖ ^ 2 := by
    have hkey : 0 ≤ (Real.sqrt ε * ‖a‖ - (1 / Real.sqrt ε) * ‖b‖) ^ 2 := sq_nonneg _
    have hs : Real.sqrt ε ^ 2 = ε := Real.sq_sqrt hε.le
    have hs0 : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
    have hinv : (1 / Real.sqrt ε) ^ 2 = 1 / ε := by rw [div_pow, one_pow, hs]
    have hmul : Real.sqrt ε * (1 / Real.sqrt ε) = 1 := by field_simp
    have hexpand : (Real.sqrt ε * ‖a‖ - (1 / Real.sqrt ε) * ‖b‖) ^ 2
        = ε * ‖a‖ ^ 2 - 2 * (‖a‖ * ‖b‖) + (1 / ε) * ‖b‖ ^ 2 := by
      have hring : (Real.sqrt ε * ‖a‖ - (1 / Real.sqrt ε) * ‖b‖) ^ 2
          = Real.sqrt ε ^ 2 * ‖a‖ ^ 2
            - 2 * (Real.sqrt ε * (1 / Real.sqrt ε)) * (‖a‖ * ‖b‖)
            + (1 / Real.sqrt ε) ^ 2 * ‖b‖ ^ 2 := by ring
      rw [hring, hs, hinv, hmul]; ring
    rw [hexpand] at hkey
    linarith
  rw [hexp]
  have hd : (1 + ε) * ‖a‖ ^ 2 + (1 + 1 / ε) * ‖b‖ ^ 2
      = ‖a‖ ^ 2 + ‖b‖ ^ 2 + (ε * ‖a‖ ^ 2 + (1 / ε) * ‖b‖ ^ 2) := by ring
  rw [hd]
  linarith

end Split

section Trace

variable {n : ℕ} {ι : Type*} [DecidableEq ι] {Ω : Type*}
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}
  {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)}

/-- **The chain's martingale coefficient** `V_j = π_j (matToUT A_j⁻¹)` — the `V` of
`StepInputs2.driftInputs_step_chain` and of `DriftStopped2.norm_stoppedV_le`. -/
noncomputable def Vcoef (q : ι → EuclideanSpace ℝ (UT n)) (W : Finset ι)
    (A₀ : EuclideanSpace ℝ (UT n)) (ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)) (j : ℕ) (ω : Ω) :
    EuclideanSpace ℝ (UT n) :=
  (Chain.freeSub q (Chain.chain q W A₀ ξ j ω).2).starProjection
    (Discharge.matToUT (symMat (Chain.chain q W A₀ ξ j ω).1)⁻¹)

/-- `A_{j+1} = lift (preState j)`. -/
theorem chain_succ_eq_lift (j : ℕ) (ω : Ω) :
    (Chain.chain q W A₀ ξ (j + 1) ω).1
      = Chain.lift q W (ChainWiring.preState q W A₀ ξ j ω) := by
  rw [Chain.chain_succ, Chain.stepTo, ChainWiring.preState]

/-- `liftStep j = lift (preState j) − preState j`, the shape `inner_matToUT_lift_sub_nonneg`
consumes. -/
theorem liftStep_eq_lift_sub (j : ℕ) (ω : Ω) :
    StateInvariant.liftStep q W A₀ ξ j ω
      = Chain.lift q W (ChainWiring.preState q W A₀ ξ j ω)
        - ChainWiring.preState q W A₀ ξ j ω := by
  rw [StateInvariant.liftStep, chain_succ_eq_lift]

/-- **The trace term splits** into the martingale increment and the lift's trace cost. -/
theorem trace_incr_eq (j : ℕ) (ω : Ω) :
    ((symMat (Chain.chain q W A₀ ξ j ω).1)⁻¹ * symMat (incr q W A₀ ξ j ω)).trace
      = ⟪Vcoef q W A₀ ξ j ω, ξ j ω⟫
        + ⟪Discharge.matToUT (symMat (Chain.chain q W A₀ ξ j ω).1)⁻¹,
            StateInvariant.liftStep q W A₀ ξ j ω⟫ := by
  rw [Discharge.trace_mul_symMat_eq_inner
      (symMat_isSymm (Chain.chain q W A₀ ξ j ω).1).inv, incr_eq, inner_add_right]
  congr 1
  rw [StateInvariant.gaussStep, Vcoef, StepInputs2.inner_starProjection_swap]

end Trace

section TraceLift

variable {n : ℕ} {ι : Type*} [DecidableEq ι] {Ω : Type*}
variable {xs : ι → (Fin n → ℝ)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}
  {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)}

/-- **The lift's trace cost is non-negative** against `A_j⁻¹`, which is positive semi-definite on
the state bounds.  This is what lets the drift's *upper* accounting be dropped entirely in the
lower direction: the lift can only raise the log-determinant. -/
theorem inner_liftStep_nonneg {m M : ℝ} {j : ℕ} {ω : Ω}
    (hSB : Discharge.StateBounds
      (symMat (Chain.chain (fun i => ChainWiring.qUT (xs i)) W A₀ ξ j ω).1) m M) :
    (0 : ℝ) ≤ ⟪Discharge.matToUT
        (symMat (Chain.chain (fun i => ChainWiring.qUT (xs i)) W A₀ ξ j ω).1)⁻¹,
      StateInvariant.liftStep (fun i => ChainWiring.qUT (xs i)) W A₀ ξ j ω⟫ := by
  rw [liftStep_eq_lift_sub]
  exact ChainErrBudget.inner_matToUT_lift_sub_nonneg (xs := xs) (W := W)
    (symMat_isSymm (Chain.chain (fun i => ChainWiring.qUT (xs i)) W A₀ ξ j ω).1).inv
    (ChainErrBudget.quadForm_inv_nonneg hSB) _

/-- **The pathwise lower bound, final shape.**  `X ≥ c + M − D` with `c = logDet A₀`,
`M = ∑_{j<K} ⟪V_j, ξ_j⟫` the martingale and `D = κ · ∑_{j<K} ‖H_j‖²` the drift proxy.  This is
exactly `ShortfallBound.shortfall_le`'s `hlow`. -/
theorem logDet_chain_ge_martingale {m M r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2) {ω : Ω} (K : ℕ)
    (hSB : ∀ j, j < K → Discharge.StateBounds
      (symMat (Chain.chain (fun i => ChainWiring.qUT (xs i)) W A₀ ξ j ω).1) m M)
    (hop : ∀ j, j < K → ‖Matrix.toEuclideanCLM (𝕜 := ℝ)
      (symMat (incr (fun i => ChainWiring.qUT (xs i)) W A₀ ξ j ω))‖ ≤ r * m) :
    ChainWiring.logDet A₀
        + (∑ j ∈ Finset.range K,
            ⟪Vcoef (fun i => ChainWiring.qUT (xs i)) W A₀ ξ j ω, ξ j ω⟫)
        - ((1 / 2 + 2 * r) / m ^ 2)
            * (∑ j ∈ Finset.range K,
                ‖incr (fun i => ChainWiring.qUT (xs i)) W A₀ ξ j ω‖ ^ 2)
      ≤ ChainWiring.logDet
          (Chain.chain (fun i => ChainWiring.qUT (xs i)) W A₀ ξ K ω).1 := by
  have hsplit := logDet_chain_ge_split (q := fun i => ChainWiring.qUT (xs i)) (W := W)
    (A₀ := A₀) (ξ := ξ) (m := m) (M := M) hr0 hr (ω := ω) K hSB hop
  have hmono : ∑ j ∈ Finset.range K,
        ⟪Vcoef (fun i => ChainWiring.qUT (xs i)) W A₀ ξ j ω, ξ j ω⟫
      ≤ ∑ j ∈ Finset.range K,
        ((symMat (Chain.chain (fun i => ChainWiring.qUT (xs i)) W A₀ ξ j ω).1)⁻¹
          * symMat (incr (fun i => ChainWiring.qUT (xs i)) W A₀ ξ j ω)).trace := by
    refine Finset.sum_le_sum fun j hj => ?_
    rw [trace_incr_eq]
    have := inner_liftStep_nonneg (xs := xs) (W := W) (A₀ := A₀) (ξ := ξ)
      (hSB j (Finset.mem_range.1 hj))
    linarith
  linarith

end TraceLift

end D5.S3.Arith.Lattices.Klartag.Drift.LogDetChainLower
