/- GID: D5/S3/Arith/Lattices/Klartag/Completion/Discharge
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Completion/Discharge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform constants and completion of lattice packing. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Completion.Assembly
import D5.S3.Arith.Lattices.Klartag.Completion.Final
import D5.S3.Arith.Lattices.Klartag.Walk.StepInputs2

set_option linter.unusedSectionVars false

open D5.S3.Arith.Lattices.Klartag.Completion
open D5.S3.Arith.Lattices.Klartag.Construction
open D5.S3.Arith.Lattices.Klartag.Gaussian
open D5.S3.Arith.Lattices.Klartag.Walk

namespace D5.S3.Arith.Lattices.Klartag.Completion.Discharge

open MeasureTheory
open Matrix
open Metric
open Finset
open Module
open ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace
open D5.S3.Arith.Lattices.Klartag
open D5.S3.Arith.Lattices.Klartag.Walk.Increments

variable {n : ℕ}

/-- The coordinate vector of a symmetric matrix — the inverse of `Increments.symMat`. -/
noncomputable def matToUT (M : Matrix (Fin n) (Fin n) ℝ) : EuclideanSpace ℝ (UT n) :=
  WithLp.toLp 2 fun p => M p.1.1 p.1.2 / cc p

@[simp] theorem matToUT_apply (M : Matrix (Fin n) (Fin n) ℝ) (p : UT n) :
    (matToUT M) p = M p.1.1 p.1.2 / cc p := rfl

theorem symMat_matToUT {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.IsSymm) (i j : Fin n) :
    symMat (matToUT M) i j = M i j := by
  rw [symMat_apply, matToUT_apply, mul_comm, div_mul_cancel₀ _ (ChainWiring.cc_ne_zero _)]
  rcases le_total i j with h | h
  · rw [up_of_le h]
  · rw [up_comm, up_of_le h]
    exact hM.apply i j

/-- `tr(B H) = ∑_{i,j} B_ij H_ij` for symmetric `H`: the trace term of the one-step inequality is
a Frobenius inner product. -/
theorem trace_mul_eq_frobenius {B H : Matrix (Fin n) (Fin n) ℝ} (hH : H.IsSymm) :
    (B * H).trace = ∑ i, ∑ j, B i j * H i j := by
  rw [Matrix.trace]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hH.apply i j]

/-- **The trace term as an inner product.**  With `H = symMat u` the step's increment and `B` a
symmetric matrix, `tr(B H) = ⟪matToUT B, u⟫` — the form `driftInputs_step_chain`'s `V` takes. -/
theorem trace_mul_symMat_eq_inner {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.IsSymm)
    (u : EuclideanSpace ℝ (UT n)) : (B * symMat u).trace = ⟪matToUT B, u⟫ := by
  rw [trace_mul_eq_frobenius (symMat_isSymm u), ← sum_symMat_mul_eq_inner (matToUT B) u]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
    rw [symMat_matToUT hB]

section GoodEventChain

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

def chainGood (G : Ω → Matrix (Fin n) (Fin n) ℝ) (r : ℝ)
    (ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)) (N : ℕ) (η : ℝ) : Set Ω :=
  GoodEvent.goodEvent G r ∩ StepInputs2.stepGood ξ N η

end GoodEventChain

theorem card_UT_le_sq {n : ℕ} (hn : 1 ≤ n) : (Fintype.card (UT n) : ℝ) ≤ (n : ℝ) ^ 2 := by
  have hnat : Fintype.card (UT n) ≤ n * n := by
    rw [ChainWiring.card_UT]
    refine Nat.div_le_of_le_mul ?_
    have : n + 1 ≤ 2 * n := by omega
    calc n * (n + 1) ≤ n * (2 * n) := Nat.mul_le_mul_left _ this
      _ = 2 * (n * n) := by ring
  have := (Nat.cast_le (α := ℝ)).2 hnat
  calc (Fintype.card (UT n) : ℝ) ≤ ((n * n : ℕ) : ℝ) := this
    _ = (n : ℝ) ^ 2 := by push_cast; ring

section Hpt

theorem symMat_add (x y : EuclideanSpace ℝ (UT n)) :
    symMat (x + y) = symMat x + symMat y := by
  ext i j
  simp only [symMat_apply, Matrix.add_apply]
  have : (x + y) (up i j) = x (up i j) + y (up i j) := rfl
  rw [this]
  ring

theorem sum_sq_symMat (u : EuclideanSpace ℝ (UT n)) :
    ∑ i, ∑ j, (symMat u i j) ^ 2 = ‖u‖ ^ 2 := by
  have h := sum_symMat_mul_eq_inner u u
  rw [real_inner_self_eq_norm_sq] at h
  rw [← h]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- **The chain's state invariant on the good event.**  `A_k` is positive definite with a uniform
lower bound `m` on its quadratic form, a uniform upper bound `M` on its operator norm, and a
symmetric congruence factor `S` with `S A_k S = 1`. -/
structure StateBounds (A : Matrix (Fin n) (Fin n) ℝ) (m M : ℝ) : Prop where
  posDef : A.PosDef
  mpos : 0 < m
  lower : ∀ x : EuclideanSpace ℝ (Fin n),
    m * ‖x‖ ^ 2 ≤ ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) A x⟫
  Mpos : 0 < M
  upper : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖ ≤ M
  congr : ∃ S : Matrix (Fin n) (Fin n) ℝ, S.IsHermitian ∧ S * A * S = 1

variable {Ω : Type*} {ι : Type*} [DecidableEq ι] {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι}
  {A₀ : EuclideanSpace ℝ (UT n)} {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)}

/-- **`hpt` for one step and one path.**  With `V k ω = π_k (A_k⁻¹)` and
`c = 1 / (2 M² (1+δ)²)`, this is exactly the inequality
`StepInputs2.driftInputs_step_chain` consumes. -/
theorem hpt_step {k : ℕ} {ω : Ω} {m M δ η : ℝ}
    (hSB : StateBounds (symMat (Chain.chain q W A₀ ξ k ω).1) m M)
    (hη : ‖Matrix.toEuclideanCLM (𝕜 := ℝ)
      (symMat ((Chain.freeSub q (Chain.chain q W A₀ ξ k ω).2).starProjection (ξ k ω)))‖ ≤ η)
    (hδ : η / m ≤ δ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    ChainWiring.logDet (Chain.chain q W A₀ ξ (k + 1) ω).1
      ≤ ChainWiring.logDet (Chain.chain q W A₀ ξ k ω).1
        + ⟪(Chain.freeSub q (Chain.chain q W A₀ ξ k ω).2).starProjection
            (matToUT (symMat (Chain.chain q W A₀ ξ k ω).1)⁻¹), ξ k ω⟫
        - (1 / (2 * M ^ 2 * (1 + δ) ^ 2))
          * ‖(Chain.freeSub q (Chain.chain q W A₀ ξ k ω).2).starProjection (ξ k ω)‖ ^ 2
        + ChainWiring.chainErr q W A₀ ξ k ω := by
  obtain ⟨S, hSherm, hSA⟩ := hSB.congr
  set A := symMat (Chain.chain q W A₀ ξ k ω).1 with hA
  set u := (Chain.freeSub q (Chain.chain q W A₀ ξ k ω).2).starProjection (ξ k ω) with hu
  have hAsymm : A.IsSymm := symMat_isSymm _
  have hH : (symMat u).IsHermitian := Matrix.isHermitian_iff_isSymm.2 (symMat_isSymm u)
  have hstep := StepInputs2.log_det_step_unconj hSB.posDef hSherm hSA hH hSB.mpos hSB.lower hη
    hδ hδ0 hδ1 hSB.upper hSB.Mpos
  have hsplit : ChainWiring.logDet (Chain.chain q W A₀ ξ (k + 1) ω).1
      = ChainWiring.logDet (ChainWiring.preState q W A₀ ξ k ω)
        + ChainWiring.chainErr q W A₀ ξ k ω := ChainWiring.logDet_chain_succ k ω
  have hpre : ChainWiring.logDet (ChainWiring.preState q W A₀ ξ k ω)
      = Real.log (A + symMat u).det := by
    rw [ChainWiring.logDet, ChainWiring.preState, symMat_add]
  have htr : (A⁻¹ * symMat u).trace
      = ⟪(Chain.freeSub q (Chain.chain q W A₀ ξ k ω).2).starProjection (matToUT A⁻¹), ξ k ω⟫ := by
    rw [trace_mul_symMat_eq_inner hAsymm.inv u, hu,
      StepInputs2.inner_starProjection_swap]
  have hfrob : (∑ i, ∑ j, (symMat u i j) ^ 2) / (2 * M ^ 2 * (1 + δ) ^ 2)
      = (1 / (2 * M ^ 2 * (1 + δ) ^ 2)) * ‖u‖ ^ 2 := by
    rw [sum_sq_symMat u]
    ring
  have hlogA : ChainWiring.logDet (Chain.chain q W A₀ ξ k ω).1 = Real.log A.det := rfl
  rw [hsplit, hpre, hlogA]
  rw [htr, hfrob] at hstep
  linarith [hstep.2]

end Hpt

section Residual

variable {Ω : Type*} [MeasurableSpace Ω] {ι : Type*} [DecidableEq ι]

end Residual

end D5.S3.Arith.Lattices.Klartag.Completion.Discharge
