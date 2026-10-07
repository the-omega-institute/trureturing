/- GID: D5/S3/Arith/Lattices/Klartag/Walk/ChainWalk
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Walk/ChainWalk
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Gaussian matrix walk, filtration and stopped increments. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.State.PaddingMap
import D5.S3.Arith.Lattices.Klartag.Walk.Chain
import D5.S3.Arith.Lattices.Klartag.Walk.ChainWiring
open D5.S3.Arith.Lattices.Klartag.Completion
open D5.S3.Arith.Lattices.Klartag.Construction
open D5.S3.Arith.Lattices.Klartag.Contact
open D5.S3.Arith.Lattices.Klartag.Gaussian
open D5.S3.Arith.Lattices.Klartag.State
open D5.S3.Arith.Lattices.Klartag.Walk

namespace D5.S3.Arith.Lattices.Klartag
open MeasureTheory
open Set
open Real
open D5.S3.Arith.Lattices.Klartag.Walk.Chain
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {ι : Type*} [DecidableEq ι] {Ω : Type*}

/-- The **pure** constraint walk: `⟪A₀, q j⟫` plus the martingale increments only, with the
one-sided lift dropped. -/
noncomputable def pureWalk (q : ι → E) (W : Finset ι) (A₀ : E) (ξ : ℕ → Ω → E) (j : ι) :
    ℕ → Ω → ℝ
  | 0, _ => ⟪A₀, q j⟫
  | k + 1, ω => pureWalk q W A₀ ξ j k ω
      + ⟪(freeSub q (chain q W A₀ ξ k ω).2).starProjection (ξ k ω), q j⟫

variable {q : ι → E} {W : Finset ι} {A₀ : E} {ξ : ℕ → Ω → E}

/-- **The chain's defining equation.**  Along one step the constraint value `⟪A_k, q j⟫` moves by
the martingale increment `⟪π_k ξ_k, q j⟫` plus the one-sided lift term. -/
theorem constraint_walk_eq (j : ι) (k : ℕ) (ω : Ω) :
    ⟪(chain q W A₀ ξ (k + 1) ω).1, q j⟫
      = ⟪(chain q W A₀ ξ k ω).1, q j⟫
        + ⟪(freeSub q (chain q W A₀ ξ k ω).2).starProjection (ξ k ω), q j⟫
        + ∑ i ∈ violated q W ((chain q W A₀ ξ k ω).1
              + (freeSub q (chain q W A₀ ξ k ω).2).starProjection (ξ k ω)),
            ((1 - ⟪(chain q W A₀ ξ k ω).1
              + (freeSub q (chain q W A₀ ξ k ω).2).starProjection (ξ k ω), q i⟫)
              / ‖q i‖ ^ 2) * ⟪q i, q j⟫ := by
  rw [chain_succ, stepTo, inner_lift, inner_add_left]

/-- **The lift is one-sided.**  Every summand is non-negative, because a violated constraint has
`⟪A', q i⟫ < 1` and the constraint vectors are non-negatively correlated. -/
theorem lift_term_nonneg (j : ι) (A' : E)
    (hq : ∀ i ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) :
    (0 : ℝ) ≤ ∑ i ∈ violated q W A', ((1 - ⟪A', q i⟫) / ‖q i‖ ^ 2) * ⟪q i, q j⟫ := by
  refine Finset.sum_nonneg fun i hi => ?_
  obtain ⟨hiW, hilt⟩ := mem_violated.1 hi
  exact mul_nonneg (div_nonneg (by linarith) (sq_nonneg _)) (hq i hiW)

/-- **The pure walk is below the constraint value.**  The lift only pushes constraints up. -/
theorem pureWalk_le (j : ι) (hq : ∀ i ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (k : ℕ) (ω : Ω) :
    pureWalk q W A₀ ξ j k ω ≤ ⟪(chain q W A₀ ξ k ω).1, q j⟫ := by
  induction k with
  | zero => exact le_of_eq rfl
  | succ k ih =>
    rw [constraint_walk_eq j k ω]
    have h := lift_term_nonneg (q := q) (W := W) j
      ((chain q W A₀ ξ k ω).1
        + (freeSub q (chain q W A₀ ξ k ω).2).starProjection (ξ k ω)) hq
    show pureWalk q W A₀ ξ j k ω
        + ⟪(freeSub q (chain q W A₀ ξ k ω).2).starProjection (ξ k ω), q j⟫ ≤ _
    linarith

/-- **The containment.**  If `j` is active at step `k`, the *pure* walk has already reached the
boundary `1` by step `k` — so the contact event sits inside the padded walk's hitting event. -/
theorem pureWalk_le_one_of_mem (j : ι) (hq : ∀ i ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) :
    ∀ (k : ℕ) (ω : Ω), j ∈ (chain q W A₀ ξ k ω).2 →
      ∃ i ≤ k, pureWalk q W A₀ ξ j i ω ≤ 1 := by
  intro k
  induction k with
  | zero => intro ω hj; simp at hj
  | succ k ih =>
    intro ω hj
    rw [chain_snd_succ_eq] at hj
    rcases Finset.mem_union.1 hj with h | h
    · obtain ⟨i, hik, hle⟩ := ih ω h
      exact ⟨i, le_trans hik (Nat.le_succ k), hle⟩
    · refine ⟨k + 1, le_rfl, ?_⟩
      obtain ⟨_, hlt⟩ := mem_violated.1 h
      have hdom := pureWalk_le (q := q) (W := W) (A₀ := A₀) (ξ := ξ) j hq k ω
      show pureWalk q W A₀ ξ j k ω
          + ⟪(freeSub q (chain q W A₀ ξ k ω).2).starProjection (ξ k ω), q j⟫ ≤ 1
      rw [inner_add_left] at hlt
      linarith

/-- The pure walk's increment, read against the increment: the projection is self-adjoint, so the
martingale increment is `⟪ξ_k, π_k (q j)⟫` — an inner product against a **past-measurable**
vector, which is what `PaddingMap.padInc` consumes. -/
theorem pureWalk_succ_sub (j : ι) (k : ℕ) (ω : Ω) :
    pureWalk q W A₀ ξ j (k + 1) ω - pureWalk q W A₀ ξ j k ω
      = ⟪ξ k ω, (freeSub q (chain q W A₀ ξ k ω).2).starProjection (q j)⟫ := by
  show (pureWalk q W A₀ ξ j k ω
      + ⟪(freeSub q (chain q W A₀ ξ k ω).2).starProjection (ξ k ω), q j⟫)
    - pureWalk q W A₀ ξ j k ω = _
  rw [add_sub_cancel_left]
  exact (freeSub q (chain q W A₀ ξ k ω).2).starProjection_isSymmetric (ξ k ω) (q j)

/-- The chain's scalar martingale for a window point, normalised so that the constraint's
boundary is `0`.  `M_0 = ⟪A₀, q j⟫ − 1` is Klartag's initial gap, eq. (61). -/
noncomputable def constraintM (q : ι → E) (W : Finset ι) (A₀ : E) (ξ : ℕ → Ω → E)
    (j : ι) (k : ℕ) (ω : Ω) : ℝ := pureWalk q W A₀ ξ j k ω - 1

theorem constraintM_zero (j : ι) (ω : Ω) :
    constraintM q W A₀ ξ j 0 ω = ⟪A₀, q j⟫ - 1 := rfl

/-- **The containment, in `TailTransport.tail_at_step_μ`'s shape.** -/
theorem chain_hhit (hq : ∀ j : ι, ∀ i ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (k : ℕ) (y : ι) :
    {ω : Ω | y ∈ (chain q W A₀ ξ k ω).2}
      ⊆ {ω : Ω | ∃ i ≤ k, constraintM q W A₀ ξ y i ω ≤ 0} := by
  intro ω hω
  obtain ⟨i, hik, hle⟩ := pureWalk_le_one_of_mem (q := q) (W := W) (A₀ := A₀) (ξ := ξ)
    y (hq y) k ω hω
  exact ⟨i, hik, by simpa [constraintM] using hle⟩

theorem chain_hgap {y : ι} (hA₀ : (1 : ℝ) < ⟪A₀, q y⟫) (ω : Ω) :
    0 < constraintM q W A₀ ξ y 0 ω := by
  rw [constraintM_zero]; linarith

section Assembly

open D5.S3.Arith.Lattices.Klartag.Construction.Tiling
open D5.S3.Arith.Lattices.Klartag.Construction.Section5
open D5.S3.Arith.Lattices.Klartag.Construction.ConstructionA
open D5.S3.Arith.Lattices.Klartag.Walk.ChainDataInst
open scoped ENNReal

variable {n : ℕ} {Ωc : Type*} [MeasurableSpace Ωc] {P : Measure Ωc} [IsProbabilityMeasure P]
variable {Ec : Type*} [NormedAddCommGroup Ec] [InnerProductSpace ℝ Ec] [FiniteDimensional ℝ Ec]

/-- Abbreviation: the chain's accumulated contact set. -/
noncomputable def contactSet (q : (Fin n → ℤ) → Ec) (W : Finset (Fin n → ℤ)) (A₀ : Ec)
    (ξ : ℕ → Ωc → Ec) (k : ℕ) (ω : Ωc) : Finset (Fin n → ℤ) := (chain q W A₀ ξ k ω).2

variable {q : (Fin n → ℤ) → Ec} {W : Finset (Fin n → ℤ)} {A₀ : Ec} {ξ : ℕ → Ωc → Ec} {α : ℝ}

end Assembly

end D5.S3.Arith.Lattices.Klartag
