/- GID: D5/S3/Combinatorics/Geometry/MiuraPolynomialCoreSum
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/MiuraPolynomialCoreSum
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Actual finite residual cores determine one rational run-vector sum polynomial. -/

module

public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Basic.Finite.Sigma
public import D5.S3.Combinatorics.Geometry.MiuraCoreNormal
public import D5.S3.Combinatorics.Geometry.MiuraPolynomialRuns
public import D5.S3.Combinatorics.Geometry.MiuraEqualityClassification
import all D5.S3.Combinatorics.Geometry.MiuraCoreTranspose

/-! The concrete finite-core polynomial candidate and its exact vector-sum evaluation. -/

@[expose] public section
namespace D5.S3.Combinatorics.Geometry.MiuraPolynomialCoreSum
open MiuraHeightEnvelope MiuraResidualCount MiuraCoreColumns MiuraCoreResidual
  MiuraCoreFrozenWalk MiuraCoreBoundary MiuraCoreNormal MiuraSlabIncidence MiuraCoreTranspose
  MiuraRunCompositions MiuraPolynomialRuns
open MiuraSlabNeutral MiuraSlabRunBound MiuraEqualityClassification
open private transpose_min_iff transpose_max_iff
  from D5.S3.Combinatorics.Geometry.MiuraCoreTranspose
open scoped BigOperators

/-- Every member is an individual normalized residual core with both run counts positive. -/
def CoreState (a b M N : ℕ) :=
  {h : Cell M N → ℤ // 2 ≤ M ∧ 2 ≤ N ∧ Residual a b h ∧
    NoAdjacentFrozen h ∧ NoAdjacentFrozen (transposeHeight h) ∧
      1 ≤ numFrozenRuns (transposeHeight h) ∧ 1 ≤ numFrozenRuns h}

instance core_state_finite (a b M N : ℕ) : Finite (CoreState a b M N) := by
  classical
  by_cases hm : 2 ≤ M
  · by_cases hn : 2 ≤ N
    · change ({h : Cell M N → ℤ | 2 ≤ M ∧ 2 ≤ N ∧ Residual a b h ∧
        NoAdjacentFrozen h ∧ NoAdjacentFrozen (transposeHeight h) ∧
          1 ≤ numFrozenRuns (transposeHeight h) ∧ 1 ≤ numFrozenRuns h} : Set _).Finite
      exact (residual_finite a b (by omega) (by omega)).subset fun _ hh => hh.2.2.1
    · haveI : IsEmpty (CoreState a b M N) := ⟨fun h => hn h.property.2.1⟩
      infer_instance
  · haveI : IsEmpty (CoreState a b M N) := ⟨fun h => hm h.property.1⟩
    infer_instance

/-- Both finite dimensions and every exact core function are retained individually. -/
def Core (a b : ℕ) :=
  Σ M : Fin (2 * (a + b)), Σ N : Fin (2 * (a + b)), CoreState a b M.val N.val

noncomputable instance core_fintype (a b : ℕ) : Fintype (Core a b) := by
  unfold Core
  exact @Sigma.instFintype _ _
    (fun M => @Sigma.instFintype _ _
      (fun N => @Fintype.ofFinite _ (core_state_finite a b M.val N.val)) inferInstance)
    inferInstance

noncomputable def rowOccupied {a b : ℕ} (K : Core a b) : ℕ :=
  numActiveColumns (transposeHeight K.2.2.val)

noncomputable def colOccupied {a b : ℕ} (K : Core a b) : ℕ :=
  numActiveColumns K.2.2.val

noncomputable def rowRuns {a b : ℕ} (K : Core a b) : ℕ :=
  numFrozenRuns (transposeHeight K.2.2.val)

noncomputable def colRuns {a b : ℕ} (K : Core a b) : ℕ :=
  numFrozenRuns K.2.2.val

private theorem axis_budget {M N : ℕ} (a b : ℕ) (h : Cell M N → ℤ)
    (hm : 2 ≤ M) (hn : 2 ≤ N) (hr : Residual a b h) :
    numActiveColumns h + numFrozenRuns h ≤ 2 * (a + b) - 1 := by
  have hd : numExtrema h ≤ a + b := by
    simpa only [hr.2.1, hr.2.2.1] using numExtrema_le_split h
  have ha := (numActiveColumns_le_numExtrema h).trans hd
  have he := boundary_columns_active h hr.1.1 (by omega) hn
  have hb := numFrozenRuns_le h (by omega) he.1 he.2
  omega

private theorem core_budgets {a b : ℕ} (K : Core a b) :
    rowOccupied K + rowRuns K ≤ 2 * (a + b) - 1 ∧
      colOccupied K + colRuns K ≤ 2 * (a + b) - 1 := by
  obtain ⟨hm, hn, hr, _, _, _, _⟩ := K.2.2.property
  exact ⟨axis_budget a b _ hn hm (transpose_residual a b _ hr), axis_budget a b _ hm hn hr⟩

/-- The single rational polynomial is chosen from the exact finite cores before dimensions. -/
noncomputable def corePolynomial (a b : ℕ) : MvPolynomial (Fin 2) ℚ :=
  ∑ K : Core a b, jointRunPolynomial (rowOccupied K) (colOccupied K) (rowRuns K) (colRuns K)

/-- This evaluation counts positive vectors over all individual actual cores. -/
theorem core_polynomial_eval (a b m n : ℕ)
    (hm : 2 * (a + b) - 1 ≤ m) (hn : 2 * (a + b) - 1 ≤ n) :
    MvPolynomial.eval (fun i : Fin 2 => if i = 0 then (m : ℚ) else (n : ℚ))
      (corePolynomial a b) =
    ∑ K : Core a b,
      (Nat.card (PositiveLengths (m - rowOccupied K) (rowRuns K) ×
        PositiveLengths (n - colOccupied K) (colRuns K)) : ℚ) := by
  classical
  rw [corePolynomial, map_sum]
  apply Finset.sum_congr rfl
  intro K _
  obtain ⟨_, _, _, _, _, hr, hs⟩ := K.2.2.property
  exact joint_run_polynomial_eval _ _ _ _ m n hr hs
    ((core_budgets K).1.trans hm) ((core_budgets K).2.trans hn)

private theorem occupied_transpose_iff {M N : ℕ} (h : Cell M N → ℤ) (i : Fin M) :
    activeColumn (transposeHeight h) i ↔ RowOccupied h i := by
  simp only [activeColumn, IsStrictLocalExtremum, RowOccupied,
    transpose_min_iff, transpose_max_iff]
  exact exists_congr fun _ => or_comm

private theorem run_count_eq {M N : ℕ} (h : Cell M N → ℤ) :
    numFrozenRuns (transposeHeight h) = (frozenRowRunStarts h).card := by
  classical
  unfold numFrozenRuns frozenRowRunStarts
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    frozenRunStart, FrozenRowRunStart, occupied_transpose_iff]
  aesop

private theorem core_runs_strict {a b : ℕ} (K : Core a b) (hd : 5 ≤ a + b) :
    rowRuns K + colRuns K ≤ a + b - 1 := by
  classical
  obtain ⟨hm, hn, hr, _, _, hrow, hcol⟩ := K.2.2.property
  have hex : ∀ {M N : ℕ} (h : Cell M N → ℤ),
      1 ≤ numFrozenRuns (transposeHeight h) → ∃ i, ¬ RowOccupied h i := by
    intro M N h hp
    rw [run_count_eq] at hp
    obtain ⟨i, hi⟩ := Finset.card_pos.mp hp
    exact ⟨i, (Finset.mem_filter.mp hi).2.1⟩
  have hbound := residual_frozen_runs_strict hm hn hd rfl hr
    (hex _ hrow) (hex (transposeHeight K.2.2.val) hcol)
  change numFrozenRuns (transposeHeight K.2.2.val) + numFrozenRuns K.2.2.val ≤ _
  have he : numFrozenRuns K.2.2.val =
      (frozenRowRunStarts (transposeHeight K.2.2.val)).card :=
    run_count_eq (transposeHeight K.2.2.val)
  rw [run_count_eq K.2.2.val, he]
  exact hbound

/-- The strict actual geometry of these same residual cores gives the original degree bound. -/
theorem core_polynomial_degree_le (a b : ℕ) (hd : 5 ≤ a + b) :
    (corePolynomial a b).totalDegree ≤ a + b - 3 := by
  classical
  apply MvPolynomial.totalDegree_finsetSum_le
  intro K _
  obtain ⟨_, _, _, _, _, hr, hs⟩ := K.2.2.property
  have hb := core_runs_strict K hd
  apply (joint_run_polynomial_degree_le _ _ _ _ hr hs).trans
  change rowRuns K + colRuns K - 2 ≤ a + b - 3
  omega

end D5.S3.Combinatorics.Geometry.MiuraPolynomialCoreSum
