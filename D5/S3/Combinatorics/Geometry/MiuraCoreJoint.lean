/- GID: D5/S3/Combinatorics/Geometry/MiuraCoreJoint
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/MiuraCoreJoint
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Signed row and column deletion commute on the same actual array. -/

module

public import D5.S3.Combinatorics.Geometry.MiuraCoreTranspose

/-! Joint signed contractions retain both physical axes. -/

@[expose] public section
namespace D5.S3.Combinatorics.Geometry.MiuraCoreJoint
open MiuraHeightEnvelope MiuraResidualCount MiuraCoreColumns MiuraCoreContract
  MiuraCoreCellExpand MiuraCoreResidual MiuraCoreReduction MiuraSlabIncidence
  MiuraCoreTranspose

variable {m n : ℕ}

/-- Signed row contraction is the same column operation on the actual transpose. -/
noncomputable def contractRow (h : Cell m n → ℤ) (hn : 0 < n)
    (i : Fin m) (hi : frozenColumn (transposeHeight h) i) : Cell (m - 1) n → ℤ :=
  transposeHeight (contractAt (transposeHeight h) hn i hi)

/-- Deleting a frozen column leaves a frozen row legal on the very same array. -/
theorem frozen_row_after_column (h : Cell m n → ℤ) (hm : 0 < m)
    (j : Fin n) (hj : frozenColumn h j)
    (i : Fin m) (hi : frozenColumn (transposeHeight h) i) :
    frozenColumn (transposeHeight (contractAt h hm j hj)) i := by
  obtain ⟨hi0, hi1, hisym⟩ := hi
  refine ⟨hi0, hi1, ?_⟩
  intro q
  by_cases hq : q.val < j.val
  · simpa only [transposeHeight, contractAt, hq, ite_true] using
      hisym ⟨q.val, by have := q.isLt; omega⟩
  · have hs := hisym ⟨q.val + 1, by have := q.isLt; omega⟩
    dsimp only [transposeHeight] at hs
    simp only [transposeHeight, contractAt, hq, ite_false]
    omega

/-- The transposed statement retains every original frozen column after row deletion. -/
theorem frozen_column_after_row (h : Cell m n → ℤ) (hn : 0 < n)
    (i : Fin m) (hi : frozenColumn (transposeHeight h) i)
    (j : Fin n) (hj : frozenColumn h j) :
    frozenColumn (contractRow h hn i hi) j :=
  frozen_row_after_column (transposeHeight h) hn i hi j hj

private theorem row_slope_after_column (h : Cell m n → ℤ) (hm : 0 < m)
    (j : Fin n) (hj : frozenColumn h j)
    (i : Fin m) (hi : frozenColumn (transposeHeight h) i) (hn : 0 < n)
    (hn' : 0 < n - 1) :
    frozenSlope (transposeHeight (contractAt h hm j hj)) hn' i
      (frozen_row_after_column h hm j hj i hi) =
    frozenSlope (transposeHeight h) hn i hi := by
  have hj0 := hj.1
  simp only [frozenSlope, transposeHeight, contractAt,
    show (0 : ℕ) < j.val from hj0, ite_true]

private theorem column_slope_after_row (h : Cell m n → ℤ) (hn : 0 < n)
    (i : Fin m) (hi : frozenColumn (transposeHeight h) i)
    (j : Fin n) (hj : frozenColumn h j) (hm : 0 < m) (hm' : 0 < m - 1) :
    frozenSlope (contractRow h hn i hi) hm' j
      (frozen_column_after_row h hn i hi j hj) = frozenSlope h hm j hj :=
  row_slope_after_column (transposeHeight h) hn i hi j hj hm hm'

/-- Both orders of a legal row and column deletion give exactly the same function. -/
theorem contract_row_column_commute (h : Cell m n → ℤ)
    (hm : 0 < m) (hn : 0 < n)
    (i : Fin m) (hi : frozenColumn (transposeHeight h) i)
    (j : Fin n) (hj : frozenColumn h j) :
    contractAt (contractRow h hn i hi) (by have := hi.1; have := hi.2.1; omega) j
        (frozen_column_after_row h hn i hi j hj) =
      contractRow (contractAt h hm j hj) (by have := hj.1; have := hj.2.1; omega) i
        (frozen_row_after_column h hm j hj i hi) := by
  have hm' : 0 < m - 1 := by have := hi.1; have := hi.2.1; omega
  have hn' : 0 < n - 1 := by have := hj.1; have := hj.2.1; omega
  have hsR := row_slope_after_column h hm j hj i hi hn hn'
  have hsC := column_slope_after_row h hn i hi j hj hm hm'
  funext p
  change (if p.2.val < j.val then _ else _ - frozenSlope _ _ _ _) = _
  simp only [hsC]
  change (if p.2.val < j.val then _ else _ - frozenSlope h hm j hj) =
    (if p.1.val < i.val then _ else _ - frozenSlope _ _ _ _)
  simp only [hsR]
  dsimp only [contractRow, transposeHeight, contractAt]
  split_ifs <;> ring

/-- A legal signed row deletion preserves the exact residual class. -/
theorem contractRow_residual (a b : ℕ) (h : Cell m n → ℤ) (hn : 0 < n)
    (i : Fin m) (hi : frozenColumn (transposeHeight h) i) (hr : Residual a b h) :
    Residual a b (contractRow h hn i hi) :=
  transpose_residual a b _ (contractAt_residual a b _ hn i hi (transpose_residual a b h hr))

/-- Every step acts on the actual preceding rectangle. -/
inductive JointReduction :
    {m n : ℕ} → (Cell m n → ℤ) → {M N : ℕ} → (Cell M N → ℤ) → Prop where
  | refl {m n : ℕ} (h : Cell m n → ℤ) : JointReduction h h
  | column {m n M N : ℕ} (h : Cell m n → ℤ) (hm : 0 < m) (j k : Fin n)
      (hj : frozenColumn h j) (hk : frozenColumn h k) (hjk : j.val + 1 = k.val)
      {g : Cell M N → ℤ} (tail : JointReduction (contractAt h hm j hj) g) :
      JointReduction h g
  | row {m n M N : ℕ} (h : Cell m n → ℤ) (hn : 0 < n) (i k : Fin m)
      (hi : frozenColumn (transposeHeight h) i) (hk : frozenColumn (transposeHeight h) k)
      (hik : i.val + 1 = k.val)
      {g : Cell M N → ℤ} (tail : JointReduction (contractRow h hn i hi) g) :
      JointReduction h g

private theorem column_chain_joint {m n N : ℕ} {h : Cell m n → ℤ}
    {g : Cell m N → ℤ} (hc : ColumnReduction h g) : JointReduction h g := by
  induction hc with
  | refl h => exact .refl h
  | step h hm j k hj hk hjk tail ih => exact .column h hm j k hj hk hjk ih

private theorem column_chain_transpose_joint {m n N : ℕ} {h : Cell m n → ℤ}
    {g : Cell m N → ℤ} (hc : ColumnReduction h g) :
    JointReduction (transposeHeight h) (transposeHeight g) := by
  induction hc with
  | refl h => exact .refl _
  | step h hm j k hj hk hjk tail ih =>
    exact .row (transposeHeight h) hm j k hj hk hjk ih

private theorem joint_trans {m n M N P Q : ℕ} {h : Cell m n → ℤ}
    {g : Cell M N → ℤ} {f : Cell P Q → ℤ}
    (hh : JointReduction h g) (hg : JointReduction g f) : JointReduction h f := by
  induction hh with
  | refl _ => exact hg
  | column h hm j k hj hk hjk tail ih => exact .column h hm j k hj hk hjk (ih hg)
  | row h hn i k hi hk hik tail ih => exact .row h hn i k hi hk hik (ih hg)

/-- One actual residual core simultaneously has both required finite dimension bounds. -/
theorem residual_joint_bounded_core_exists (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (h : Cell m n → ℤ) (hm : 2 ≤ m) (hn : 2 ≤ n) (hr : Residual a b h) :
    ∃ (M N : ℕ) (g : Cell M N → ℤ),
      2 ≤ M ∧ M ≤ 2 * (a + b) - 1 ∧ 2 ≤ N ∧ N ≤ 2 * (a + b) - 1 ∧
        JointReduction h g ∧ Residual a b g := by
  obtain ⟨N, g, hNlo, hNhi, hcol, hg⟩ :=
    residual_column_core_exists a b ha hb (by omega) h hn hr
  obtain ⟨M, f, hMlo, hMhi, hrow, hf⟩ :=
    residual_column_core_exists a b ha hb (by omega) (transposeHeight g) hm
      (transpose_residual a b g hg)
  refine ⟨M, N, transposeHeight f, hMlo, hMhi, hNlo, hNhi, ?_,
    transpose_residual a b f hf⟩
  exact joint_trans (column_chain_joint hcol) (column_chain_transpose_joint hrow)

end D5.S3.Combinatorics.Geometry.MiuraCoreJoint
