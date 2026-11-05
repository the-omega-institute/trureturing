/- GID: D5/S3/Combinatorics/Geometry/MiuraCoreStretch
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/MiuraCoreStretch
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Every frozen run permits arbitrary actual residual-preserving length expansion. -/

module

public import D5.S3.Combinatorics.Geometry.MiuraCoreRestore
import all D5.S3.Combinatorics.Geometry.MiuraCoreJoint

/-! Positive frozen-run enlargement uses the actual common signed slope. -/

@[expose] public section
namespace D5.S3.Combinatorics.Geometry.MiuraCoreStretch
open MiuraHeightEnvelope MiuraResidualCount MiuraCoreColumns MiuraCoreContract
  MiuraCoreCellExpand MiuraCoreResidual MiuraCoreReduction MiuraCoreRestore
  MiuraCoreJoint MiuraCoreTranspose MiuraSlabIncidence

variable {m n : ℕ}

/-- Insert one line immediately before an actual frozen column. -/
noncomputable def stretchColumn (h : Cell m n → ℤ) (hm : 0 < m)
    (j : Fin n) (hj : frozenColumn h j) : Cell m (n + 1) → ℤ :=
  restoreColumn (n := n + 1) h ⟨j.val, by have := j.isLt; omega⟩ hj.1
    (by simp only [Fin.val_mk]; have := hj.2.1; omega) (frozenSlope h hm j hj)

private theorem stretch_seam (h : Cell m n → ℤ) (hh : IsHeight h) (hm : 0 < m)
    (j : Fin n) (hj : frozenColumn h j) :
    SeamSlope h (⟨j.val, by have := j.isLt; omega⟩ : Fin (n + 1)) hj.1
      (by simp only [Fin.val_mk]; have := hj.2.1; omega) (frozenSlope h hm j hj) := by
  intro i
  exact frozenSlope_eq h hh hm j hj i

private theorem stretch_new_frozen (h : Cell m n → ℤ) (hh : IsHeight h) (hm : 0 < m)
    (j : Fin n) (hj : frozenColumn h j) :
    frozenColumn (stretchColumn h hm j hj) ⟨j.val, by have := j.isLt; omega⟩ :=
  restoreColumn_frozen (n := n + 1) h ⟨j.val, by have := j.isLt; omega⟩ hj.1 _ _ (stretch_seam h hh hm j hj)

private theorem stretch_old_frozen (h : Cell m n → ℤ) (hm : 0 < m)
    (j : Fin n) (hj : frozenColumn h j) :
    frozenColumn (stretchColumn h hm j hj) ⟨j.val + 1, by have := hj.2.1; omega⟩ := by
  have hj0 := hj.1
  have hj1 := hj.2.1
  refine ⟨by simp only [Fin.val_mk]; omega, by simp only [Fin.val_mk]; omega, ?_⟩
  intro i
  have hs := hj.2.2 i
  simp only [stretchColumn, restoreColumn, Fin.val_mk, Nat.add_sub_cancel,
    show ¬ j.val < j.val from lt_irrefl _,
    show ¬ j.val + 1 < j.val by omega,
    show ¬ j.val + 1 + 1 < j.val by omega, dite_false]
  change (h (i, ⟨j.val - 1, by omega⟩) + frozenSlope h hm j hj) +
      (h (i, ⟨j.val + 1, hj1⟩) + frozenSlope h hm j hj) =
        2 * (h (i, j) + frozenSlope h hm j hj)
  linarith [hs]

private theorem restore_frozen_row (g : Cell m (n - 1) → ℤ)
    (j : Fin n) (hj0 : 0 < j.val) (hj1 : j.val + 1 < n) (s : ℤ)
    (i : Fin m) (hi : frozenColumn (transposeHeight g) i) :
    frozenColumn (transposeHeight (restoreColumn g j hj0 hj1 s)) i := by
  refine ⟨hi.1, hi.2.1, ?_⟩
  intro q
  by_cases hq : q.val < j.val
  · simpa only [transposeHeight, restoreColumn, hq, dite_true] using
      hi.2.2 ⟨q.val, by omega⟩
  · have hs := hi.2.2 ⟨q.val - 1, by have := q.isLt; omega⟩
    dsimp only [transposeHeight] at hs
    simp only [transposeHeight, restoreColumn, hq, dite_false]
    omega

/-- Every elementary run expansion is an exact inverse of a legal frozen-pair deletion. -/
theorem stretchColumn_reduction (h : Cell m n → ℤ) (hh : IsHeight h) (hm : 0 < m)
    (j : Fin n) (hj : frozenColumn h j) :
    ColumnReduction (stretchColumn h hm j hj) h := by
  let j' : Fin (n + 1) := ⟨j.val, by have := j.isLt; omega⟩
  let k' : Fin (n + 1) := ⟨j.val + 1, by have := hj.2.1; omega⟩
  have hf : frozenColumn (stretchColumn h hm j hj) j' := stretch_new_frozen h hh hm j hj
  have hk : frozenColumn (stretchColumn h hm j hj) k' := stretch_old_frozen h hm j hj
  refine .step (stretchColumn h hm j hj) hm j' k' hf hk rfl ?_
  have he : contractAt (stretchColumn h hm j hj) hm j' hf = h :=
    contractAt_restoreColumn (n := n + 1) h hm j' hj.1 _ _ (stretch_seam h hh hm j hj)
  rw [he]
  exact .refl h

/-- Inserting into a genuine frozen run preserves both exact extremum counts and all sides. -/
theorem stretchColumn_residual (a b : ℕ) (h : Cell m n → ℤ) (hm : 0 < m)
    (j : Fin n) (hj : frozenColumn h j) (hr : Residual a b h) :
    Residual a b (stretchColumn h hm j hj) :=
  restoreColumn_residual (n := n + 1) a b h hm ⟨j.val, by have := j.isLt; omega⟩ hj.1 _ _ (frozenSlope_pm h hr.1.1 hm j hj)
    (stretch_seam h hr.1.1 hm j hj) hr

private theorem column_trans {m n N P : ℕ} {h : Cell m n → ℤ}
    {g : Cell m N → ℤ} {f : Cell m P → ℤ}
    (hh : ColumnReduction h g) (hg : ColumnReduction g f) : ColumnReduction h f := by
  induction hh with
  | refl _ => exact hg
  | step h hm j k hj hk hjk tail ih => exact .step h hm j k hj hk hjk (ih hg)

/-- Any prescribed number of extra lines is realized by actual residual heights. -/
theorem residual_frozen_run_extension (a b : ℕ) (h : Cell m n → ℤ) (hm : 0 < m)
    (j : Fin n) (hj : frozenColumn h j) (hr : Residual a b h) (L : ℕ) :
    ∃ g : Cell m (n + L) → ℤ, Residual a b g ∧ ColumnReduction g h ∧
      (∃ k : Fin (n + L), frozenColumn g k) ∧
        ∀ i : Fin m, frozenColumn (transposeHeight h) i → frozenColumn (transposeHeight g) i := by
  induction L with
  | zero => exact ⟨h, hr, .refl h, ⟨j, hj⟩, fun _ hi => hi⟩
  | succ L ih =>
    obtain ⟨g, hg, hchain, ⟨k, hk⟩, hrows⟩ := ih
    refine ⟨stretchColumn g hm k hk, stretchColumn_residual a b g hm k hk hg,
      column_trans (stretchColumn_reduction g hg.1.1 hm k hk) hchain,
      ⟨⟨k.val, by have := k.isLt; omega⟩, stretch_new_frozen g hg.1.1 hm k hk⟩, ?_⟩
    intro i hi
    exact restore_frozen_row (n := n + L + 1) g _ hk.1 _ _ i (hrows i hi)

end D5.S3.Combinatorics.Geometry.MiuraCoreStretch
