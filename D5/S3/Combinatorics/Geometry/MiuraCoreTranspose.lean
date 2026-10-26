/- GID: D5/S3/Combinatorics/Geometry/MiuraCoreTranspose
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/MiuraCoreTranspose
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Axis exchange preserves the exact normalized residual class. -/

module

public import Batteries.Tactic.OpenPrivate
public import D5.S3.Combinatorics.Geometry.MiuraCoreReduction
public import D5.S3.Combinatorics.Geometry.MiuraSlabIncidence
import all D5.S3.Combinatorics.Geometry.MiuraSlabIncidence

/-! Transposition and preservation of exact signed extremum data. -/

@[expose] public section
namespace D5.S3.Combinatorics.Geometry.MiuraCoreTranspose
open MiuraHeightEnvelope MiuraResidualCount MiuraCoreResidual MiuraSlabIncidence

open private transpose_min transpose_max from D5.S3.Combinatorics.Geometry.MiuraSlabIncidence

variable {m n : ℕ}

private theorem transpose_min_iff (h : Cell m n → ℤ) (v : Cell n m) :
    IsStrictLocalMin (transposeHeight h) v ↔ IsStrictLocalMin h (v.2, v.1) := by
  constructor
  · exact transpose_min
  · intro hv
    exact transpose_min (h := transposeHeight h) hv

private theorem transpose_max_iff (h : Cell m n → ℤ) (v : Cell n m) :
    IsStrictLocalMax (transposeHeight h) v ↔ IsStrictLocalMax h (v.2, v.1) := by
  constructor
  · exact transpose_max
  · intro hv
    exact transpose_max (h := transposeHeight h) hv

/-- Axis exchange preserves minima and maxima separately. -/
theorem transpose_extremum_cards (h : Cell m n → ℤ) :
    (minima (transposeHeight h)).card = (minima h).card ∧
      (maxima (transposeHeight h)).card = (maxima h).card := by
  classical
  constructor
  · apply Finset.card_bij (fun v _ => (v.2, v.1))
    · intro v hv
      simpa only [minima, Finset.mem_filter, Finset.mem_univ, true_and,
        transpose_min_iff] using hv
    · intro v _ u _ he
      exact Prod.ext (congrArg Prod.snd he) (congrArg Prod.fst he)
    · intro u hu
      refine ⟨(u.2, u.1), ?_, rfl⟩
      simpa only [minima, Finset.mem_filter, Finset.mem_univ, true_and,
        transpose_min_iff] using hu
  · apply Finset.card_bij (fun v _ => (v.2, v.1))
    · intro v hv
      simpa only [maxima, Finset.mem_filter, Finset.mem_univ, true_and,
        transpose_max_iff] using hv
    · intro v _ u _ he
      exact Prod.ext (congrArg Prod.snd he) (congrArg Prod.fst he)
    · intro u hu
      refine ⟨(u.2, u.1), ?_, rfl⟩
      simpa only [maxima, Finset.mem_filter, Finset.mem_univ, true_and,
        transpose_max_iff] using hu

/-- A physical side is transported together with its axis. -/
def transposeSide : Side → Side
  | .top => .left
  | .bottom => .right
  | .left => .top
  | .right => .bottom

private theorem transpose_cell_side (sd : Side) (v : Cell n m) :
    cellOnSide sd v ↔ cellOnSide (transposeSide sd) (v.2, v.1) := by
  cases sd <;> rfl

/-- The same common physical side is preserved with its transposed name. -/
theorem transpose_all_minima_side_iff (h : Cell m n → ℤ) (sd : Side) :
    AllOnSide (fun v : Cell n m => ((v.1.val : ℤ) + 1, (v.2.val : ℤ) + 1))
      (minima (transposeHeight h)) (n : ℤ) (m : ℤ) sd ↔
    AllOnSide (fun v : Cell m n => ((v.1.val : ℤ) + 1, (v.2.val : ℤ) + 1))
      (minima h) (m : ℤ) (n : ℤ) (transposeSide sd) := by
  rw [all_minima_side_iff, all_minima_side_iff]
  constructor
  · intro hs v hv
    exact (transpose_cell_side sd (v.2, v.1)).mp
      (hs (v.2, v.1) ((transpose_min_iff h (v.2, v.1)).mpr hv))
  · intro hs v hv
    exact (transpose_cell_side sd v).mpr
      (hs (v.2, v.1) ((transpose_min_iff h v).mp hv))

/-- Axis exchange preserves the exact normalized residual predicate. -/
theorem transpose_residual (a b : ℕ) (h : Cell m n → ℤ) (hr : Residual a b h) :
    Residual a b (transposeHeight h) := by
  refine ⟨⟨transpose_isHeight hr.1.1, ?_⟩,
    (transpose_extremum_cards h).1.trans hr.2.1,
    (transpose_extremum_cards h).2.trans hr.2.2.1, ?_⟩
  · intro p hp hq
    exact hr.1.2 (p.2, p.1) hq hp
  · rintro ⟨sd, hs⟩
    exact hr.2.2.2 ⟨transposeSide sd, (transpose_all_minima_side_iff h sd).mp hs⟩

end D5.S3.Combinatorics.Geometry.MiuraCoreTranspose
