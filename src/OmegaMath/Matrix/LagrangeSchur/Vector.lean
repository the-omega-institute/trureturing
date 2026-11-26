module
prelude
public import OmegaMath.Matrix.LagrangeSchur.Diagonal

/-!
Omega original.

Diagonal block elimination with an arbitrary retained vector and diagonal
pivots on the eliminated coordinates.
-/

noncomputable section
@[expose] public section

namespace Omega.LagrangeSchur

/-- A row evaluated on the first `n` coordinates of the retained vector. -/
def dotPrefix (n : Nat) (u v : Nat → FiniteRatio) : FiniteRatio :=
  Nat.rec FiniteRatio.zero (fun i s => s.add ((u i).mul (v i))) n

/-- A row of the coupling matrix, its pivot, and its eliminated coordinate. -/
structure CoupledRow where
  row : Nat → FiniteRatio
  pivot : FiniteRatio
  coordinate : FiniteRatio

def evaluateRows (n : Nat) (x : Nat → FiniteRatio) (rows : Sequence CoupledRow) :
    Sequence DiagonalCoordinate :=
  rows.map (fun p => ⟨dotPrefix n p.row x, p.pivot, p.coordinate⟩)

/-- At fixed `x`, `a` is the value of the retained quadratic form. The coupling
on row `i` is the dot product of that row with `x`. -/
def vectorForm (a : FiniteRatio) (n : Nat) (x : Nat → FiniteRatio)
    (rows : Sequence CoupledRow) : FiniteRatio :=
  diagonalForm a FiniteRatio.one (evaluateRows n x rows)

def vectorSchurValue (a : FiniteRatio) (n : Nat) (x : Nat → FiniteRatio)
    (rows : Sequence CoupledRow) : FiniteRatio :=
  diagonalValue a FiniteRatio.one (evaluateRows n x rows)

private theorem rowProperty (n : Nat) (x : Nat → FiniteRatio)
    (P : FiniteRatio → Prop) (rows : Sequence CoupledRow)
    (h : rows.All (fun (p : CoupledRow) => P (CoupledRow.pivot p))) :
    (evaluateRows n x rows).All (fun (p : DiagonalCoordinate) => P (DiagonalCoordinate.c p)) :=
  (Sequence.rec (motive := fun rows => rows.All (fun (p : CoupledRow) => P (CoupledRow.pivot p)) →
    (evaluateRows n x rows).All (fun (p : DiagonalCoordinate) => P (DiagonalCoordinate.c p))) (fun _ => True.intro)
    (fun head tail ih h =>
      have h' : And (P (head .false).pivot) (tail.All (fun (p : CoupledRow) => P (CoupledRow.pivot p))) := h
      show And (P (head .false).pivot) ((evaluateRows n x tail).All (fun (p : DiagonalCoordinate) => P (DiagonalCoordinate.c p))) from
        And.intro h'.left (ih h'.right)) rows) h

theorem vector_schur_complete (a : FiniteRatio) (n : Nat) (x : Nat → FiniteRatio)
    (rows : Sequence CoupledRow) (h : rows.All (fun p => Not (Eq p.pivot.num Int.zero))) :
    (vectorForm a n x rows).Equivalent ((vectorSchurValue a n x rows).add
      (diagonalSquares FiniteRatio.one (evaluateRows n x rows))) :=
  diagonal_schur_complete a FiniteRatio.one (evaluateRows n x rows)
    (rowProperty n x (fun p => Not (Eq p.num Int.zero)) rows h)

theorem vector_schur_min (a : FiniteRatio) (n : Nat) (x : Nat → FiniteRatio)
    (rows : Sequence CoupledRow) (h : rows.All (fun p => FiniteRatio.zero.Lt p.pivot)) :
    And ((vectorSchurValue a n x rows).Le (vectorForm a n x rows))
      ((diagonalForm a FiniteRatio.one
        (diagonalMinPoint FiniteRatio.one (evaluateRows n x rows))).Equivalent
        (vectorSchurValue a n x rows)) :=
  diagonal_schur_min a FiniteRatio.one (evaluateRows n x rows)
    (rowProperty n x (FiniteRatio.Lt FiniteRatio.zero) rows h)

end Omega.LagrangeSchur
