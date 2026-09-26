/- GID: D5/S3/Combinatorics/CrosswordRookCountsDefs
   generality: G
   mirror-B: D5/B/S3/Combinatorics/CrosswordRookCountsDefs
   mirror-E: none(waiver:fixed-external-open-question-statement)
   anchors: [mathlib/module/Mathlib.Order.Fin.Basic]
   utility: none
   digest: Fixed crossword-grid rook-placement definitions and the Lewis-Won existence claim. -/

import Mathlib.Data.Finset.Powerset
import Mathlib.Order.Fin.Basic
import Mathlib.Data.Fintype.Prod

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.CrosswordRookCounts

/-- A cell of an `N × N` crossword grid: (row, column). -/
abbrev Cell (N : ℕ) := Fin N × Fin N

/-- `c` and `d` lie in the same across word of the grid whose white cells are `W`:
they are in the same row and every cell of that row between them (inclusive) is white. -/
def SameAcross {N : ℕ} (W : Finset (Cell N)) (c d : Cell N) : Prop :=
  c.1 = d.1 ∧ ∀ j : Fin N, min c.2 d.2 ≤ j → j ≤ max c.2 d.2 → (c.1, j) ∈ W

/-- `c` and `d` lie in the same down word: same column, every cell between them white. -/
def SameDown {N : ℕ} (W : Finset (Cell N)) (c d : Cell N) : Prop :=
  c.2 = d.2 ∧ ∀ i : Fin N, min c.1 d.1 ≤ i → i ≤ max c.1 d.1 → (i, c.2) ∈ W

/-- A complete non-attacking rook placement: a set of white cells meeting every across word
and every down word exactly once (at most once: no two rooks share a word; at least once:
the word of every white cell contains a rook). -/
def IsRookPlacement {N : ℕ} (W R : Finset (Cell N)) : Prop :=
  R ⊆ W ∧
  (∀ c ∈ R, ∀ d ∈ R, c ≠ d → ¬ SameAcross W c d ∧ ¬ SameDown W c d) ∧
  ∀ c ∈ W, (∃ d ∈ R, SameAcross W c d) ∧ (∃ d ∈ R, SameDown W c d)

open Classical in
/-- The number `|RP(G)|` of complete rook placements of the grid with white cells `W`. -/
noncomputable def rookCount {N : ℕ} (W : Finset (Cell N)) : ℕ :=
  (W.powerset.filter (fun R => IsRookPlacement W R)).card

/-- Lewis–Won, Question 4.2 (existence part): every natural number is the number of complete
rook placements of some (square) crossword grid. -/
def claim : Prop := ∀ r : ℕ, ∃ N : ℕ, ∃ W : Finset (Cell N), rookCount W = r

/-- The width leaves the five active columns and the active rows inside a square. -/
def gridSize (r : ℕ) : ℕ := max 5 (2 * r - 1)

/-- The side occupied by the three-cell down word in block `i`. -/
def side (i : ℕ) : ℕ := if i % 2 = 0 then 3 else 1

/-- The singleton down word of block `i` is on its outer edge. -/
def tip (i : ℕ) : ℕ := if i % 2 = 0 then 4 else 0

/-- Left endpoint of a nonempty row of the displayed board. -/
def rowLeft (r a : ℕ) : ℕ :=
  if a % 2 = 1 then (if a % 4 = 1 then 2 else 0)
  else if a = 0 ∨ (a = 2 * r - 2 ∧ a % 4 = 2) then 2 else 1

/-- Right endpoint of a nonempty row of the displayed board. -/
def rowRight (r a : ℕ) : ℕ :=
  if a % 2 = 1 then (if a % 4 = 1 then 4 else 2)
  else if a = 2 * r - 2 ∧ a % 4 = 0 then 2 else 3

/-- The report's square grid, given as contiguous intervals in its occupied rows. -/
noncomputable def white (r : ℕ) : Finset (Cell (gridSize r)) :=
  by
    classical
    exact Finset.univ.filter (fun c =>
      c.1.val < 2 * r - 1 ∧
        rowLeft r c.1.val ≤ c.2.val ∧ c.2.val ≤ rowRight r c.1.val)

/-- The candidate indexed by the even row `2*k` occupied in the central down word. -/
noncomputable def candidate (r k : ℕ) : Finset (Cell (gridSize r)) :=
  by
    classical
    exact Finset.univ.filter (fun c =>
      (c.1.val = 2 * k ∧ c.2.val = 2) ∨
      (∃ i : ℕ, i + 1 < r ∧ c.1.val = 2 * i + 1 ∧ c.2.val = tip i) ∨
      (∃ i : ℕ, i + 1 < r ∧ c.2.val = side i ∧
        ((i < k ∧ c.1.val = 2 * i) ∨ (k ≤ i ∧ c.1.val = 2 * i + 2))))

end D5.S3.Combinatorics.CrosswordRookCounts
