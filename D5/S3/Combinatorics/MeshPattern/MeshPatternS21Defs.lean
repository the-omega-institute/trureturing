/- GID: D5/S3/Combinatorics/MeshPattern/MeshPatternS21Defs
   generality: G
   mirror-B: D5/B/S3/Combinatorics/MeshPattern/MeshPatternS21Defs
   mirror-E: none(waiver:fixed-mesh-pattern-joint-symmetry-statement-definition)
   anchors: [mathlib/module/Mathlib.Data.Set.Card]
   utility: none
   digest: Lv and Zhang's joint symmetry conjecture for the mesh patterns 123 and 321 (pair S21). -/

import Mathlib.Data.Set.Card

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.MeshPattern.MeshPatternS21Defs

/-! Fixed public statement: Lv and Zhang, *Joint equidistributions of mesh patterns 123 and 321
    with symmetric and minus-antipodal shadings*, arXiv:2501.00357v3, §2.4, Conjecture 2, pair
    S21.  Both patterns carry the shading `R = {0,1,2}² ∪ {(3,3)}`, where a cell `(i, j)` has
    column `i` (the number of pattern points to its left) and row `j` (the number of pattern
    points below it).  Permutations of `[n]` are lists in one-line notation and positions are
    zero-based. -/

/-- The shaded cells `R = {0,1,2}² ∪ {(3,3)}`. -/
def Shaded (col row : ℕ) : Prop := (col ≤ 2 ∧ row ≤ 2) ∨ (col = 3 ∧ row = 3)

/-- The column of position `l` relative to the chosen positions `i, j, k`. -/
def column (i j k l : ℕ) : ℕ :=
  (if i < l then 1 else 0) + (if j < l then 1 else 0) + (if k < l then 1 else 0)

/-- The row of value `x` relative to the chosen values `a, b, c`. -/
def row (a b c x : ℕ) : ℕ :=
  (if a < x then 1 else 0) + (if b < x then 1 else 0) + (if c < x then 1 else 0)

/-- `(i, j, k)` is an occurrence in `p` of the mesh pattern `(123, R)` when `inc` holds, and of
    `(321, R)` otherwise: the three entries have the pattern's order, and no other entry of `p`
    lies in a shaded cell. -/
def IsOccurrence (inc : Bool) (p : List ℕ) (t : ℕ × ℕ × ℕ) : Prop :=
  t.1 < t.2.1 ∧ t.2.1 < t.2.2 ∧ t.2.2 < p.length ∧
    (if inc then p.getD t.1 0 < p.getD t.2.1 0 ∧ p.getD t.2.1 0 < p.getD t.2.2 0
      else p.getD t.2.2 0 < p.getD t.2.1 0 ∧ p.getD t.2.1 0 < p.getD t.1 0) ∧
    ∀ l < p.length, l ≠ t.1 → l ≠ t.2.1 → l ≠ t.2.2 →
      ¬ Shaded (column t.1 t.2.1 t.2.2 l)
        (row (p.getD t.1 0) (p.getD t.2.1 0) (p.getD t.2.2 0) (p.getD l 0))

/-- The number of occurrences of `(123, R)` (`inc = true`) or `(321, R)` (`inc = false`). -/
noncomputable def occ (inc : Bool) (p : List ℕ) : ℕ := {t | IsOccurrence inc p t}.ncard

/-- Permutations of `[n]` with `k` occurrences of `(123, R)` and `l` occurrences of `(321, R)`. -/
def joint (n k l : ℕ) : Set (List ℕ) :=
  {p | p.Perm (List.range' 1 n) ∧ occ true p = k ∧ occ false p = l}

/-- Conjecture 2 (pair S21): the joint distribution of the two occurrence counts is symmetric. -/
def claim : Prop := ∀ n k l : ℕ, (joint n k l).ncard = (joint n l k).ncard

end D5.S3.Combinatorics.MeshPattern.MeshPatternS21Defs
