import D5.S0.Certificates.BoxCover.CheckedRationalBoxCover
import Batteries.Tactic.OpenPrivate
import Mathlib.Data.Fin.VecNotation

/-! Midpoint bisection for the 103-cell Wu cubic upper focal cover. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Semigroups.WuCubicUpperPartition

open private region leftBox rightBox split_retains from
  D5.S0.Certificates.BoxCover.CheckedRationalBoxCover

abbrev Box := Fin 4 → ℚ × ℚ

/-- Closed real membership for the rational endpoints. -/
abbrev InBox (box : Box) (x : Fin 4 → ℝ) : Prop := x ∈ region box

/-- A split bisects the current box along its given coordinate. -/
inductive Tree where
  | leaf
  | split (axis : Fin 4) (left right : Tree)

private def midpoint (box : Box) (axis : Fin 4) : ℚ :=
  ((box axis).1 + (box axis).2) / 2

/-- The concrete leaf boxes in left-to-right order. -/
def Tree.leaves : Tree → Box → List Box
  | .leaf, box => [box]
  | .split axis left right, box =>
    let cut := midpoint box axis
    left.leaves (leftBox box axis cut) ++ right.leaves (rightBox box axis cut)

/-- Every point in the starting box belongs to a leaf box. -/
theorem Tree.covers (t : Tree) (box : Box) {x : Fin 4 → ℝ} (hx : InBox box x) :
    ∃ cell ∈ t.leaves box, InBox cell x := by
  induction t generalizing box with
  | leaf =>
    exact ⟨box, List.mem_singleton_self _, hx⟩
  | split axis left right ihLeft ihRight =>
    let cut := midpoint box axis
    rcases split_retains box axis cut hx with hxLeft | hxRight
    · obtain ⟨cell, hcell, hinside⟩ := ihLeft (leftBox box axis cut) hxLeft
      exact ⟨cell, List.mem_append.mpr (Or.inl hcell), hinside⟩
    · obtain ⟨cell, hcell, hinside⟩ := ihRight (rightBox box axis cut) hxRight
      exact ⟨cell, List.mem_append.mpr (Or.inr hcell), hinside⟩

/-- Run the rational checker on each concrete leaf box. -/
def Tree.check (t : Tree) (box : Box) (checkCell : Box → Bool) : Bool :=
  (t.leaves box).all checkCell

/-- An accepted fold proves the property throughout the starting box using
soundness on the checked leaves. -/
theorem Tree.check_sound (t : Tree) (box : Box) (checkCell : Box → Bool)
    {P : (Fin 4 → ℝ) → Prop}
    (hcheck : t.check box checkCell = true)
    (soundCell : ∀ cell ∈ t.leaves box, checkCell cell = true →
      ∀ x, InBox cell x → P x)
    {x : Fin 4 → ℝ} (hx : InBox box x) : P x := by
  obtain ⟨cell, hcell, hinside⟩ := t.covers box hx
  exact soundCell cell hcell (List.all_eq_true.mp hcheck cell hcell) x hinside

/-- Assemble separate kernel decisions indexed by the concrete leaf list. -/
theorem Tree.check_of_leaves (t : Tree) (box : Box) (checkCell : Box → Bool)
    (h : ∀ i : Fin (t.leaves box).length, checkCell ((t.leaves box).get i) = true) :
    t.check box checkCell = true := by
  apply List.all_eq_true.mpr
  intro cell hcell
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hcell
  exact h i

/-- The rational root in coordinates `(r, y₀, y₁, blend)`, definitionally
equal to `WuCubicThermalDerivatives.upperRoot`. For the corner-jet input
`z : Fin 5 → ℝ`, the corresponding point is `fun i => z i.castSucc`. -/
def root : Box :=
  ![(1049 / 1000, 6 / 5), (0, 1 / 256), (-1 / 128, 1 / 128), (0, 1)]

/-- The bisection axes from `wu-cubic-hellinger-margin-20261127/split-tree.lean.txt`.
The leaf boxes for replay are `tree.leaves root`. -/
def tree : Tree :=
  (.split 0
    (.split 0
      (.split 0
        (.split 2
          (.split 3
            (.split 0
              (.split 2
                (.split 3 (.split 0 .leaf .leaf) (.split 0 .leaf .leaf))
                (.split 3 .leaf (.split 0 .leaf .leaf)))
              (.split 2 (.split 3 .leaf .leaf) (.split 3 .leaf .leaf)))
            (.split 0
              (.split 2
                (.split 3
                  (.split 0 (.split 2 .leaf .leaf) .leaf)
                  (.split 0 (.split 2 .leaf .leaf) (.split 2 .leaf .leaf)))
                (.split 3 (.split 0 .leaf .leaf) (.split 0 .leaf .leaf)))
              (.split 2
                (.split 3 (.split 0 .leaf .leaf) (.split 0 .leaf .leaf))
                (.split 3 .leaf (.split 0 .leaf .leaf)))))
          (.split 2
            (.split 0
              (.split 3
                (.split 2 .leaf .leaf)
                (.split 0 (.split 2 .leaf .leaf) (.split 2 .leaf .leaf)))
              (.split 3 .leaf (.split 2 .leaf .leaf)))
            (.split 0 (.split 2 (.split 0 .leaf .leaf) .leaf) (.split 2 .leaf .leaf))))
        (.split 2
          (.split 3
            (.split 0 (.split 2 (.split 3 .leaf .leaf) .leaf) (.split 2 .leaf .leaf))
            (.split 0
              (.split 2 (.split 3 .leaf .leaf) (.split 3 .leaf .leaf))
              (.split 2 (.split 3 .leaf .leaf) .leaf)))
          (.split 2
            (.split 0 (.split 3 .leaf .leaf) (.split 3 .leaf .leaf))
            (.split 0 (.split 2 .leaf .leaf) .leaf))))
      (.split 0
        (.split 2
          (.split 3
            (.split 0 (.split 2 .leaf .leaf) (.split 2 .leaf .leaf))
            (.split 0 (.split 2 .leaf .leaf) (.split 2 .leaf .leaf)))
          (.split 2 (.split 0 (.split 3 .leaf .leaf) .leaf) (.split 0 .leaf .leaf)))
        (.split 2
          (.split 3
            (.split 0 (.split 2 .leaf .leaf) .leaf)
            (.split 0 (.split 2 .leaf .leaf) (.split 2 .leaf .leaf)))
          (.split 2 (.split 0 .leaf .leaf) .leaf))))
    (.split 0
      (.split 2
        (.split 0
          (.split 3 (.split 0 .leaf .leaf) (.split 0 .leaf .leaf))
          (.split 3 .leaf (.split 0 .leaf .leaf)))
        (.split 0 (.split 2 .leaf .leaf) (.split 2 .leaf .leaf)))
      (.split 2
        (.split 0 (.split 3 .leaf .leaf) (.split 3 .leaf .leaf))
        (.split 0 (.split 2 .leaf .leaf) .leaf))))

theorem leaf_count : (tree.leaves root).length = 103 := by
  decide +kernel

end D5.S3.Quantum.Semigroups.WuCubicUpperPartition
