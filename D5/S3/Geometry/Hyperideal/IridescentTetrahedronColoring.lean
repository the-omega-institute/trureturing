/- GID: D5/S3/Geometry/Hyperideal/IridescentTetrahedronColoring
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/IridescentTetrahedronColoring
   mirror-E: none(waiver:finite-local-color-classification)
   anchors: []
   utility: none
   digest: Rainbow three-edge colorings of one tetrahedron are exactly the opposite-pair balanced colorings, with six named choices. -/

import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Geometry.Hyperideal.IridescentTetrahedronColoring

/-- The six local edges are ordered as (12,13,14,34,24,23). -/
def faceEdges : Fin 4 → Fin 3 → Fin 6 :=
  ![![3, 4, 5], ![1, 2, 3], ![0, 2, 4], ![0, 1, 5]]

/-- A face is rainbow when its three edge colors are pairwise different. -/
def faceRainbow (color : Fin 6 → Fin 3) (face : Fin 4) : Prop :=
  let e := faceEdges face
  color (e 0) ≠ color (e 1) ∧
    color (e 0) ≠ color (e 2) ∧
      color (e 1) ≠ color (e 2)

/-- Every face of the tetrahedron is rainbow. -/
def rainbow (color : Fin 6 → Fin 3) : Prop :=
  ∀ face, faceRainbow color face

/-- Opposite local edges carry equal colors. -/
def oppositeBalanced (color : Fin 6 → Fin 3) : Prop :=
  color 0 = color 3 ∧ color 1 = color 4 ∧ color 2 = color 5

/-- The three opposite pairs have mutually different colors. -/
def pairColorsDistinct (color : Fin 6 → Fin 3) : Prop :=
  color 0 ≠ color 1 ∧ color 0 ≠ color 2 ∧ color 1 ≠ color 2

private theorem value_classification : ∀ c0 c1 c2 c3 c4 c5 : Fin 3,
    ((c3 ≠ c4 ∧ c3 ≠ c5 ∧ c4 ≠ c5) ∧
      (c1 ≠ c2 ∧ c1 ≠ c3 ∧ c2 ≠ c3) ∧
      (c0 ≠ c2 ∧ c0 ≠ c4 ∧ c2 ≠ c4) ∧
      (c0 ≠ c1 ∧ c0 ≠ c5 ∧ c1 ≠ c5)) ↔
      ((c0 = c3 ∧ c1 = c4 ∧ c2 = c5) ∧
        (c0 ≠ c1 ∧ c0 ≠ c2 ∧ c1 ≠ c2)) := by
  intro c0 c1 c2 c3 c4 c5
  fin_cases c0 <;> fin_cases c1 <;> fin_cases c2 <;>
    fin_cases c3 <;> fin_cases c4 <;> fin_cases c5 <;> decide

/-- In a tetrahedron, all four faces are rainbow exactly when opposite pairs
    agree and the three opposite-pair colors are mutually different. -/
theorem rainbow_iff_opposite_balanced_and_distinct :
    ∀ color : Fin 6 → Fin 3,
      rainbow color ↔ oppositeBalanced color ∧ pairColorsDistinct color := by
  intro color
  have hfaces : (∀ face : Fin 4, faceRainbow color face) ↔
      faceRainbow color 0 ∧ faceRainbow color 1 ∧
        faceRainbow color 2 ∧ faceRainbow color 3 := by
    constructor
    · intro h
      exact ⟨h 0, h 1, h 2, h 3⟩
    · rintro ⟨h0, h1, h2, h3⟩ face
      fin_cases face <;> assumption
  change (∀ face : Fin 4, faceRainbow color face) ↔
    oppositeBalanced color ∧ pairColorsDistinct color
  rw [hfaces]
  simpa [faceRainbow, faceEdges, oppositeBalanced, pairColorsDistinct] using
    value_classification (color 0) (color 1) (color 2) (color 3) (color 4) (color 5)

/-- A named coloring is obtained by assigning the three colors to the three
    opposite pairs in the order (12,34), (13,24), (14,23). -/
def namedColoring (permutation : Equiv.Perm (Fin 3)) : Fin 6 → Fin 3 :=
  ![permutation 0, permutation 1, permutation 2,
    permutation 0, permutation 1, permutation 2]

/-- Every named permutation coloring is rainbow on all four faces. -/
theorem namedColoring_is_rainbow :
    ∀ permutation : Equiv.Perm (Fin 3), rainbow (namedColoring permutation) := by
  intro permutation face
  fin_cases face <;>
    simp [faceRainbow, faceEdges, namedColoring]

/-- The three colors have exactly six named permutations. -/
theorem namedColoring_count : Fintype.card (Equiv.Perm (Fin 3)) = 6 := by decide

#print axioms rainbow_iff_opposite_balanced_and_distinct
#print axioms namedColoring_is_rainbow
#print axioms namedColoring_count

end D5.S3.Geometry.Hyperideal.IridescentTetrahedronColoring
