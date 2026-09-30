/- GID: D5/S3/Geometry/Hyperideal/VertexStateColoring
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/VertexStateColoring
   mirror-E: none(waiver:finite-tetrahedral-vertex-state)
   anchors: []
   utility: none
   digest: Balanced binary vertex colorings classify the three opposite-edge flat-angle patterns. -/

import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Geometry.Hyperideal.VertexStateColoring

/-- Exactly two of the four vertices carry the zero color. -/
def balanced (b : Fin 4 → Bool) : Bool :=
  ((List.finRange 4).filter (fun i => !b i)).length == 2

/-- The three partitions 12|34, 13|24, and 14|23, using zero-based indices. -/
def stateColor (k : Fin 3) : Fin 4 → Bool :=
  if k = 0 then ![false, false, true, true]
  else if k = 1 then ![false, true, false, true]
  else ![false, true, true, false]

/-- Equal-color edges of a coloring have the same pattern as state `k`. -/
def corresponds (b : Fin 4 → Bool) (k : Fin 3) : Bool :=
  (List.finRange 4).all fun i =>
    (List.finRange 4).all fun j =>
      (i == j) || ((b i == b j) == (stateColor k i == stateColor k j))

/-- XOR is addition of the two vertex colors in the binary field. -/
def crossing (b : Fin 4 → Bool) (i j : Fin 4) : Bool :=
  xor (b i) (b j)

/-- The local flat extension angle attached to a vertex coloring. -/
noncomputable def flatAngle (b : Fin 4 → Bool) (i j : Fin 4) : ℝ :=
  if b i = b j then Real.pi else 0

/-- The three standard states exhaust the balanced colorings up to swapping colors.
    Same-color edges carry angle pi, and cross-color edges carry angle zero. -/
theorem balanced_coloring_flat_angle_correspondence :
    (∀ k : Fin 3,
      balanced (stateColor k) = true ∧ corresponds (stateColor k) k = true) ∧
    (∀ b : Fin 4 → Bool, balanced b = true →
      ((List.finRange 3).filter (fun k => corresponds b k)).length = 1) ∧
    (∀ (b : Fin 4 → Bool) (i j : Fin 4),
      flatAngle b i j = Real.pi * (1 - ((crossing b i j).toNat : ℝ))) := by
  constructor
  · intro k
    fin_cases k <;> decide
  constructor
  · intro b
    have hfun : b = ![b 0, b 1, b 2, b 3] := by
      funext i
      fin_cases i <;> rfl
    rw [hfun]
    generalize h0 : b 0 = c0
    generalize h1 : b 1 = c1
    generalize h2 : b 2 = c2
    generalize h3 : b 3 = c3
    cases c0 <;> cases c1 <;> cases c2 <;> cases c3 <;> decide
  · intro b i j
    cases hbi : b i <;> cases hbj : b j <;>
      simp [flatAngle, crossing, hbi, hbj]

#print axioms balanced_coloring_flat_angle_correspondence

end D5.S3.Geometry.Hyperideal.VertexStateColoring
