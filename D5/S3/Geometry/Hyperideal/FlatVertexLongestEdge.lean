/- GID: D5/S3/Geometry/Hyperideal/FlatVertexLongestEdge
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/FlatVertexLongestEdge
   mirror-E: none(waiver:hyperbolic-flat-vertex-inequality)
   anchors: []
   utility: none
   digest: A flat hyperbolic face angle forces its opposite truncated side to be longest. -/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic.Linarith

/-!
# Flat hyperbolic vertex edge inequality

The cosine-law inequality at a flat vertex forces the opposite edge to be at
least the sum of the two incident positive edges.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Geometry.Hyperideal.FlatVertexLongestEdge

/-- The hyperbolic cosine of the angle opposite the side `c` in a positive
    triangle with the other sides `a` and `b`. -/
def faceCosine (a b c : ℝ) : ℝ :=
  (Real.cosh a * Real.cosh b - Real.cosh c) /
    (Real.sinh a * Real.sinh b)

/-- A nonpositive flat-angle cosine forces the opposite side to dominate the
    sum of the two incident sides. -/
theorem flat_vertex_longest_edge {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hflat : faceCosine a b c ≤ -1) :
    a + b ≤ c := by
  have hden : 0 < Real.sinh a * Real.sinh b :=
    mul_pos (Real.sinh_pos_iff.mpr ha) (Real.sinh_pos_iff.mpr hb)
  have hmul : Real.cosh a * Real.cosh b - Real.cosh c ≤
      -(Real.sinh a * Real.sinh b) := by
    simpa [faceCosine] using (div_le_iff₀ hden).mp hflat
  have hcosh : Real.cosh (a + b) ≤ Real.cosh c := by
    rw [Real.cosh_add]
    linarith
  have habs : |a + b| ≤ |c| := (Real.cosh_le_cosh).mp hcosh
  simpa [abs_of_nonneg (le_of_lt (add_pos ha hb)), abs_of_nonneg (le_of_lt hc)]
    using habs

#print axioms flat_vertex_longest_edge

end D5.S3.Geometry.Hyperideal.FlatVertexLongestEdge
