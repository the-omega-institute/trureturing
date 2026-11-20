/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9NineProjection
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9NineProjection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: A signed-row obstruction to the normalized nine-point projection. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9FourFiberSpectrum
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9ThetaProjection
import Batteries.Tactic.OpenPrivate

/-! The normalized nine-point projection in Hong–Wu–Xia, §7 Problem 2, is
excluded by four exterior rows of the TRUE-prefix signed four-cube. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9NineProjection

open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced)
open Q9SignedProjection (join fiber signedRow q9_balanced_signed_projection)
open Q9FourFiberSpectrum (leftProjection fiber_and_signedRow_supported)
open private pattern signed_row_four from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9ThetaProjection
open private mem_leftProjection from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9FourFiberSpectrum

private def nineCodes : Finset (BitVec 4) := {0, 1, 2, 3, 4, 11, 12, 13, 15}

/-- The normalized nine points in the little-endian projection coordinates. -/
def nineProjection : Finset (Q 4) := nineCodes.map (cubeBitVec 4).toEmbedding

private theorem pattern_mem_nineProjection (k : BitVec 4) :
    pattern k ∈ nineProjection ↔ k ∈ nineCodes :=
  Finset.mem_map' (cubeBitVec 4).toEmbedding

/-- If both an integer four-cube function and its TRUE-prefix signed row vanish
outside the nine points, the function vanishes at code `1`. -/
theorem fiber_one_eq_zero {f : Q 4 → ℤ}
    (hf : ∀ x ∉ nineProjection, f x = 0)
    (hr : ∀ x ∉ nineProjection, signedRow f x = 0) : f (cubeBitVec 4 1) = 0 := by
  have outside (k : BitVec 4) (hk : k ∉ nineCodes) : pattern k ∉ nineProjection :=
    fun h => hk ((pattern_mem_nineProjection k).mp h)
  have row5 := signed_row_four f 5 4 7 1 13 1 (-1) (-1) 1
    (by decide +kernel) (by decide +kernel)
  have row6 := signed_row_four f 6 7 4 2 14 1 1 (-1) 1
    (by decide +kernel) (by decide +kernel)
  have row9 := signed_row_four f 9 8 11 13 1 1 (-1) (-1) (-1)
    (by decide +kernel) (by decide +kernel)
  have row10 := signed_row_four f 10 11 8 14 2 1 1 (-1) (-1)
    (by decide +kernel) (by decide +kernel)
  simp only [hr _ (outside 5 (by decide +kernel)), hr _ (outside 6 (by decide +kernel)),
    hr _ (outside 9 (by decide +kernel)), hr _ (outside 10 (by decide +kernel)),
    hf _ (outside 7 (by decide +kernel)), hf _ (outside 8 (by decide +kernel)),
    hf _ (outside 14 (by decide +kernel)), one_mul, neg_one_mul, neg_zero, zero_add,
    add_zero] at row5 row6 row9 row10
  have h42 : f (pattern 4) = f (pattern 2) := by omega
  have h211 : f (pattern 2) = f (pattern 11) := by omega
  rw [h42, h211] at row5
  change f (pattern 1) = 0
  omega

open Classical in
/-- A Huang-balanced induced cubic support in the nine-cube cannot realize
the normalized nine-point set as its first four coordinates. -/
theorem balanced_projection_ne_nineProjection {C : Finset (Q 9)}
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) : leftProjection C ≠ nineProjection := by
  intro hP
  have hone : pattern 1 ∈ leftProjection C := by
    rw [hP]
    exact (pattern_mem_nineProjection 1).mpr (by decide +kernel)
  obtain ⟨y, hy⟩ := mem_leftProjection.mp hone
  obtain ⟨z, hunit, hzero, hrow, _⟩ := q9_balanced_signed_projection hreg hb
  have supported (x : Q 4) (hx : x ∉ nineProjection) :
      fiber z y x = 0 ∧ signedRow (fiber z y) x = 0 :=
    fiber_and_signedRow_supported hzero hrow y (x := x) (by simpa only [hP] using hx)
  have hvanish := fiber_one_eq_zero (f := fiber z y)
    (fun x hx => (supported x hx).1) (fun x hx => (supported x hx).2)
  change z (join (pattern 1) y) = 0 at hvanish
  rcases hunit _ hy with h | h <;> omega

/- To transport the obstruction, lift a cube action `g` on `Q 4` by
`G (join x y) = join (g x) y`. Extend its direction permutation by the
identity on the last five directions. The left and right join-flip identities
give flip compatibility by the two cases of `Fin.addCases`. Then
`HuangBalancedSymmetry.cube_action_regular_balanced` transfers cubicity and
balance to `C.image G`, whose left projection is `(leftProjection C).image g`.
Apply the exclusion to any action sending the original projection to `nineProjection`. -/

#print axioms fiber_one_eq_zero
#print axioms balanced_projection_ne_nineProjection

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9NineProjection
