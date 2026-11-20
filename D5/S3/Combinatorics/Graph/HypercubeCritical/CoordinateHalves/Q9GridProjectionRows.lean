import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9ThetaProjection
import Batteries.Tactic.OpenPrivate

/-! The signed rows of a nine-cube support projecting into a nine-point grid
reduce to four functions on the complementary five coordinates. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9GridProjectionRows

open BalancedCriticalSpectrum (Q)
open Q9SignedProjection (join fiber signedRow leftParitySign q9_signed_row_split
  q9_signed_row_eq_zero_outside_projection)
open Q9ThetaProjection (leftCode)
open private pattern leftCode_join signed_row_four from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9ThetaProjection

/-- The nine points of `P₃ × P₃` in the little-endian projection coordinates. -/
def gridEnvelope : Finset (BitVec 4) := {0, 1, 2, 3, 4, 5, 8, 10, 12}

private theorem outside_patterns :
    (6 : BitVec 4) ∉ gridEnvelope ∧ (7 : BitVec 4) ∉ gridEnvelope ∧
    (9 : BitVec 4) ∉ gridEnvelope ∧ (11 : BitVec 4) ∉ gridEnvelope ∧
    (13 : BitVec 4) ∉ gridEnvelope ∧ (14 : BitVec 4) ∉ gridEnvelope ∧
    (15 : BitVec 4) ∉ gridEnvelope := by
  decide +kernel

private theorem carrier_parities :
    leftParitySign (pattern 0) = 1 ∧ leftParitySign (pattern 1) = -1 ∧
    leftParitySign (pattern 2) = -1 ∧ leftParitySign (pattern 3) = 1 := by
  decide +kernel

/-- The exterior rows identify five fibers with signed copies of the four
carrier fibers. The signed row on `Q 5` then satisfies the four carrier
equations and the equation for the sum of fibers `1` and `2`.

For a balanced induced cubic support, `q9_balanced_signed_projection` supplies
the switching with `hzero` and `hz`. -/
theorem grid_projection_rows {C : Finset (Q 9)} {z : Q 9 → ℤ}
    (hgrid : ∀ u ∈ C, leftCode u ∈ gridEnvelope)
    (hzero : ∀ u ∉ C, z u = 0) (hz : ∀ u, signedRow z u = 3 * z u) (y : Q 5) :
    let h (k : BitVec 4) (v : Q 5) := fiber z v (cubeBitVec 4 k)
    h 4 y = h 2 y ∧ h 5 y = h 3 y ∧ h 8 y = h 1 y ∧
    h 10 y = -h 3 y ∧ h 12 y = -h 3 y ∧
    signedRow (h 0) y = 3 * h 0 y - 2 * h 1 y - 2 * h 2 y ∧
    signedRow (h 1) y = h 0 y - 3 * h 1 y - 2 * h 3 y ∧
    signedRow (h 2) y = h 0 y - 3 * h 2 y + 2 * h 3 y ∧
    signedRow (h 3) y = 3 * h 3 y + h 1 y - h 2 y ∧
    signedRow (fun v => h 1 v + h 2 v) y = 2 * h 0 y - 3 * (h 1 y + h 2 y) := by
  intro h
  have zero (k : BitVec 4) (hk : k ∉ gridEnvelope) (v : Q 5) :
      fiber z v (pattern k) = 0 := by
    refine hzero (join (pattern k) v) ?_
    intro hv
    exact hk (by simpa only [leftCode_join] using hgrid (join (pattern k) v) hv)
  have row_zero (k : BitVec 4) (hk : k ∉ gridEnvelope) :
      signedRow (fiber z y) (pattern k) = 0 :=
    q9_signed_row_eq_zero_outside_projection hz (zero k hk) y
  obtain ⟨n6, n7, n9, n11, n13, n14, n15⟩ := outside_patterns
  -- Evaluate the five exterior rows that determine the repeated fibers.
  have h4 : h 4 y = h 2 y := by
    have e : 0 = h 4 y + -h 2 y := by
      simpa only [row_zero 6 n6, zero 7 n7 y, zero 14 n14 y, one_mul, neg_one_mul,
        zero_add, add_zero] using
        signed_row_four (fiber z y) 6 7 4 2 14 1 1 (-1) 1 (by decide +kernel) (by decide +kernel)
    omega
  have h5 : h 5 y = h 3 y := by
    have e : 0 = -h 5 y + h 3 y := by
      simpa only [row_zero 7 n7, zero 6 n6 y, zero 15 n15 y, one_mul, neg_one_mul,
        neg_zero, zero_add, add_zero] using
        signed_row_four (fiber z y) 7 6 5 3 15 1 (-1) 1 (-1) (by decide +kernel) (by decide +kernel)
    omega
  have h8 : h 8 y = h 1 y := by
    have e : 0 = h 8 y + -h 1 y := by
      simpa only [row_zero 9 n9, zero 11 n11 y, zero 13 n13 y, one_mul, neg_one_mul,
        neg_zero, zero_add] using
        signed_row_four (fiber z y) 9 8 11 13 1 1 (-1) (-1) (-1) (by decide +kernel) (by decide +kernel)
    omega
  have h10 : h 10 y = -h 3 y := by
    have e : 0 = h 10 y + h 3 y := by
      simpa only [row_zero 11 n11, zero 9 n9 y, zero 15 n15 y, one_mul, neg_one_mul,
        neg_zero, zero_add] using
        signed_row_four (fiber z y) 11 10 9 15 3 1 (-1) 1 1 (by decide +kernel) (by decide +kernel)
    omega
  have h12 : h 12 y = -h 3 y := by
    have e : 0 = h 12 y + h 5 y := by
      simpa only [row_zero 13 n13, zero 15 n15 y, zero 9 n9 y, one_mul, neg_one_mul,
        neg_zero, zero_add] using
        signed_row_four (fiber z y) 13 12 15 9 5 1 (-1) (-1) 1 (by decide +kernel) (by decide +kernel)
    rw [h5] at e
    omega
  have split (k : BitVec 4) : 3 * h k y = signedRow (fiber z y) (pattern k) +
      leftParitySign (pattern k) * signedRow (h k) y :=
    q9_signed_row_split hz (pattern k) y
  obtain ⟨p0, p1, p2, p3⟩ := carrier_parities
  have ha : signedRow (h 0) y = 3 * h 0 y - 2 * h 1 y - 2 * h 2 y := by
    have e : signedRow (fiber z y) (pattern 0) = h 1 y + (h 2 y + (h 4 y + h 8 y)) := by
      simpa only [one_mul] using
        signed_row_four (fiber z y) 0 1 2 4 8 1 1 1 1 (by decide +kernel) (by decide +kernel)
    have hs := split 0
    rw [e, h4, h8, p0, one_mul] at hs
    omega
  have hb : signedRow (h 1) y = h 0 y - 3 * h 1 y - 2 * h 3 y := by
    have e : signedRow (fiber z y) (pattern 1) = h 0 y + (-h 3 y + -h 5 y) := by
      simpa only [zero 9 n9 y, one_mul, neg_one_mul, neg_zero, add_zero] using
        signed_row_four (fiber z y) 1 0 3 5 9 1 (-1) (-1) (-1) (by decide +kernel) (by decide +kernel)
    have hs := split 1
    rw [e, h5, p1, neg_one_mul] at hs
    omega
  have hc : signedRow (h 2) y = h 0 y - 3 * h 2 y + 2 * h 3 y := by
    have e : signedRow (fiber z y) (pattern 2) = h 3 y + (h 0 y + -h 10 y) := by
      simpa only [zero 6 n6 y, one_mul, neg_one_mul, neg_zero, zero_add] using
        signed_row_four (fiber z y) 2 3 0 6 10 1 1 (-1) (-1) (by decide +kernel) (by decide +kernel)
    have hs := split 2
    rw [e, h10, p2, neg_one_mul, neg_neg] at hs
    omega
  have hd : signedRow (h 3) y = 3 * h 3 y + h 1 y - h 2 y := by
    have e : signedRow (fiber z y) (pattern 3) = h 2 y + -h 1 y := by
      simpa only [zero 7 n7 y, zero 11 n11 y, one_mul, neg_one_mul, add_zero] using
        signed_row_four (fiber z y) 3 2 1 7 11 1 (-1) 1 1 (by decide +kernel) (by decide +kernel)
    have hs := split 3
    rw [e, p3, one_mul] at hs
    omega
  refine ⟨h4, h5, h8, h10, h12, ha, hb, hc, hd, ?_⟩
  calc
    signedRow (fun v => h 1 v + h 2 v) y = signedRow (h 1) y + signedRow (h 2) y := by
      simp only [signedRow, mul_add, Finset.sum_add_distrib]
    _ = 2 * h 0 y - 3 * (h 1 y + h 2 y) := by
      rw [hb, hc]
      omega

#print axioms grid_projection_rows

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9GridProjectionRows
