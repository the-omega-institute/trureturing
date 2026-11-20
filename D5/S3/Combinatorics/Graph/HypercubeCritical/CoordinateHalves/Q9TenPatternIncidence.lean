/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9TenPatternIncidence
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9TenPatternIncidence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: The signed incidence and fiber cuts of a normalized ten-point projection. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9FourFiberSpectrum
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9ThetaProjection
import Batteries.Tactic.OpenPrivate

/-! The signed incidence structure of the normalized ten-point model for
Hong–Wu–Xia, §7 Problem 2. The four even patterns index the vertices of a
complete graph, with one odd midpoint for each of its six edges. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TenPatternIncidence

open scoped Matrix
open BalancedCriticalSpectrum (Q IsBalanced)
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open Q9FourFiberSpectrum (leftProjection fiber_and_signedRow_supported)
open Q9SignedProjection (join fiber signedRow q9_balanced_signed_projection)
open private pattern signed_row_four from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9ThetaProjection

private def tenCodes : Finset (BitVec 4) := {0, 1, 2, 4, 9, 10, 11, 12, 13, 14}

/-- The normalized ten-point projection in little-endian coordinates. -/
def tenProjection : Finset (Q 4) := tenCodes.map (cubeBitVec 4).toEmbedding

private theorem outside (k : BitVec 4) (hk : k ∉ tenCodes) : pattern k ∉ tenProjection :=
  fun h => hk ((Finset.mem_map' (cubeBitVec 4).toEmbedding).mp h)

/-- The exterior rows at codes 3, 5, 6 and 8 give three midpoint differences
and the zero sum on the four even codes. -/
theorem exterior_constraints {f : Q 4 → ℤ}
    (hf : ∀ x ∉ tenProjection, f x = 0)
    (hr : ∀ x ∉ tenProjection, signedRow f x = 0) :
    f (pattern 11) = f (pattern 1) - f (pattern 2) ∧
    f (pattern 13) = f (pattern 1) - f (pattern 4) ∧
    f (pattern 14) = f (pattern 2) - f (pattern 4) ∧
    f (pattern 0) + f (pattern 9) + f (pattern 10) + f (pattern 12) = 0 := by
  have row3 := signed_row_four f 3 2 1 7 11 1 (-1) 1 1
    (by decide +kernel) (by decide +kernel)
  have row5 := signed_row_four f 5 4 7 1 13 1 (-1) (-1) 1
    (by decide +kernel) (by decide +kernel)
  have row6 := signed_row_four f 6 7 4 2 14 1 1 (-1) 1
    (by decide +kernel) (by decide +kernel)
  have row8 := signed_row_four f 8 9 10 12 0 1 1 1 1
    (by decide +kernel) (by decide +kernel)
  simp only [hr _ (outside 3 (by decide +kernel)), hr _ (outside 5 (by decide +kernel)),
    hr _ (outside 6 (by decide +kernel)), hr _ (outside 8 (by decide +kernel)),
    hf _ (outside 7 (by decide +kernel)), one_mul, neg_one_mul, neg_zero, zero_add]
    at row3 row5 row6 row8
  exact ⟨by omega, by omega, by omega, by omega⟩

/-- The vertex codes of the complete graph, in order. -/
def vertexCode : Fin 4 → BitVec 4 := ![0, 9, 10, 12]

/-- The odd midpoint codes, in the order of the columns of `incidence`. -/
def midpointCode : Fin 6 → BitVec 4 := ![1, 2, 4, 11, 13, 14]

/-- The positive and negative endpoints of each midpoint in the TRUE-prefix signing. -/
def endpoints : Fin 6 → Fin 4 × Fin 4 :=
  ![(0, 1), (0, 2), (0, 3), (2, 1), (3, 1), (3, 2)]

/-- The signed incidence matrix from the six midpoints to the four vertices. -/
def incidence : Matrix (Fin 4) (Fin 6) ℤ := fun i e =>
  (if i = (endpoints e).1 then 1 else 0) - (if i = (endpoints e).2 then 1 else 0)

/-- Potentials at even codes `0`, `9`, `10`, `12`, in that order. -/
def potential (f : Q 4 → ℤ) : Fin 4 → ℤ :=
  ![0, -f (pattern 1), -f (pattern 2), -f (pattern 4)]

private theorem transpose_mulVec (a : Fin 4 → ℤ) (e : Fin 6) :
    (incidence.transpose *ᵥ a) e = a (endpoints e).1 - a (endpoints e).2 := by
  simp [Matrix.mulVec_apply_eq_sum, incidence, sub_mul, Finset.sum_sub_distrib]

private theorem endpoints_cover : ∀ i j : Fin 4, i ≠ j →
    ∃ e : Fin 6, endpoints e = (i, j) ∨ endpoints e = (j, i) := by
  decide +kernel

/-- The midpoint values are the signed incidence transpose applied to `potential`.
If each midpoint has absolute value at most one, the potentials lie in two
consecutive integer levels, and the nonzero midpoints are exactly their cut. -/
theorem midpoint_cut {f : Q 4 → ℤ}
    (hf : ∀ x ∉ tenProjection, f x = 0)
    (hr : ∀ x ∉ tenProjection, signedRow f x = 0)
    (hunit : ∀ e, |f (pattern (midpointCode e))| ≤ 1) :
    (fun e => f (pattern (midpointCode e))) = incidence.transpose *ᵥ potential f ∧
    (∀ i j, |potential f i - potential f j| ≤ 1) ∧
    ∃ (level : ℤ) (side : Fin 4 → Bool),
      (∀ i, potential f i = level + if side i then 1 else 0) ∧
      (∀ e, f (pattern (midpointCode e)) ≠ 0 ↔ side (endpoints e).1 ≠ side (endpoints e).2) := by
  obtain ⟨h11, h13, h14, _⟩ := exterior_constraints hf hr
  have hdiff (e : Fin 6) :
      f (pattern (midpointCode e)) = potential f (endpoints e).1 - potential f (endpoints e).2 := by
    fin_cases e
    · simp [midpointCode, potential, endpoints]
    · simp [midpointCode, potential, endpoints]
    · simp [midpointCode, potential, endpoints]
    · change f (pattern 11) = -f (pattern 2) - -f (pattern 1)
      omega
    · change f (pattern 13) = -f (pattern 4) - -f (pattern 1)
      omega
    · change f (pattern 14) = -f (pattern 4) - -f (pattern 2)
      omega
  have hspan (i j : Fin 4) : |potential f i - potential f j| ≤ 1 := by
    by_cases hij : i = j
    · simp [hij]
    · obtain ⟨e, he | he⟩ := endpoints_cover i j hij
      · simpa only [hdiff e, he] using hunit e
      · simpa only [hdiff e, he, abs_sub_comm] using hunit e
  obtain ⟨low, _, hlow⟩ := Finset.exists_min_image Finset.univ (potential f)
    ⟨0, Finset.mem_univ 0⟩
  let side (i : Fin 4) := decide (potential f low < potential f i)
  have hlevel (i : Fin 4) : potential f i = potential f low + if side i then 1 else 0 := by
    have hmin := hlow i (Finset.mem_univ i)
    have hmax := (abs_le.mp (hspan i low)).2
    by_cases hi : potential f low < potential f i <;> simp [side, hi] <;> omega
  refine ⟨funext fun e => (hdiff e).trans (transpose_mulVec _ e).symm,
    hspan, potential f low, side, hlevel, fun e => ?_⟩
  rw [hdiff, hlevel (endpoints e).1, hlevel (endpoints e).2]
  cases side (endpoints e).1 <;> cases side (endpoints e).2 <;> simp

-- The same incidence matrix gives both off-diagonal blocks of the signed row.
private theorem signed_row_blocks {f : Q 4 → ℤ} (hf : ∀ x ∉ tenProjection, f x = 0) :
    (fun i => signedRow f (pattern (vertexCode i))) =
      incidence *ᵥ (fun e => f (pattern (midpointCode e))) ∧
    (fun e => signedRow f (pattern (midpointCode e))) =
      incidence.transpose *ᵥ (fun i => f (pattern (vertexCode i))) := by
  have zero (k : BitVec 4) (hk : k ∉ tenCodes) : f (pattern k) = 0 := hf _ (outside k hk)
  have row0 := signed_row_four f 0 1 2 4 8 1 1 1 1
    (by decide +kernel) (by decide +kernel)
  have row9 := signed_row_four f 9 8 11 13 1 1 (-1) (-1) (-1)
    (by decide +kernel) (by decide +kernel)
  have row10 := signed_row_four f 10 11 8 14 2 1 1 (-1) (-1)
    (by decide +kernel) (by decide +kernel)
  have row12 := signed_row_four f 12 13 14 8 4 1 1 1 (-1)
    (by decide +kernel) (by decide +kernel)
  simp only [zero 8 (by decide +kernel), one_mul, neg_one_mul, zero_add, add_zero]
    at row0 row9 row10 row12
  have row1 := signed_row_four f 1 0 3 5 9 1 (-1) (-1) (-1)
    (by decide +kernel) (by decide +kernel)
  have row2 := signed_row_four f 2 3 0 6 10 1 1 (-1) (-1)
    (by decide +kernel) (by decide +kernel)
  have row4 := signed_row_four f 4 5 6 0 12 1 1 1 (-1)
    (by decide +kernel) (by decide +kernel)
  have row11 := signed_row_four f 11 10 9 15 3 1 (-1) 1 1
    (by decide +kernel) (by decide +kernel)
  have row13 := signed_row_four f 13 12 15 9 5 1 (-1) (-1) 1
    (by decide +kernel) (by decide +kernel)
  have row14 := signed_row_four f 14 15 12 10 6 1 1 (-1) 1
    (by decide +kernel) (by decide +kernel)
  simp only [zero 3 (by decide +kernel), zero 5 (by decide +kernel), zero 6 (by decide +kernel),
    zero 15 (by decide +kernel), one_mul, neg_one_mul, neg_zero, zero_add, add_zero]
    at row1 row2 row4 row11 row13 row14
  constructor
  · funext i
    fin_cases i <;>
      simp [Matrix.mulVec_apply_eq_sum, incidence, endpoints, vertexCode, midpointCode,
        Fin.sum_univ_succ] at row0 row9 row10 row12 ⊢ <;> omega
  · funext e
    rw [transpose_mulVec]
    fin_cases e
    · change signedRow f (pattern 1) = f (pattern 0) - f (pattern 9)
      simpa only [sub_eq_add_neg] using row1
    · change signedRow f (pattern 2) = f (pattern 0) - f (pattern 10)
      simpa only [sub_eq_add_neg] using row2
    · change signedRow f (pattern 4) = f (pattern 0) - f (pattern 12)
      simpa only [sub_eq_add_neg] using row4
    · change signedRow f (pattern 11) = f (pattern 10) - f (pattern 9)
      simpa only [sub_eq_add_neg] using row11
    · change signedRow f (pattern 13) = f (pattern 12) - f (pattern 9)
      simpa only [sub_eq_add_neg] using row13
    · change signedRow f (pattern 14) = f (pattern 12) - f (pattern 10)
      simpa only [sub_eq_add_neg] using row14

open Classical in
/-- Every suffix fiber of a Huang-balanced induced cubic support with the normalized
ten-point projection has zero even sum, the two signed incidence blocks, and a cut
on the four even patterns whose cross-edges are exactly the occupied odd patterns. -/
theorem balanced_fibers_incidence_cut {C : Finset (Q 9)}
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (hP : leftProjection C = tenProjection) :
    ∃ z : Q 9 → ℤ,
      (∀ u ∈ C, z u = 1 ∨ z u = -1) ∧ (∀ u ∉ C, z u = 0) ∧
      (∀ u, signedRow z u = 3 * z u) ∧
      ∀ y : Q 5,
        let f := fiber z y
        let a := fun i => f (pattern (vertexCode i))
        let m := fun e => f (pattern (midpointCode e))
        a 0 + a 1 + a 2 + a 3 = 0 ∧
        (fun i => signedRow f (pattern (vertexCode i))) = incidence *ᵥ m ∧
        (fun e => signedRow f (pattern (midpointCode e))) = incidence.transpose *ᵥ a ∧
        m = incidence.transpose *ᵥ potential f ∧
        (∀ i j, |potential f i - potential f j| ≤ 1) ∧
        ∃ (level : ℤ) (side : Fin 4 → Bool),
          (∀ i, potential f i = level + if side i then 1 else 0) ∧
          (∀ e, join (pattern (midpointCode e)) y ∈ C ↔
            side (endpoints e).1 ≠ side (endpoints e).2) := by
  obtain ⟨z, hunit, hzero, hrow, _⟩ := q9_balanced_signed_projection hreg hb
  refine ⟨z, hunit, hzero, hrow, fun y => ?_⟩
  have supported (x : Q 4) (hx : x ∉ tenProjection) :
      fiber z y x = 0 ∧ signedRow (fiber z y) x = 0 :=
    fiber_and_signedRow_supported hzero hrow y (hP.symm ▸ hx)
  have hf (x : Q 4) (hx : x ∉ tenProjection) := (supported x hx).1
  have hr (x : Q 4) (hx : x ∉ tenProjection) := (supported x hx).2
  have absolute (e : Fin 6) : |fiber z y (pattern (midpointCode e))| ≤ 1 := by
    change |z (join (pattern (midpointCode e)) y)| ≤ 1
    by_cases he : join (pattern (midpointCode e)) y ∈ C
    · rcases hunit _ he with h | h <;> simp [h]
    · simp [hzero _ he]
  obtain ⟨_, _, _, hsum⟩ := exterior_constraints hf hr
  obtain ⟨hrowEven, hrowOdd⟩ := signed_row_blocks hf
  obtain ⟨hgradient, hspan, level, side, hlevel, hcut⟩ := midpoint_cut hf hr absolute
  refine ⟨hsum, hrowEven, hrowOdd, hgradient, hspan, level, side, hlevel, fun e => ?_⟩
  rw [← hcut]
  change join (pattern (midpointCode e)) y ∈ C ↔ z (join (pattern (midpointCode e)) y) ≠ 0
  constructor
  · intro he
    rcases hunit _ he with h | h <;> simp [h]
  · intro he
    by_contra hn
    exact he (hzero _ hn)

#print axioms exterior_constraints
#print axioms midpoint_cut
#print axioms balanced_fibers_incidence_cut

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TenPatternIncidence
