/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9TenShadowExterior
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9TenShadowExterior
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Exterior signed rows exclude two normalized ten-pattern shadows. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TenShadowSelfAdjoint

/-! Two normalized ten-pattern projections arising in Hong–Wu–Xia,
arXiv:2610.09483v1, §7 Problem 2. The first loses code 2 at a one-term
exterior row. In the second, cubicity makes columns 3 and 4 disjoint,
and the signed suffix equations force them both to vanish. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TenShadowExterior

open Finset
open scoped BigOperators
open BalancedCriticalSpectrum (Q IsBalanced flip)
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open Q9SignedProjection (join fiber signedRow leftParitySign q9_balanced_signed_projection
  q9_signed_row_split)
open Q9ThetaProjection (leftCode)
open private pattern rightBlock leftCode_join join_blocks signed_row_four occupation row_degree from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9ThetaProjection
open private column fiber_occupied signedRow_pairing_symmetric from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TenShadowSelfAdjoint

/-- The normalized shadow whose exterior row at code 10 has a single term. -/
def tenShadowRowTen : Finset (BitVec 4) := {0, 1, 2, 3, 4, 7, 9, 12, 13, 15}

/-- The normalized shadow with coupled suffix rows at codes 3 and 4. -/
def tenShadowRowsThreeFour : Finset (BitVec 4) := {0, 1, 2, 3, 4, 5, 10, 13, 14, 15}

private theorem projection_avoid {C : Finset (Q 9)} {P : Finset (BitVec 4)}
    (hshadow : C.image leftCode = P) {k : BitVec 4} (hk : k ∉ P) (y : Q 5) :
    join (pattern k) y ∉ C := by
  intro hy
  exact hk (by simpa only [hshadow, leftCode_join] using mem_image_of_mem leftCode hy)

private theorem not_mem_projection_of_zero_column {C : Finset (Q 9)} {z : Q 9 → ℤ}
    (hunit : ∀ u ∈ C, z u = 1 ∨ z u = -1) (hzero : ∀ u ∉ C, z u = 0)
    {k : BitVec 4} (hk : ∀ y, column z k y = 0) : k ∉ C.image leftCode := by
  intro hmem
  obtain ⟨u, hu, rfl⟩ := mem_image.mp hmem
  have hjoin : join (pattern (leftCode u)) (rightBlock u) ∈ C := by rwa [join_blocks]
  exact (fiber_occupied hunit hzero _ _).mp hjoin (hk (rightBlock u))

open Classical in
/-- The exterior row at code 10 excludes this exact projection of a balanced induced
cubic support in the nine-cube. -/
theorem tenShadowRowTen_excluded {C : Finset (Q 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) : C.image leftCode ≠ tenShadowRowTen := by
  intro hshadow
  obtain ⟨z, hunit, hzero, _, hout⟩ := q9_balanced_signed_projection hr hb
  have outside : (10 : BitVec 4) ∉ tenShadowRowTen ∧ (11 : BitVec 4) ∉ tenShadowRowTen ∧
      (8 : BitVec 4) ∉ tenShadowRowTen ∧ (14 : BitVec 4) ∉ tenShadowRowTen := by
    decide +kernel
  obtain ⟨n10, n11, n8, n14⟩ := outside
  have zeroTwo (y : Q 5) : column z 2 y = 0 := by
    have e := signed_row_four (fiber z y) 10 11 8 14 2 1 1 (-1) (-1)
      (by decide +kernel) (by decide +kernel)
    simp only [hout _ (projection_avoid hshadow n10) y, fiber,
      hzero _ (projection_avoid hshadow n11 y), hzero _ (projection_avoid hshadow n8 y),
      hzero _ (projection_avoid hshadow n14 y), mul_zero, zero_add, neg_one_mul] at e
    change z (join (pattern 2) y) = 0
    omega
  exact not_mem_projection_of_zero_column hunit hzero zeroTwo
    (hshadow.symm ▸ (by decide +kernel : (2 : BitVec 4) ∈ tenShadowRowTen))

private theorem exterior_reconstruction (f : Q 4 → ℤ)
    (hf : ∀ k ∉ tenShadowRowsThreeFour, f (pattern k) = 0)
    (hr : ∀ k ∉ tenShadowRowsThreeFour, signedRow f (pattern k) = 0) :
    f (pattern 0) = -f (pattern 10) ∧
    f (pattern 1) = -f (pattern 13) ∧
    f (pattern 2) = f (pattern 13) + 2 * f (pattern 14) ∧
    f (pattern 3) = -f (pattern 10) - f (pattern 15) ∧
    f (pattern 4) = f (pattern 13) + f (pattern 14) ∧
    f (pattern 5) = -f (pattern 10) - 2 * f (pattern 15) := by
  have outside : (6 : BitVec 4) ∉ tenShadowRowsThreeFour ∧
      (7 : BitVec 4) ∉ tenShadowRowsThreeFour ∧ (8 : BitVec 4) ∉ tenShadowRowsThreeFour ∧
      (9 : BitVec 4) ∉ tenShadowRowsThreeFour ∧ (11 : BitVec 4) ∉ tenShadowRowsThreeFour ∧
      (12 : BitVec 4) ∉ tenShadowRowsThreeFour := by decide +kernel
  obtain ⟨n6, n7, n8, n9, n11, n12⟩ := outside
  have e6 := signed_row_four f 6 7 4 2 14 1 1 (-1) 1 (by decide +kernel) (by decide +kernel)
  have e7 := signed_row_four f 7 6 5 3 15 1 (-1) 1 (-1) (by decide +kernel) (by decide +kernel)
  have e8 := signed_row_four f 8 9 10 12 0 1 1 1 1 (by decide +kernel) (by decide +kernel)
  have e9 := signed_row_four f 9 8 11 13 1 1 (-1) (-1) (-1) (by decide +kernel) (by decide +kernel)
  have e11 := signed_row_four f 11 10 9 15 3 1 (-1) 1 1 (by decide +kernel) (by decide +kernel)
  have e12 := signed_row_four f 12 13 14 8 4 1 1 1 (-1) (by decide +kernel) (by decide +kernel)
  simp only [hr 6 n6, hr 7 n7, hr 8 n8, hr 9 n9, hr 11 n11, hr 12 n12,
    hf 6 n6, hf 7 n7, hf 8 n8, hf 9 n9, hf 11 n11, hf 12 n12,
    one_mul, neg_one_mul, neg_zero, zero_add] at e6 e7 e8 e9 e11 e12
  exact ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩

private theorem zero_of_paired_suffix_rows {f g : Q 5 → ℤ}
    (hf : ∀ y, signedRow f y = 3 * f y - 2 * g y)
    (hg : ∀ y, signedRow g y = 2 * f y - 3 * g y)
    (hfg : ∀ y, f y * g y = 0) : (∀ y, f y = 0) ∧ (∀ y, g y = 0) := by
  have left (y : Q 5) : signedRow f y * g y = -2 * (g y * g y) := by
    rw [hf, sub_mul, mul_assoc 3, mul_assoc 2, hfg, mul_zero, zero_sub, neg_mul]
  have right (y : Q 5) : f y * signedRow g y = 2 * (f y * f y) := by
    rw [hg, mul_sub, mul_left_comm (f y) 2, mul_left_comm (f y) 3, hfg, mul_zero, sub_zero]
  have h := signedRow_pairing_symmetric f g
  simp only [left, right, ← Finset.mul_sum] at h
  have nf : 0 ≤ ∑ y, f y * f y := sum_nonneg fun y _ => mul_self_nonneg (f y)
  have ng : 0 ≤ ∑ y, g y * g y := sum_nonneg fun y _ => mul_self_nonneg (g y)
  have zf : ∑ y, f y * f y = 0 := by omega
  have zg : ∑ y, g y * g y = 0 := by omega
  exact ⟨fun y => (sum_mul_self_eq_zero_iff univ f).mp zf y (mem_univ y),
    fun y => (sum_mul_self_eq_zero_iff univ g).mp zg y (mem_univ y)⟩

open Classical in
/-- Exterior reconstruction and the coupled suffix rows exclude this exact projection
of a balanced induced cubic support in the nine-cube. -/
theorem tenShadowRowsThreeFour_excluded {C : Finset (Q 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) : C.image leftCode ≠ tenShadowRowsThreeFour := by
  intro hshadow
  obtain ⟨z, hunit, hzero, hrow, hout⟩ := q9_balanced_signed_projection hr hb
  have avoid := fun k hk y => projection_avoid hshadow (k := k) hk y
  have exterior (k : BitVec 4) (hk : k ∉ tenShadowRowsThreeFour) (y : Q 5) :
      column z k y = 0 := hzero _ (avoid k hk y)
  have reconstruct (y : Q 5) :
      column z 0 y = -column z 10 y ∧
      column z 1 y = -column z 13 y ∧
      column z 2 y = column z 13 y + 2 * column z 14 y ∧
      column z 3 y = -column z 10 y - column z 15 y ∧
      column z 4 y = column z 13 y + column z 14 y ∧
      column z 5 y = -column z 10 y - 2 * column z 15 y :=
    exterior_reconstruction (fiber z y) (fun k hk => exterior k hk y)
      (fun k hk => hout _ (avoid k hk) y)
  have selected := fiber_occupied hunit hzero
  have flat (k : BitVec 4) (y : Q 5) : -1 ≤ column z k y ∧ column z k y ≤ 1 := by
    by_cases hy : join (pattern k) y ∈ C
    · change -1 ≤ z (join (pattern k) y) ∧ z (join (pattern k) y) ≤ 1
      rcases hunit _ hy with h | h <;> omega
    · have h : column z k y = 0 := hzero _ hy
      omega
  have same_occupation (y : Q 5) : occupation C 1 y = occupation C 13 y := by
    unfold occupation
    refine if_congr ?_ rfl rfl
    rw [selected 1 y, selected 13 y]
    rw [(reconstruct y).2.1, neg_ne_zero]
  -- Codes 1 and 13 have the same suffix degree in every occupied fiber.
  have disjoint (y : Q 5) : column z 3 y * column z 4 y = 0 := by
    by_contra hprod
    have h3 : column z 3 y ≠ 0 := fun h => hprod (by rw [h, zero_mul])
    have h4 : column z 4 y ≠ 0 := fun h => hprod (by rw [h, mul_zero])
    obtain ⟨e0, e1, e2, e3, e4, e5⟩ := reconstruct y
    have z15 : column z 15 y = 0 := by
      have := flat 10 y
      have := flat 5 y
      omega
    have h13 : column z 13 y ≠ 0 := by
      have := flat 2 y
      omega
    have m1 := (selected 1 y).mpr (show column z 1 y ≠ 0 by omega)
    have m13 := (selected 13 y).mpr h13
    have d1 := row_degree hr (k := 1) (a := 0) (b := 3) (c := 5) (d := 9)
      (by decide +kernel) m1
    have d13 := row_degree hr (k := 13) (a := 12) (b := 15) (c := 9) (d := 5)
      (by decide +kernel) m13
    have z9 := avoid 9 (by decide +kernel) y
    have z12 := avoid 12 (by decide +kernel) y
    have m15 : join (pattern 15) y ∉ C := fun h => (selected 15 y).mp h z15
    have m0 := (selected 0 y).mpr (show column z 0 y ≠ 0 by omega)
    have m3 := (selected 3 y).mpr h3
    have tails : (∑ j : Fin 5, occupation C 1 (flip y j)) =
        ∑ j : Fin 5, occupation C 13 (flip y j) :=
      sum_congr rfl fun j _ => same_occupation (flip y j)
    rw [← tails] at d13
    simp only [occupation, ite_eq_left m0, ite_eq_left m3, ite_eq_right z9,
      ite_eq_right z12, ite_eq_right m15] at d1 d13
    omega
  have suffix (y : Q 5) :
      signedRow (column z 3) y = 3 * column z 3 y - 2 * column z 4 y ∧
      signedRow (column z 4) y = 2 * column z 3 y - 3 * column z 4 y := by
    have row3 := signed_row_four (fiber z y) 3 2 1 7 11 1 (-1) 1 1
      (by decide +kernel) (by decide +kernel)
    have row4 := signed_row_four (fiber z y) 4 5 6 0 12 1 1 1 (-1)
      (by decide +kernel) (by decide +kernel)
    have n6 : (6 : BitVec 4) ∉ tenShadowRowsThreeFour := by decide +kernel
    have n7 : (7 : BitVec 4) ∉ tenShadowRowsThreeFour := by decide +kernel
    have n11 : (11 : BitVec 4) ∉ tenShadowRowsThreeFour := by decide +kernel
    have n12 : (12 : BitVec 4) ∉ tenShadowRowsThreeFour := by decide +kernel
    have r3 := q9_signed_row_split hrow (pattern 3) y
    have r4 := q9_signed_row_split hrow (pattern 4) y
    change 3 * column z 3 y = signedRow (fiber z y) (pattern 3) +
      leftParitySign (pattern 3) * signedRow (column z 3) y at r3
    change 3 * column z 4 y = signedRow (fiber z y) (pattern 4) +
      leftParitySign (pattern 4) * signedRow (column z 4) y at r4
    have p3 : leftParitySign (pattern 3) = 1 := by decide +kernel
    have p4 : leftParitySign (pattern 4) = -1 := by decide +kernel
    change signedRow (fiber z y) (pattern 3) = 1 * column z 2 y + (-1 * column z 1 y +
      (1 * column z 7 y + 1 * column z 11 y)) at row3
    change signedRow (fiber z y) (pattern 4) = 1 * column z 5 y + (1 * column z 6 y +
      (1 * column z 0 y + -1 * column z 12 y)) at row4
    rw [row3, p3, exterior 7 n7 y, exterior 11 n11 y] at r3
    rw [row4, p4, exterior 6 n6 y, exterior 12 n12 y] at r4
    obtain ⟨e0, e1, e2, e3, e4, e5⟩ := reconstruct y
    exact ⟨by omega, by omega⟩
  obtain ⟨zeroThree, _⟩ := zero_of_paired_suffix_rows
    (fun y => (suffix y).1) (fun y => (suffix y).2) disjoint
  exact not_mem_projection_of_zero_column hunit hzero zeroThree
    (hshadow.symm ▸ (by decide +kernel : (3 : BitVec 4) ∈ tenShadowRowsThreeFour))

#check tenShadowRowTen_excluded
#check tenShadowRowsThreeFour_excluded
#print axioms tenShadowRowTen_excluded
#print axioms tenShadowRowsThreeFour_excluded

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TenShadowExterior
