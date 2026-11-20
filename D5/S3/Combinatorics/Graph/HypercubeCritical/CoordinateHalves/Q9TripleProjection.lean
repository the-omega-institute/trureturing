/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9TripleProjection
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9TripleProjection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: A half-size bound from two omitted triple patterns at distance two. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9SignedProjection
import Batteries.Tactic.OpenPrivate

/-! Exterior signed rows for the omitted patterns `001` and `111`
give two disjoint translations of the TRUE half into the FALSE half. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TripleProjection

open scoped BigOperators
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced flip flip_apply_same flip_flip)
open Q9SignedProjection (signedRow)
open private flip_comm from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth

private theorem flip_apply_of_ne (x : Q 9) {i j : Fin 9} (h : j ≠ i) :
    flip x i j = x j :=
  Function.update_of_ne h _ _

private theorem index_lt_one (i : Fin 9) : i < 1 ↔ i = 0 := by
  constructor
  · intro h
    change i.val < 1 at h
    exact Fin.ext (Nat.lt_one_iff.mp h)
  · rintro rfl
    decide

section PrefixSigns

attribute [local instance] Classical.propDecidable

private theorem prefix_sign_zero (x : Q 9) : truePrefixSign x 0 = 1 := by
  simp [truePrefixSign]

private theorem prefix_sign_one (x : Q 9) :
    truePrefixSign x 1 = if x 0 = true then -1 else 1 := by
  have hfilter :
      (Finset.univ.filter (fun i : Fin 9 => i < 1 ∧ x i = true)) =
        ({0} : Finset (Fin 9)).filter (fun i => x i = true) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, index_lt_one]
  rw [truePrefixSign, hfilter, Finset.filter_singleton]
  by_cases h : x 0 = true <;> simp [h]

private theorem prefix_sign_unit (x : Q 9) (i : Fin 9) :
    truePrefixSign x i = 1 ∨ truePrefixSign x i = -1 := by
  unfold truePrefixSign
  exact neg_one_pow_eq_or ℤ _

end PrefixSigns

private theorem row_three (z : Q 9 → ℤ) (x : Q 9)
    (hzero : ∀ y : Q 9, y 0 = x 0 → y 1 = x 1 → y 2 = x 2 → z y = 0) :
    signedRow z x =
      z (flip x 0) + truePrefixSign x 1 * z (flip x 1) +
        truePrefixSign x 2 * z (flip x 2) := by
  have htail (i : Fin 6) : z (flip x (i.natAdd 3)) = 0 := by
    have hne (j : Fin 9) (hj : j.val < 3) : j ≠ i.natAdd 3 := by
      intro h
      have hval := congrArg Fin.val h
      change j.val = 3 + i.val at hval
      omega
    exact hzero _ (flip_apply_of_ne x (hne 0 (by decide)))
      (flip_apply_of_ne x (hne 1 (by decide))) (flip_apply_of_ne x (hne 2 (by decide)))
  rw [signedRow, Fin.sum_univ_add (a := 3) (b := 6), Fin.sum_univ_three]
  change truePrefixSign x 0 * z (flip x 0) + truePrefixSign x 1 * z (flip x 1) +
    truePrefixSign x 2 * z (flip x 2) +
    (∑ i : Fin 6, truePrefixSign x (i.natAdd 3) * z (flip x (i.natAdd 3))) = _
  simp only [prefix_sign_zero, one_mul, htail, mul_zero, Finset.sum_const_zero, add_zero]

private theorem solve_exterior_rows {a b w p q c d : ℤ}
    (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1)
    (hp : -1 ≤ c * p ∧ c * p ≤ 1) (hq : -1 ≤ d * q ∧ d * q ≤ 1)
    (hu : a + b * w + c * p = 0) (hv : w + (-b) * a + d * q = 0) :
    w = 0 ∧ p ≠ 0 ∧ q ≠ 0 := by
  obtain ⟨hp_lower, hp_upper⟩ := hp
  obtain ⟨hq_lower, hq_upper⟩ := hq
  have hw : w = 0 := by
    rcases hb with hb | hb <;> rcases ha with ha | ha <;>
      simp only [ha, hb, one_mul, neg_one_mul, neg_neg] at hu hv <;> omega
  refine ⟨hw, ?_, ?_⟩
  · intro h
    have haz : a = 0 := by simpa only [hw, h, mul_zero, add_zero] using hu
    rcases ha with ha | ha <;> omega
  · intro h
    have hba : (-b) * a = 0 := by simpa only [hw, h, mul_zero, zero_add, add_zero] using hv
    rcases mul_eq_zero.mp hba with hbz | haz
    · rcases hb with hb | hb <;> omega
    · rcases ha with ha | ha <;> omega

open Classical in
/-- An order-72 balanced induced cubic support omitting `001` and `111`
in coordinates `0, 1, 2` has at most 24 vertices with coordinate `2` TRUE.
This gives a normalized triple-projection restriction for Hong–Wu–Xia, §7 Problem 2. -/
theorem true_half_card_le_of_missing_001_111 {S : Finset (Q 9)} (hsize : S.card = 72)
    (hreg : ((hypercube 9).induce (S : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced S)
    (h001 : ∀ x : Q 9, x 0 = false → x 1 = false → x 2 = true → x ∉ S)
    (h111 : ∀ x : Q 9, x 0 = true → x 1 = true → x 2 = true → x ∉ S) :
    (S.filter (fun x => x 2 = true)).card ≤ 24 := by
  classical
  obtain ⟨z, hunit, hzero, _, hz⟩ := q9_integral_true_prefix_switching hreg hb
  have exterior (y : Q 9) (h01 : y 0 = y 1) (h2 : y 2 = true) : y ∉ S := by
    rcases Bool.eq_false_or_eq_true (y 0) with h0 | h0
    · exact h111 y h0 (h01.symm.trans h0) h2
    · exact h001 y h0 (h01.symm.trans h0) h2
  have exterior_row (y : Q 9) (h01 : y 0 = y 1) (h2 : y 2 = true) :
      z (flip y 0) + truePrefixSign y 1 * z (flip y 1) +
        truePrefixSign y 2 * z (flip y 2) = 0 := by
    have hrow : signedRow z y = 3 * z y := hz y
    have hvanish (t : Q 9) (h0 : t 0 = y 0) (h1 : t 1 = y 1) (h2' : t 2 = y 2) :
        z t = 0 :=
      hzero t (exterior t (h0.trans (h01.trans h1.symm)) (h2'.trans h2))
    rw [row_three z y hvanish, hzero y (exterior y h01 h2), mul_zero] at hrow
    exact hrow
  have signed_bounds (y : Q 9) :
      -1 ≤ truePrefixSign y 2 * z (flip y 2) ∧ truePrefixSign y 2 * z (flip y 2) ≤ 1 := by
    have hlabel : -1 ≤ z (flip y 2) ∧ z (flip y 2) ≤ 1 := by
      by_cases hy : flip y 2 ∈ S
      · rcases hunit _ hy with h | h <;> constructor <;> omega
      · have h := hzero _ hy
        constructor <;> omega
    obtain ⟨hlo, hhi⟩ := hlabel
    rcases prefix_sign_unit y 2 with h | h <;>
      simp only [h, one_mul, neg_one_mul] <;> constructor <;> omega
  let upper := S.filter (fun x => x 2 = true)
  let move (i : Fin 9) (x : Q 9) := flip (flip x i) 2
  -- At each selected upper vertex, the two other sides of the forbidden rows
  -- give selected lower vertices and exclude the double flip in coordinates 0 and 1.
  have local_moves (x : Q 9) (hx : x ∈ upper) :
      flip (flip x 0) 1 ∉ S ∧ move 0 x ∈ S ∧ move 1 x ∈ S := by
    obtain ⟨hxS, hx2⟩ := Finset.mem_filter.mp hx
    have hne : x 0 ≠ x 1 := fun h => exterior x h hx2 hxS
    have hbits : (!x 0) = x 1 ∧ x 0 = (!x 1) := by
      cases h0 : x 0 <;> cases h1 : x 1 <;> simp [h0, h1] at hne ⊢
    let u := flip x 0
    let v := flip x 1
    let w := flip u 1
    have hu0 : u 0 = !x 0 := flip_apply_same x 0
    have hv0 : v 0 = x 0 := flip_apply_of_ne x (i := 1) (j := 0) (by decide)
    have hu1 : u 1 = x 1 := flip_apply_of_ne x (i := 0) (j := 1) (by decide)
    have hv1 : v 1 = !x 1 := flip_apply_same x 1
    have hu2 : u 2 = true := (flip_apply_of_ne x (i := 0) (j := 2) (by decide)).trans hx2
    have hv2 : v 2 = true := (flip_apply_of_ne x (i := 1) (j := 2) (by decide)).trans hx2
    have hsign : truePrefixSign v 1 = -truePrefixSign u 1 := by
      rw [prefix_sign_one, prefix_sign_one, hu0, hv0]
      cases x 0 <;> simp
    have hru := exterior_row u (hu0.trans (hbits.1.trans hu1.symm)) hu2
    have hrv := exterior_row v (hv0.trans (hbits.2.trans hv1.symm)) hv2
    have hux : flip u 0 = x := flip_flip x 0
    have hvx : flip v 1 = x := flip_flip x 1
    have hvw : flip v 0 = w := flip_comm x 1 0
    rw [hux] at hru
    rw [hvw, hvx, hsign] at hrv
    have ⟨hw, hp, hq⟩ := solve_exterior_rows (hunit x hxS) (prefix_sign_unit u 1)
      (signed_bounds u) (signed_bounds v) hru hrv
    refine ⟨?_, ?_, ?_⟩
    · intro hwS
      change z w = 0 at hw
      rcases hunit w hwS with h | h <;> omega
    · by_contra h
      exact hp (hzero _ h)
    · by_contra h
      exact hq (hzero _ h)
  have flip_injective (i : Fin 9) : Function.Injective (fun x : Q 9 => flip x i) :=
    (show Function.Involutive (fun x : Q 9 => flip x i) from fun x => flip_flip x i).injective
  have move_injective (i : Fin 9) : Function.Injective (move i) :=
    (flip_injective 2).comp (flip_injective i)
  have upper_disjoint (i : Fin 9) (hi : (2 : Fin 9) ≠ i) :
      Disjoint upper (upper.image (move i)) := by
    refine Finset.disjoint_left.mpr ?_
    intro y hy hyImage
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hyImage
    have hx2 : x 2 = true := (Finset.mem_filter.mp hx).2
    have hy2 : flip (flip x i) 2 2 = true := (Finset.mem_filter.mp hy).2
    rw [flip_apply_same, flip_apply_of_ne x hi, hx2] at hy2
    cases hy2
  let image0 := upper.image (move 0)
  let image1 := upper.image (move 1)
  -- A collision would select both an upper vertex and its excluded double flip.
  have images_disjoint : Disjoint image0 image1 := by
    refine Finset.disjoint_left.mpr ?_
    intro t h0 h1
    obtain ⟨x, hx, hxt⟩ := Finset.mem_image.mp h0
    obtain ⟨y, hy, hyt⟩ := Finset.mem_image.mp h1
    have hxy : flip x 0 = flip y 1 := flip_injective 2 (hxt.trans hyt.symm)
    have hw : flip (flip x 0) 1 = y := by rw [hxy, BalancedCriticalSpectrum.flip_flip]
    exact (local_moves x hx).1 (hw.symm ▸ (Finset.mem_filter.mp hy).1)
  have upper_disjoint_images : Disjoint upper (image0 ∪ image1) :=
    Finset.disjoint_union_right.mpr ⟨upper_disjoint 0 (by decide), upper_disjoint 1 (by decide)⟩
  have union_subset : upper ∪ (image0 ∪ image1) ⊆ S := by
    intro y hy
    rcases Finset.mem_union.mp hy with hy | hy
    · exact (Finset.mem_filter.mp hy).1
    · rcases Finset.mem_union.mp hy with hy | hy
      · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
        exact (local_moves x hx).2.1
      · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
        exact (local_moves x hx).2.2
  have hcount := Finset.card_le_card union_subset
  rw [Finset.card_union_of_disjoint upper_disjoint_images,
    Finset.card_union_of_disjoint images_disjoint, hsize] at hcount
  change upper.card + ((upper.image (move 0)).card + (upper.image (move 1)).card) ≤ 72 at hcount
  rw [Finset.card_image_of_injective _ (move_injective 0),
    Finset.card_image_of_injective _ (move_injective 1)] at hcount
  change upper.card ≤ 24
  omega

#print axioms true_half_card_le_of_missing_001_111

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TripleProjection
