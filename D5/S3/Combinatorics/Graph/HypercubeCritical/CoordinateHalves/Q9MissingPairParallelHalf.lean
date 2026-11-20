/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9MissingPairParallelHalf
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9MissingPairParallelHalf
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Four normalized parallel stars force three TRUE halves of size twenty. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9MissingPairSignedFibers
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q7ParallelStarHalf
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9FourFiberSpectrum

/-! Counts the TRUE halves along the star axes when the opposite fiber contains four
normalized parallel stars. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9MissingPairParallelHalf

open scoped BigOperators
open Finset
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced flip)
open BalancedCubeComponentBoundary (directions regular_directions)
open Q9SignedProjection (signedRow)
open Q9MissingPairSignedFibers (prefixBits fiber q9_missing_pair_signed_fibers)
open Q7ParallelStarHalf (starIndicator true_half_card_of_parallel_stars)
open private mem_directions from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary
open private abs_prefixSign signedRow_eq_sum_directions from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9FourFiberSpectrum
open private flip_append_suffix sign_append_suffix from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9MissingPairSignedFibers
open private center center_indicator star_cases flip_append_left sign_append_left from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q7ParallelStarHalf

private theorem star_eq_center_or_flip : ∀ x : Q 3, starIndicator x = 1 →
    x = center ∨ ∃ i : Fin 3, x = flip center i := by
  decide +kernel

open Classical in
/-- At a selected vertex all three terms of the signed row attain the unit bound
after multiplying by the sign at that vertex. -/
private theorem edge_alignment {C : Finset (Q 9)} {z : Q 9 → ℤ}
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hunit : ∀ u ∈ C, z u = 1 ∨ z u = -1) (hzero : ∀ u ∉ C, z u = 0)
    (hrow : ∀ u, signedRow z u = 3 * z u)
    {u : Q 9} (hu : u ∈ C) (j : Fin 9) (hj : flip u j ∈ C) :
    truePrefixSign u j * z (flip u j) = z u := by
  let t (k : Fin 9) := z u * (truePrefixSign u k * z (flip u k))
  have hbound (k : Fin 9) (hk : k ∈ directions C u) : t k ≤ 1 := by
    apply (le_abs_self _).trans
    have ha : |z u| = 1 := by rcases hunit u hu with h | h <;> simp [h]
    have hb : |z (flip u k)| = 1 := by
      rcases hunit _ ((mem_directions C u k).mp hk) with h | h <;> simp [h]
    simp [t, abs_mul, abs_prefixSign, ha, hb]
  have hsum : (∑ k ∈ directions C u, t k) = ∑ _k ∈ directions C u, (1 : ℤ) := by
    simp only [t, ← mul_sum, ← signedRow_eq_sum_directions C hzero u, hrow u]
    rw [sum_const, regular_directions C hreg hu]
    rcases hunit u hu with h | h <;> norm_num [h]
  have he := (sum_eq_sum_iff_of_le hbound).mp hsum j ((mem_directions C u j).mpr hj)
  dsimp only [t] at he
  rcases hunit u hu with h | h <;> simp [h] at he ⊢ <;> omega

private theorem card_split_prefix (C : Finset (Q 9)) (p : Q 9 → Prop) [DecidablePred p] :
    (C.filter p).card = ∑ a : Bool, ∑ b : Bool,
      (univ.filter fun y : Q 7 => p (Fin.append (prefixBits a b) y) ∧
        Fin.append (prefixBits a b) y ∈ C).card := by
  have hfilter : (univ.filter fun u : Q 9 => p u ∧ u ∈ C) = C.filter p := by
    ext u
    simp [and_comm]
  let join : (Bool × Bool) × Q 7 ≃ Q 9 :=
    (Equiv.prodCongr (finTwoArrowEquiv Bool).symm (Equiv.refl (Q 7))).trans (Fin.appendEquiv 2 7)
  have hjoin (a b : Bool) (y : Q 7) : join ((a, b), y) = Fin.append (prefixBits a b) y := by
    change Fin.append ((finTwoArrowEquiv Bool).symm (a, b)) y = _
    congr 1
    funext j
    fin_cases j <;> rfl
  rw [← hfilter, card_filter,
    ← join.sum_comp (fun u => if p u ∧ u ∈ C then (1 : ℕ) else 0),
    Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp only [card_filter, hjoin]

open Classical in
/-- With prefix `11` absent, a TRUE prefix half of size 28 and four independent
normalized stars in the `00` fiber force a TRUE half of size 20 on each star axis. -/
theorem q9_missing_pair_parallel_true_half_card {C : Finset (Q 9)}
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (hmissing : ∀ y : Q 7, Fin.append (prefixBits true true) y ∉ C)
    (hhalf : (C.filter fun u => u 0 = true).card = 28)
    (centers : Finset (Q 4)) (hcenters : centers.card = 4)
    (hindependent : ∀ y ∈ centers, ∀ j : Fin 4, flip y j ∉ centers)
    (hstars : ∀ (x : Q 3) (y : Q 4),
      Fin.append (prefixBits false false) (Fin.append x y) ∈ C ↔
        starIndicator x = 1 ∧ y ∈ centers)
    (i : Fin 3) :
    (C.filter fun u => u ((i.castAdd 4).natAdd 2) = true).card = 20 := by
  obtain ⟨z, hunit, hzero, hrow, hcommon, hdouble⟩ :=
    q9_missing_pair_signed_fibers hreg hb hmissing
  have hmem (a b : Bool) (y : Q 7) :
      Fin.append (prefixBits a b) y ∈ C ↔ fiber z a b y ≠ 0 := by
    constructor
    · intro hy
      rcases hunit _ hy with h | h <;> simp [fiber, h]
    · intro hz
      by_contra hy
      exact hz (hzero _ hy)
  let ε (y : Q 4) := fiber z false false (Fin.append center y)
  have hε (y : Q 4) : ε y ≠ 0 ↔ y ∈ centers := by
    rw [← hmem]
    simpa only [center_indicator, true_and] using hstars center y
  have hfactor (x : Q 3) (y : Q 4) :
      fiber z false false (Fin.append x y) = starIndicator x * ε y := by
    rcases star_cases x with hx | hx
    · have hnot : Fin.append (prefixBits false false) (Fin.append x y) ∉ C := by
        intro hm
        have := ((hstars x y).mp hm).1
        omega
      simp [fiber, hzero _ hnot, hx]
    · by_cases hy : y ∈ centers
      · rw [hx, one_mul]
        rcases star_eq_center_or_flip x hx with rfl | ⟨j, rfl⟩
        · rfl
        · let u : Q 9 := Fin.append (prefixBits false false) (Fin.append center y)
          let k : Fin 9 := (j.castAdd 4).natAdd 2
          have hu : u ∈ C := (hstars center y).mpr ⟨center_indicator, hy⟩
          have hflip : flip u k =
              Fin.append (prefixBits false false) (Fin.append (flip center j) y) := by
            simp only [u, k, flip_append_suffix, flip_append_left]
          have hk : flip u k ∈ C := by
            rw [hflip]
            exact (hstars (flip center j) y).mpr ⟨hx, hy⟩
          have hsign : truePrefixSign u k = 1 := by
            dsimp only [u, k]
            rw [sign_append_suffix, sign_append_left]
            have hp : prefixBits false false = (fun _ => false) := by decide +kernel
            simp [hp, truePrefixSign, center]
          have hedge := edge_alignment hreg hunit hzero hrow hu k hk
          simpa only [hsign, one_mul, hflip, u, ε, fiber] using hedge
      · have hnot : Fin.append (prefixBits false false) (Fin.append x y) ∉ C :=
          fun hm => hy ((hstars x y).mp hm).2
        simp [fiber, hzero _ hnot, hx, not_ne_iff.mp (mt (hε y).mp hy)]
  have hcenterCard : (univ.filter fun y : Q 4 => ε y ≠ 0).card = 4 := by
    rw [show (univ.filter fun y : Q 4 => ε y ≠ 0) = centers by ext y; simp [hε], hcenters]
  have hcenterInd (y : Q 4) (hy : ε y ≠ 0) (j : Fin 4) : ε (flip y j) = 0 :=
    not_ne_iff.mp (mt (hε _).mp (hindependent y ((hε y).mp hy) j))
  have hfirst (a b : Bool) (y : Q 7) :
      Fin.append (prefixBits a b) y 0 = a := by
    change Fin.append (prefixBits a b) y ((0 : Fin 2).castAdd 7) = a
    rw [Fin.append_left]
    rfl
  have hcommonCard : (univ.filter fun y : Q 7 => fiber z true false y ≠ 0).card = 28 := by
    rw [card_split_prefix, Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool] at hhalf
    simpa only [hfirst, hmissing, false_and, true_and, Bool.true_eq_false, Bool.false_eq_true,
      and_true, and_false, filter_false, card_empty, add_zero, zero_add, hmem] using hhalf
  have hcard := true_half_card_of_parallel_stars hfactor hcenterCard hcenterInd
    hdouble hcommonCard i
  rw [card_split_prefix, Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool]
  simp only [Fin.append_right, hmissing, and_false, filter_false, card_empty, zero_add,
    hmem, ← hcommon]
  omega

#check q9_missing_pair_parallel_true_half_card
#print axioms q9_missing_pair_parallel_true_half_card

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9MissingPairParallelHalf
