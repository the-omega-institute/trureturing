/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricHighProfiles
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/SymmetricHighProfiles
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Girth]
   utility: none
   digest: Derive the actual high-neighbor square bound and the two possible side profiles A=(1,6,0) and B=(2,4,1). -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricHighTypes
import D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricTwentyTwoLocal
import Batteries.Tactic.OpenPrivate

/-! Internal actual-graph profiles for the symmetric twenty-two-point branch.
The square bound and every scalar-classification premise are derived from actual
local path bounds and weighted incidence. No profile is an input assumption. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricHighProfiles

open SimpleGraph GirthSliceCounting
open scoped BigOperators

attribute [local instance] Classical.propDecidable

open private degree_three_local_bound high_neighbor_weighted_double_count
  symmetric_high_counts from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricTwentyTwoLocal
open private count count_decompositions from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricHighTypes

variable {V : Type*} [Fintype V] [DecidableEq V]

private def highDegree (G : SimpleGraph V) (x : V) : ℕ :=
  (degreeThree G (G.neighborFinset x)).card

private def highTypeA (G : SimpleGraph V) (S : Finset V) : Prop :=
  ((S.filter fun x => highDegree G x = 1).card,
    (S.filter fun x => highDegree G x = 2).card,
    (S.filter fun x => highDegree G x = 3).card) = (1, 6, 0)

private def highTypeB (G : SimpleGraph V) (S : Finset V) : Prop :=
  ((S.filter fun x => highDegree G x = 1).card,
    (S.filter fun x => highDegree G x = 2).card,
    (S.filter fun x => highDegree G x = 3).card) = (2, 4, 1)

private def highProfile (G : SimpleGraph V) (S : Finset V) : Prop :=
  (S.filter fun x => highDegree G x = 0).card = 0 ∧
  (highTypeA G S ∨ highTypeB G S) ∧
  ∀ x ∈ S, highDegree G x ≠ 0 ∧ highDegree G x ≤ 3

private def zero_or_three_count (G : SimpleGraph V) (S : Finset V) : ℕ :=
  (S.filter fun x => highDegree G x = 0).card +
    (S.filter fun x => highDegree G x = 3).card

private def highDeficit (G : SimpleGraph V) (x : V) : ℤ :=
  (2 : ℤ) + (highDegree G x : ℤ) -
    ((∑ y ∈ degreeThree G (G.neighborFinset x), highDegree G y : ℕ) : ℤ)

variable {G : SimpleGraph V} {L R : Finset V}

private theorem high_degree_le_three {x : V} (hx : G.degree x = 3) :
    highDegree G x ≤ 3 := by
  calc
    highDegree G x ≤ (G.neighborFinset x).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = 3 := by rw [G.card_neighborFinset_eq_degree, hx]

private theorem opposite_square_bound
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False)
    (hg : (8 : ℕ∞) ≤ G.egirth) (hR : R.card = 11)
    (hcard : (degreeThree G L).card = 7)
    (hsum : (∑ x ∈ degreeThree G L, highDegree G x) = 13) :
    (∑ y ∈ degreeThree G R, (highDegree G y) ^ 2) ≤ 27 := by
  calc
    _ = ∑ x ∈ degreeThree G L,
        ∑ y ∈ degreeThree G (G.neighborFinset x), highDegree G y := by
      simpa only [highDegree] using (high_neighbor_weighted_double_count hpart).symm
    _ ≤ ∑ x ∈ degreeThree G L, (highDegree G x + 2) := by
      apply Finset.sum_le_sum
      intro x hx
      exact degree_three_local_bound hpart hdeg hlow hg hR
        (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hx).2
    _ = 27 := by
      rw [Finset.sum_add_distrib, hsum]
      simp [hcard]

private theorem square_sum_identity (S : Finset V)
    (hcard : S.card = 7) (hsum : (∑ x ∈ S, highDegree G x) = 13)
    (hbound : ∀ x ∈ S, highDegree G x ≤ 3) :
    (∑ x ∈ S, (highDegree G x) ^ 2) = 25 + 2 * zero_or_three_count G S := by
  obtain ⟨hc, hs, hq⟩ := count_decompositions S (highDegree G) hbound
  simp only [count] at hc hs hq
  dsimp only [zero_or_three_count]
  omega

private theorem side_deficit_sum
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hcard : (degreeThree G L).card = 7)
    (hsum : (∑ x ∈ degreeThree G L, highDegree G x) = 13)
    (hcardR : (degreeThree G R).card = 7)
    (hsumR : (∑ y ∈ degreeThree G R, highDegree G y) = 13)
    (hboundR : ∀ y ∈ degreeThree G R, highDegree G y ≤ 3) :
    (∑ x ∈ degreeThree G L, highDeficit G x) =
      2 - 2 * (zero_or_three_count G (degreeThree G R) : ℤ) := by
  have hweighted :
      (∑ x ∈ degreeThree G L,
        ∑ y ∈ degreeThree G (G.neighborFinset x), highDegree G y) =
      ∑ y ∈ degreeThree G R, (highDegree G y) ^ 2 :=
    high_neighbor_weighted_double_count hpart
  have hsquare := square_sum_identity (G := G) (degreeThree G R) hcardR hsumR hboundR
  calc
    _ = (2 : ℤ) * (degreeThree G L).card +
        ((∑ x ∈ degreeThree G L, highDegree G x : ℕ) : ℤ) -
        ((∑ x ∈ degreeThree G L,
          ∑ y ∈ degreeThree G (G.neighborFinset x), highDegree G y : ℕ) : ℤ) := by
      simp only [highDeficit, Finset.sum_sub_distrib, Finset.sum_add_distrib,
        Nat.cast_sum, Finset.sum_const, nsmul_eq_mul]
      ring
    _ = 2 - 2 * (zero_or_three_count G (degreeThree G R) : ℤ) := by
      rw [hcard, hsum, hweighted, hsquare]
      push_cast
      ring

private theorem high_deficit_nonnegative
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False)
    (hg : (8 : ℕ∞) ≤ G.egirth) (hR : R.card = 11)
    {x : V} (hx : x ∈ degreeThree G L) : 0 ≤ highDeficit G x := by
  have hb : (∑ y ∈ degreeThree G (G.neighborFinset x), highDegree G y) ≤
      highDegree G x + 2 :=
    degree_three_local_bound hpart hdeg hlow hg hR
      (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hx).2
  have hb' :
      ((∑ y ∈ degreeThree G (G.neighborFinset x), highDegree G y : ℕ) : ℤ) ≤
        (highDegree G x : ℤ) + 2 := by exact_mod_cast hb
  dsimp only [highDeficit]
  omega

/-- Both actual high-point sets have types A=(1,6,0) or B=(2,4,1),
nonzero high-neighbor degrees at most three, square sum at most twenty-seven,
and actual integer deficit totals determined by the opposite type. -/
private theorem symmetric_high_profiles
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False)
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (hL : L.card = 11) (hR : R.card = 11)
    (hL2 : (degreeTwo G L).card = 4) (hR2 : (degreeTwo G R).card = 4) :
    (∑ x ∈ degreeThree G L, (highDegree G x) ^ 2) ≤ 27 ∧
    (∑ y ∈ degreeThree G R, (highDegree G y) ^ 2) ≤ 27 ∧
    highProfile G (degreeThree G L) ∧ highProfile G (degreeThree G R) ∧
    (∀ x ∈ degreeThree G L, 0 ≤ highDeficit G x) ∧
    (∀ y ∈ degreeThree G R, 0 ≤ highDeficit G y) ∧
    (∑ x ∈ degreeThree G L, highDeficit G x) =
      2 - 2 * (zero_or_three_count G (degreeThree G R) : ℤ) ∧
    (∑ y ∈ degreeThree G R, highDeficit G y) =
      2 - 2 * (zero_or_three_count G (degreeThree G L) : ℤ) := by
  obtain ⟨hLc, hRc, hLs, hRs⟩ :=
    symmetric_high_counts hpart hdeg hlow hL hR hL2 hR2
  have hLb : ∀ x ∈ degreeThree G L, highDegree G x ≤ 3 := by
    intro x hx
    exact high_degree_le_three (Finset.mem_filter.mp hx).2
  have hRb : ∀ y ∈ degreeThree G R, highDegree G y ≤ 3 := by
    intro y hy
    exact high_degree_le_three (Finset.mem_filter.mp hy).2
  have hLq := opposite_square_bound hpart.symm hdeg hlow hg hL hRc hRs
  have hRq := opposite_square_bound hpart hdeg hlow hg hR hLc hLs
  obtain ⟨hL0, hLt, hLn⟩ := SymmetricHighTypes.high_type_classification
    (degreeThree G L) (highDegree G) hLc hLs hLb hLq
  obtain ⟨hR0, hRt, hRn⟩ := SymmetricHighTypes.high_type_classification
    (degreeThree G R) (highDegree G) hRc hRs hRb hRq
  have hLp : highProfile G (degreeThree G L) :=
    ⟨hL0, hLt, fun x hx => ⟨hLn x hx, hLb x hx⟩⟩
  have hRp : highProfile G (degreeThree G R) :=
    ⟨hR0, hRt, fun y hy => ⟨hRn y hy, hRb y hy⟩⟩
  refine ⟨hLq, hRq, hLp, hRp, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact high_deficit_nonnegative hpart hdeg hlow hg hR hx
  · intro y hy
    exact high_deficit_nonnegative hpart.symm hdeg hlow hg hL hy
  · exact side_deficit_sum hpart hLc hLs hRc hRs hRb
  · exact side_deficit_sum hpart.symm hRc hRs hLc hLs hLb

private theorem zero_or_three_of_typeA (S : Finset V)
    (hp : highProfile G S) (hA : highTypeA G S) :
    zero_or_three_count G S = 0 := by
  have hthree := congrArg (fun p : ℕ × ℕ × ℕ => p.2.2) hA
  change (S.filter fun x => highDegree G x = 3).card = 0 at hthree
  dsimp only [zero_or_three_count]
  rw [hp.1, hthree]

private theorem zero_or_three_of_typeB (S : Finset V)
    (hp : highProfile G S) (hB : highTypeB G S) :
    zero_or_three_count G S = 1 := by
  have hthree := congrArg (fun p : ℕ × ℕ × ℕ => p.2.2) hB
  change (S.filter fun x => highDegree G x = 3).card = 1 at hthree
  dsimp only [zero_or_three_count]
  rw [hp.1, hthree]

private theorem saturation_of_zero_total (S : Finset V)
    (hnonneg : ∀ x ∈ S, 0 ≤ highDeficit G x)
    (hsum : (∑ x ∈ S, highDeficit G x) = 0) :
    ∀ x ∈ S, (∑ y ∈ degreeThree G (G.neighborFinset x), highDegree G y) =
      highDegree G x + 2 := by
  intro x hx
  have hxle : highDeficit G x ≤ ∑ z ∈ S, highDeficit G z :=
    Finset.single_le_sum hnonneg hx
  rw [hsum] at hxle
  have hxnonneg := hnonneg x hx
  dsimp only [highDeficit] at hxle hxnonneg
  omega

/-- Type B on the opposite side forces every local inequality on this side
to saturate. Type A on the opposite side leaves total deficit exactly two. -/
private theorem symmetric_high_profile_saturation
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False)
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (hL : L.card = 11) (hR : R.card = 11)
    (hL2 : (degreeTwo G L).card = 4) (hR2 : (degreeTwo G R).card = 4) :
    (highTypeB G (degreeThree G R) →
      ∀ x ∈ degreeThree G L,
        (∑ y ∈ degreeThree G (G.neighborFinset x), highDegree G y) =
          highDegree G x + 2) ∧
    (highTypeB G (degreeThree G L) →
      ∀ y ∈ degreeThree G R,
        (∑ x ∈ degreeThree G (G.neighborFinset y), highDegree G x) =
          highDegree G y + 2) ∧
    (highTypeA G (degreeThree G R) →
      (∑ x ∈ degreeThree G L, highDeficit G x) = 2) ∧
    (highTypeA G (degreeThree G L) →
      (∑ y ∈ degreeThree G R, highDeficit G y) = 2) := by
  obtain ⟨_, _, hLp, hRp, hLn, hRn, hLs, hRs⟩ :=
    symmetric_high_profiles hpart hdeg hlow hg hL hR hL2 hR2
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hRB
    have hd := zero_or_three_of_typeB (degreeThree G R) hRp hRB
    have hz : (∑ x ∈ degreeThree G L, highDeficit G x) = 0 := by
      simpa [hd] using hLs
    exact saturation_of_zero_total (degreeThree G L) hLn hz
  · intro hLB
    have hd := zero_or_three_of_typeB (degreeThree G L) hLp hLB
    have hz : (∑ y ∈ degreeThree G R, highDeficit G y) = 0 := by
      simpa [hd] using hRs
    exact saturation_of_zero_total (degreeThree G R) hRn hz
  · intro hRA
    have hd := zero_or_three_of_typeA (degreeThree G R) hRp hRA
    simpa [hd] using hLs
  · intro hLA
    have hd := zero_or_three_of_typeA (degreeThree G L) hLp hLA
    simpa [hd] using hRs

end D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricHighProfiles
