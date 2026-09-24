/- GID: D5/S3/Combinatorics/Interpolation/AbrIteratedOrder
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Interpolation/AbrIteratedOrder
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Iterated ABR order preservation and integer triangularity. -/

import D5.S3.Combinatorics.Interpolation.AbrResidualPartition

/-!
The order lemmas here are the formal content of ABR Lemma 3.3.  They turn the
one-factor result into an iterated triangular system without changing the
coordinate-box filtration.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Interpolation.AbrIteratedTriangularity

open scoped BigOperators Pointwise
open MvPolynomial
open D5.S1.Words.Patterns.Separable.CutFactorization
open D5.S3.Combinatorics.Interpolation.AbrCoordinateBoxStraightening
open D5.S3.Combinatorics.Interpolation.AbrResidualPartition

theorem abrLower_trans {n : Nat} {a b c : Fin n →₀ Nat}
    (hab : AbrLower a b) (hbc : AbrLower b c) : AbrLower a c := by
  classical
  have htrans {u v w : Fin n →₀ Nat}
      (huv : DominatedBy u v) (hvw : DominatedBy v w) : DominatedBy u w :=
    ⟨huv.1.trans hvw.1, fun k => (huv.2 k).trans (hvw.2 k)⟩
  have hsortedDom {u v : Fin n →₀ Nat}
      (hsorted : (fun i => u (indexPerm u i)) = fun i => v (indexPerm v i)) :
      DominatedBy u v := by
    constructor
    · calc
        (∑ x, u x) = ∑ i, u (indexPerm u i) := by
          symm
          exact Fintype.sum_equiv (indexPerm u)
            (fun i => u (indexPerm u i)) (fun x => u x) (fun _ => rfl)
        _ = ∑ i, v (indexPerm v i) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [congrFun hsorted i]
        _ = ∑ x, v x := by
          exact Fintype.sum_equiv (indexPerm v)
            (fun i => v (indexPerm v i)) (fun x => v x) (fun _ => rfl)
    · intro k
      unfold prefixWeight
      apply le_of_eq
      apply Finset.sum_congr rfl
      intro i _
      rw [congrFun hsorted i]
  rcases hab with hab | hab <;> rcases hbc with hbc | hbc
  · left
    refine ⟨htrans hab.1 hbc.1, ?_⟩
    intro hca
    exact hab.2 (htrans hbc.1 hca)
  · left
    have hbcDom := hsortedDom hbc.1
    refine ⟨htrans hab.1 hbcDom, ?_⟩
    intro hca
    exact hab.2 (htrans hbcDom hca)
  · left
    have habDom := hsortedDom hab.1
    refine ⟨htrans habDom hbc.1, ?_⟩
    intro hca
    exact hbc.2 (htrans hca habDom)
  · right
    exact ⟨hab.1.trans hbc.1, lt_trans hbc.2 hab.2⟩

theorem abrLower_leadExponent {n : Nat} {a b : Fin n →₀ Nat}
    (hab : AbrLower a b) (h : Nat) :
    AbrLower (leadExponent a h) (leadExponent b h) := by
  classical
  have hsumSubset (s t : Finset (Fin n)) :
      (∑ x ∈ s, subsetExponent t x) = (s ∩ t).card := by
    simp [subsetExponent, Finsupp.indicator_apply, Finset.card_inter]
  have hcardInitialGeneral (u : Fin n →₀ Nat) (m : Nat) :
      (initialSet u m).card = min n m := by
    let e := indexPerm u
    have himage : initialSet u m =
        (Finset.univ.filter fun i : Fin n => i.val < m).image e := by
      ext x
      simp only [initialSet, Finset.mem_image, Finset.mem_filter,
        Finset.mem_univ, true_and, e]
      constructor
      · intro hx
        exact ⟨(indexPerm u).symm x, hx, by simp⟩
      · rintro ⟨i, hi, rfl⟩
        simpa using hi
    rw [himage, Finset.card_image_of_injective _ e.injective]
    exact Fin.card_filter_val_lt
  have hlead {u v : Fin n →₀ Nat} (huv : DominatedBy u v) :
      DominatedBy (leadExponent u h) (leadExponent v h) := by
    constructor
    · change (Finset.univ.sum fun x : Fin n =>
          u x + subsetExponent (initialSet u h) x) =
        Finset.univ.sum fun x : Fin n =>
          v x + subsetExponent (initialSet v h) x
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        hsumSubset, hsumSubset]
      simp [huv.1, hcardInitialGeneral]
    · intro k
      rw [prefixWeight_leadExponent, prefixWeight_leadExponent]
      exact Nat.add_le_add_right (huv.2 k) _
  rcases hab with hab | hab
  · left
    refine ⟨hlead hab.1, ?_⟩
    intro hreverse
    apply hab.2
    constructor
    · exact hab.1.1.symm
    · intro k
      have hk := hreverse.2 k
      rw [prefixWeight_leadExponent, prefixWeight_leadExponent] at hk
      omega
  · right
    constructor
    · funext i
      rw [indexPerm_leadExponent, indexPerm_leadExponent]
      simp only [leadExponent, Finsupp.add_apply, subsetExponent,
        Finsupp.indicator_apply, initialSet, Finset.mem_filter, Finset.mem_univ,
        Equiv.symm_apply_apply, true_and, congrFun hab.1 i]
    · rw [indexPerm_leadExponent, indexPerm_leadExponent]
      exact hab.2


end D5.S3.Combinatorics.Interpolation.AbrIteratedTriangularity
