/- GID: D5/S3/Geometry/FiniteGeometry/AffineBlockingBound
   generality: G
   mirror-B: D5/B/S3/Geometry/FiniteGeometry/AffineBlockingBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Affine blocking sets over a finite field of order q have sharp minimum 2q-1. -/

import D5.S3.Geometry.FiniteGeometry.AffinePlaneLines
import Mathlib.FieldTheory.ChevalleyWarning

/- proof_shape: affine_blocking_minimum: content
   admission_basis: escape-witness
   The incidence condition constructs a dual polynomial supported exactly at zero.
   Its geometric vanishing certificate is used by MvPolynomial.sum_eval_eq_zero.
   Translation, degree bounds, and the attaining axes stay inside this proof. -/

namespace D5.S3.Geometry.FiniteGeometry.AffineBlockingBound

open AffinePlaneLines MvPolynomial
open scoped BigOperators

/-- The sharp Jamison--Brouwer--Schrijver minimum in the coordinate affine plane. -/
theorem affine_blocking_minimum {F : Type*} [Field F] [Fintype F] :
    IsLeast {n : ℕ | ∃ B : Finset (F × F),
      (∀ ℓ : AffineLine F, ∃ p ∈ B, p ∈ ℓ) ∧ B.card = n}
      (2 * Fintype.card F - 1) := by
  classical
  constructor
  · let A : Finset (F × F) := Finset.univ.product {0}
    let C : Finset (F × F) := Finset.product {0} Finset.univ
    refine ⟨A ∪ C, ?_, ?_⟩
    · intro ℓ
      cases ℓ with
      | graph m b =>
          refine ⟨(0, b), Finset.mem_union_right _ ?_, ?_⟩
          · simp [C]
          · change b = m * 0 + b
            simp
      | vertical c =>
          refine ⟨(c, 0), Finset.mem_union_left _ ?_, ?_⟩
          · simp [A]
          · rfl
    · have hI : A ∩ C = {(0, 0)} := by
        ext p
        simp [A, C, Prod.ext_iff, and_comm]
        aesop
      have hc := Finset.card_union_add_card_inter A C
      simp only [hI, Finset.card_singleton] at hc
      have hA : A.card = Fintype.card F := by simp [A]
      have hC : C.card = Fintype.card F := by simp [C]
      rw [hA, hC] at hc
      omega
  · rintro n ⟨B, hB, rfl⟩
    by_contra hn
    have hsmall : B.card < 2 * Fintype.card F - 1 := by omega
    obtain ⟨b0, hb0, _⟩ := hB (.vertical 0)
    have hpos : 0 < B.card := Finset.card_pos.mpr ⟨b0, hb0⟩
    let P : MvPolynomial Bool F := ∏ b ∈ B.erase b0,
      (1 - MvPolynomial.C (b.1 - b0.1) * X false -
        MvPolynomial.C (b.2 - b0.2) * X true)
    have hhit (w : Bool → F) (hw : w ≠ 0) :
        ∃ b ∈ B.erase b0,
          (b.1 - b0.1) * w false + (b.2 - b0.2) * w true = 1 := by
      by_cases hv : w true = 0
      · have hu : w false ≠ 0 := by
          intro hu
          apply hw
          funext i
          cases i <;> assumption
        obtain ⟨b, hb, hl⟩ := hB (.vertical (b0.1 + (w false)⁻¹))
        change b.1 = b0.1 + (w false)⁻¹ at hl
        have he : (b.1 - b0.1) * w false + (b.2 - b0.2) * w true = 1 := by
          rw [hl, hv]
          simp [hu]
        refine ⟨b, Finset.mem_erase.mpr ⟨?_, hb⟩, he⟩
        intro heq
        rw [heq] at he
        simp at he
      · obtain ⟨b, hb, hl⟩ := hB (.graph (-w false / w true)
          (b0.2 + (1 + w false * b0.1) / w true))
        change b.2 = (-w false / w true) * b.1 +
          (b0.2 + (1 + w false * b0.1) / w true) at hl
        have he : (b.1 - b0.1) * w false + (b.2 - b0.2) * w true = 1 := by
          rw [hl]
          field_simp
          ring
        refine ⟨b, Finset.mem_erase.mpr ⟨?_, hb⟩, he⟩
        intro heq
        rw [heq] at he
        simp at he
    have hzero : eval (0 : Bool → F) P = 1 := by simp [P]
    have hnonzero (w : Bool → F) (hw : w ≠ 0) : eval w P = 0 := by
      obtain ⟨b, hb, he⟩ := hhit w hw
      dsimp only [P]
      rw [eval_prod]
      apply Finset.prod_eq_zero hb
      simp only [map_sub, map_one, map_mul, eval_C, eval_X]
      linear_combination -he
    have hdegree : P.totalDegree ≤ (B.erase b0).card := by
      calc
        P.totalDegree ≤ ∑ b ∈ B.erase b0,
            (1 - MvPolynomial.C (b.1 - b0.1) * X false -
              MvPolynomial.C (b.2 - b0.2) * X true).totalDegree :=
          totalDegree_finsetProd _ _
        _ ≤ ∑ _b ∈ B.erase b0, 1 := by
          apply Finset.sum_le_sum
          intro b hb
          apply (totalDegree_sub _ _).trans
          apply max_le
          · apply (totalDegree_sub _ _).trans
            apply max_le
            · simp
            · exact (totalDegree_mul _ _).trans (by
                simp only [totalDegree_C, totalDegree_X, zero_add, le_refl])
          · exact (totalDegree_mul _ _).trans (by
              simp only [totalDegree_C, totalDegree_X, zero_add, le_refl])
        _ = (B.erase b0).card := by simp
    have hlt : P.totalDegree < (Fintype.card F - 1) * Fintype.card Bool := by
      rw [Fintype.card_bool]
      have herase := Finset.card_erase_of_mem hb0
      omega
    have hsum := sum_eval_eq_zero P hlt
    have hone : (∑ w : Bool → F, eval w P) = 1 := by
      rw [Finset.sum_eq_single (0 : Bool → F)]
      · exact hzero
      · intro w hw hne
        exact hnonzero w hne
      · simp
    rw [hone] at hsum
    exact one_ne_zero hsum

end D5.S3.Geometry.FiniteGeometry.AffineBlockingBound
