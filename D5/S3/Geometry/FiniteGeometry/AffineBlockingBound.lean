/- GID: D5/S3/Geometry/FiniteGeometry/AffineBlockingBound
   generality: G
   mirror-B: D5/B/S3/Geometry/FiniteGeometry/AffineBlockingBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sharp 2q-1 blocking minimum for all nonzero linear fibres in a finite-field plane. -/

import Mathlib.LinearAlgebra.Prod
import Mathlib.FieldTheory.ChevalleyWarning

/- proof_shape: affine_blocking_minimum: content
   admission_basis: escape-witness
   The blocking condition constructs a polynomial on the dual plane with singleton
   evaluation support. Its degree obstruction proves the lower bound; all local
   linear algebra, translation and axis cardinality steps remain inside the proof. -/

namespace D5.S3.Geometry.FiniteGeometry.AffineBlockingBound

open MvPolynomial
open scoped BigOperators

/-- The sharp Jamison--Brouwer--Schrijver minimum for all affine linear fibres in a plane. -/
theorem affine_blocking_minimum {F : Type*} [Field F] [Fintype F] :
    IsLeast {n : ℕ | ∃ B : Finset (F × F),
      (∀ φ : (F × F) →ₗ[F] F, φ ≠ 0 → ∀ c : F, ∃ p ∈ B, φ p = c) ∧ B.card = n}
      (2 * Fintype.card F - 1) := by
  classical
  constructor
  · let A : Finset (F × F) := Finset.univ.product {0}
    let C : Finset (F × F) := Finset.product {0} Finset.univ
    refine ⟨A ∪ C, ?_, ?_⟩
    · intro φ hφ c
      have hcoords (x y : F) : φ (x, y) = x * φ (1, 0) + y * φ (0, 1) := by
        calc
          φ (x, y) = φ (x • (1, 0) + y • (0, 1)) := by simp
          _ = x * φ (1, 0) + y * φ (0, 1) := by
            simp only [map_add, map_smul, smul_eq_mul]
      by_cases ha : φ (1, 0) = 0
      · have hb : φ (0, 1) ≠ 0 := by
          intro hb
          apply hφ
          apply LinearMap.ext
          intro p
          simpa only [ha, hb, mul_zero, add_zero, LinearMap.zero_apply] using
            hcoords p.1 p.2
        refine ⟨(0, c / φ (0, 1)), Finset.mem_union_right _ ?_, ?_⟩
        · simp [C]
        · rw [hcoords]
          simp [hb]
      · refine ⟨(c / φ (1, 0), 0), Finset.mem_union_left _ ?_, ?_⟩
        · simp [A]
        · rw [hcoords]
          simp [ha]
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
    have hfst : (LinearMap.fst F F F) ≠ 0 := by
      intro h
      have hh := congrArg (fun φ : (F × F) →ₗ[F] F => φ (1, 0)) h
      simp at hh
    obtain ⟨b0, hb0, _⟩ := hB (LinearMap.fst F F F) hfst 0
    have hpos : 0 < B.card := Finset.card_pos.mpr ⟨b0, hb0⟩
    let P : MvPolynomial Bool F := ∏ b ∈ B.erase b0,
      (1 - MvPolynomial.C (b.1 - b0.1) * X false -
        MvPolynomial.C (b.2 - b0.2) * X true)
    have hhit (w : Bool → F) (hw : w ≠ 0) :
        ∃ b ∈ B.erase b0,
          (b.1 - b0.1) * w false + (b.2 - b0.2) * w true = 1 := by
      let φ : (F × F) →ₗ[F] F :=
        w false • LinearMap.fst F F F + w true • LinearMap.snd F F F
      have heval (b : F × F) : φ b = b.1 * w false + b.2 * w true := by
        simp [φ, mul_comm]
      have hφ : φ ≠ 0 := by
        intro h
        apply hw
        funext i
        cases i with
        | false =>
            have hh := congrArg (fun ψ : (F × F) →ₗ[F] F => ψ (1, 0)) h
            simpa [heval] using hh
        | true =>
            have hh := congrArg (fun ψ : (F × F) →ₗ[F] F => ψ (0, 1)) h
            simpa [heval] using hh
      obtain ⟨b, hb, hl⟩ := hB φ hφ (φ b0 + 1)
      have he : (b.1 - b0.1) * w false + (b.2 - b0.2) * w true = 1 := by
        rw [heval, heval] at hl
        linear_combination hl
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
