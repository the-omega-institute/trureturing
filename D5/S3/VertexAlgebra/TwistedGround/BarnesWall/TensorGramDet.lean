/- GID: D5/S3/VertexAlgebra/TwistedGround/BarnesWall/TensorGramDet
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Complementary tensor rows balance the scaling and give determinant one. -/

import D5.S3.VertexAlgebra.TwistedGround.BarnesWall.TensorGram

/-! Unimodularity of the normalized Barnes–Wall tensor Gram at any odd slot count. -/

open scoped BigOperators Matrix
set_option autoImplicit false

namespace D5.S3.VertexAlgebra.TwistedGround.BarnesWall.TensorGramDet

open TailPauliPairing (Word complement)
open TensorSubsetRows (scaledRow subsetRow included rowScale falseCount)
open TensorGram (gram gram_eq_normalized_dotProduct support fullRowExponent normalizationExponent)
open LatticeTwistedGroundRealization.SignQuotient (F₂)

variable {ι : Type} [Fintype ι] [LinearOrder ι]

noncomputable section

private def scaledRows : Matrix (Word ι) (Word ι) ℚ := Matrix.of scaledRow

private def gramMatrix : Matrix (Word ι) (Word ι) ℤ := Matrix.of gram

private theorem support_injective : Function.Injective (support (ι := ι)) := by
  intro u v h
  funext r
  have hr : (u r = true) ↔ (v r = true) := by
    simpa only [support, Finset.mem_filter, Finset.mem_univ, true_and] using
      (SetLike.ext_iff.mp h r : r ∈ support u ↔ r ∈ support v)
  cases hu : u r <;> cases hv : v r <;> simp_all

private theorem permutation_eq_one_of_subsets (σ : Equiv.Perm (Word ι))
    (hσ : ∀ u : Word ι, included (σ u) u) : σ = 1 := by
  let f (u : Word ι) := (support u).card
  have hsub (u : Word ι) : support u ⊆ support (σ u) := by
    intro r hr
    have hp := (Finset.mem_filter.mp hr).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hσ u r hp⟩
  have hf (u : Word ι) : f u ≤ f (σ u) := Finset.card_le_card (hsub u)
  have hsum : (∑ u : Word ι, f (σ u)) = ∑ u : Word ι, f u := Equiv.sum_comp σ f
  apply Equiv.ext
  intro u
  have hrev : f (σ u) ≤ f u := by
    by_contra! hlt
    have hbad := Finset.sum_lt_sum (s := Finset.univ)
      (f := f) (g := fun z => f (σ z)) (fun z _ => hf z) ⟨u, Finset.mem_univ _, hlt⟩
    exact (lt_irrefl _ (hbad.trans_eq hsum)).elim
  exact support_injective (Finset.eq_of_subset_of_card_le (hsub u) hrev).symm

private theorem det_scaledRows : (scaledRows (ι := ι)).det =
    (2 : ℚ) ^ ∑ u : Word ι, fullRowExponent u := by
  classical
  rw [Matrix.det_apply, Finset.sum_eq_single (1 : Equiv.Perm (Word ι))]
  · simp [scaledRows, scaledRow, subsetRow, included, rowScale, fullRowExponent,
      Finset.prod_pow_eq_pow_sum]
  · intro σ _ hσ
    have hx : ∃ u : Word ι, ¬ included (σ u) u := by
      by_contra! h
      exact hσ (permutation_eq_one_of_subsets σ h)
    obtain ⟨u, hu⟩ := hx
    rw [Finset.prod_eq_zero (Finset.mem_univ u) (by simp [scaledRows, scaledRow, subsetRow, hu]), smul_zero]
  · simp

private theorem complement_equiv : Function.Involutive (complement (ι := ι)) := by
  intro u
  funext r
  simp [complement]

private theorem row_exponents_complement (hodd : (Fintype.card ι : F₂) = 1) (u : Word ι) :
    fullRowExponent u + fullRowExponent (complement u) = normalizationExponent (ι := ι) := by
  have hc : Fintype.card ι % 2 = 1 := by
    have h := congrArg ZMod.val hodd
    simpa only [ZMod.val_natCast, show (1 : F₂).val = 1 by decide] using h
  have hcount : falseCount u + falseCount (complement u) = Fintype.card ι := by
    have hcard (v : Word ι) : falseCount v = ∑ r, if v r = false then 1 else 0 := by
      rw [falseCount, Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [hcard, hcard, ← Finset.sum_add_distrib]
    suffices hs : ∀ r : ι, (if u r = false then (1 : ℕ) else 0) +
        (if complement u r = false then 1 else 0) = 1 by simp [hs]
    intro r
    cases hr : u r <;> simp [complement, hr]
  unfold fullRowExponent normalizationExponent
  omega

private theorem twice_row_exponent_sum (hodd : (Fintype.card ι : F₂) = 1) :
    (∑ u : Word ι, fullRowExponent u) + (∑ u : Word ι, fullRowExponent u) =
      normalizationExponent (ι := ι) * Fintype.card (Word ι) := by
  let c : Word ι ≃ Word ι := ⟨complement, complement, complement_equiv, complement_equiv⟩
  have h := c.sum_comp fullRowExponent
  calc
    _ = (∑ u : Word ι, fullRowExponent u) + (∑ u : Word ι, fullRowExponent (complement u)) :=
      congrArg ((∑ u : Word ι, fullRowExponent u) + ·) h.symm
    _ = ∑ u : Word ι, (fullRowExponent u + fullRowExponent (complement u)) :=
      Finset.sum_add_distrib.symm
    _ = _ := by simp [row_exponents_complement hodd, mul_comm]

private theorem gram_factorization (hodd : (Fintype.card ι : F₂) = 1) :
    (gramMatrix (ι := ι)).map (Int.castRingHom ℚ) =
      ((2 : ℚ) ^ normalizationExponent (ι := ι))⁻¹ •
        (scaledRows * scaledRowsᵀ : Matrix (Word ι) (Word ι) ℚ) := by
  ext u v
  change (gram u v : ℚ) = ((2 : ℚ) ^ normalizationExponent (ι := ι))⁻¹ *
    (scaledRows * scaledRowsᵀ : Matrix (Word ι) (Word ι) ℚ) u v
  rw [gram_eq_normalized_dotProduct hodd, Matrix.mul_apply, div_eq_mul_inv, mul_comm]
  rfl

/-- The KRR Gram is unimodular whenever the number of tensor slots is odd. -/
theorem gram_det_one (hodd : (Fintype.card ι : F₂) = 1) :
    (Matrix.of (gram (ι := ι))).det = 1 := by
  change (gramMatrix (ι := ι)).det = 1
  apply (Int.cast_injective (α := ℚ))
  rw [Int.cast_one, Int.cast_det]
  change ((gramMatrix (ι := ι)).map (Int.castRingHom ℚ)).det = 1
  rw [gram_factorization hodd, Matrix.det_smul, Matrix.det_mul, Matrix.det_transpose,
    det_scaledRows, ← pow_add, twice_row_exponent_sum hodd, ← inv_pow, ← pow_mul,
    ← mul_pow, inv_mul_cancel₀ (by norm_num : (2 : ℚ) ≠ 0), one_pow]

end
end D5.S3.VertexAlgebra.TwistedGround.BarnesWall.TensorGramDet
