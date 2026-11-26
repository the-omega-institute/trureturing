/- GID: D5/S3/Quantum/Measurement/Auric/CompressionSpectrum
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/Auric/CompressionSpectrum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Spectral threshold counts under isometric compression. -/

import D5.S3.Weil.ZetaLinear.Sylvester
import Mathlib.Order.Interval.Finset.Fin

/-! # Spectral threshold counts under isometric compression -/

namespace D5.S3.Quantum.Measurement.Auric.CompressionSpectrum

open Matrix RHLinalg Finset
open scoped ComplexOrder

variable {K : Type*} [RCLike K]
variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

private theorem hermForm_le_of_truncation_zero {A : Matrix n n K} (hA : A.IsHermitian)
    (threshold : ℝ) (x : n → K)
    (hx : specMap hA (fun t => (t - threshold)⁺) *ᵥ x = 0) :
    hermForm A x ≤ threshold * ∑ i, ‖x i‖ ^ 2 := by
  have hposZero : hermForm (specMap hA (fun t => (t - threshold)⁺)) x = 0 := by
    unfold hermForm
    rw [hx]
    simp
  have hneg : 0 ≤ hermForm (specMap hA (fun t => (t - threshold)⁻)) x :=
    hermForm_nonneg_of_posSemidef
      (specMap_posSemidef hA (f := fun t => (t - threshold)⁻) (fun _ => negPart_nonneg _)) x
  have hshift : hermForm (specMap hA (fun t => t - threshold)) x = hermForm A x -
      threshold * ∑ i, ‖x i‖ ^ 2 := by
    calc
      _ = ∑ i, (hA.eigenvalues i - threshold) *
            ‖(star (hA.eigenvectorUnitary : Matrix n n K) *ᵥ x) i‖ ^ 2 :=
        hermForm_specMap hA _ x
      _ = _ := by
        conv_rhs => rw [← specMap_id hA]
        change _ = RCLike.re (star x ⬝ᵥ (specMap hA id *ᵥ x)) - _
        rw [hermForm_specMap hA, ← sum_normSq_unitary_mulVec hA x, mul_sum, ← sum_sub_distrib]
        apply sum_congr rfl
        intro i _
        simp only [id_eq]
        ring
  have hdecomp : specMap hA (fun t => t - threshold) =
      specMap hA (fun t => (t - threshold)⁺) - specMap hA (fun t => (t - threshold)⁻) := by
    rw [← specMap_sub]
    congr 1
    funext t
    exact (posPart_sub_negPart (t - threshold)).symm
  rw [hdecomp, hermForm_sub, hposZero] at hshift
  linarith

/-- An isometric compression cannot increase the number of eigenvalues
strictly above the same real threshold. -/
theorem positiveCount_compression_le {A : Matrix n n K} (hA : A.IsHermitian)
    (W : Matrix n m K) (hW : Wᴴ * W = 1) (threshold : ℝ) :
    posIndexAbove (isHermitian_conjTranspose_mul_mul W hA) threshold ≤
      posIndexAbove hA threshold := by
  let B := Wᴴ * A * W
  let hB : B.IsHermitian := isHermitian_conjTranspose_mul_mul W hA
  let V := LinearMap.range (specMap hB (fun t => (t - threshold)⁺)).mulVecLin
  let P := (specMap hA (fun t => (t - threshold)⁺)).mulVecLin
  let L := P.comp W.mulVecLin
  have hnorm (x : m → K) : ∑ i, ‖(W *ᵥ x) i‖ ^ 2 = ∑ i, ‖x i‖ ^ 2 := by
    rw [← hermForm_one (W *ᵥ x), ← hermForm_conj (1 : Matrix n n K) W x,
      Matrix.mul_one, hW, hermForm_one]
  have hinj : Function.Injective (L.domRestrict V) := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    rintro ⟨x, hx⟩ hzero
    simp only [LinearMap.mem_ker, LinearMap.domRestrict_apply, LinearMap.comp_apply,
      mulVecLin_apply, L, P] at hzero
    simp only [Submodule.mem_bot]
    by_contra! hxzero
    have hx' : x ≠ 0 := fun h => hxzero (Subtype.ext h)
    have hsoft := hermForm_le_of_truncation_zero hA threshold (W *ᵥ x) hzero
    have hhard := hermForm_gt_on_range_truncPos hB threshold x hx hx'
    rw [hnorm, ← hermForm_conj A W x] at hsoft
    exact (not_lt_of_ge hsoft) hhard
  calc
    posIndexAbove hB threshold = Module.finrank K V := (finrank_range_truncPos hB _).symm
    _ = Module.finrank K (LinearMap.range (L.domRestrict V)) :=
      (LinearMap.finrank_range_of_inj hinj).symm
    _ ≤ Module.finrank K (LinearMap.range P) := by
      apply Submodule.finrank_mono
      rintro _ ⟨⟨x, _⟩, rfl⟩
      exact ⟨W *ᵥ x, rfl⟩
    _ = posIndexAbove hA threshold := finrank_range_truncPos hA _

/-- Each decreasingly ordered eigenvalue of an isometric compression is
bounded by the corresponding eigenvalue of the original Hermitian matrix. -/
theorem eigenvalue_compression_le {A : Matrix n n K} (hA : A.IsHermitian)
    (W : Matrix n m K) (hW : Wᴴ * W = 1) (i : Fin (Fintype.card m))
    (hi : i.val < Fintype.card n) :
    (isHermitian_conjTranspose_mul_mul W hA).eigenvalues₀ i ≤
      hA.eigenvalues₀ ⟨i.val, hi⟩ := by
  classical
  let hB := isHermitian_conjTranspose_mul_mul W hA
  let j : Fin (Fintype.card n) := ⟨i.val, hi⟩
  let threshold := hA.eigenvalues₀ j
  change hB.eigenvalues₀ i ≤ threshold
  by_contra! hbad
  have hlow : i.val + 1 ≤ posIndexAbove hB threshold := by
    unfold posIndexAbove
    rw [card_eigenvalues_reindex]
    rw [← Fin.card_Iic i]
    apply card_le_card
    intro k hk
    exact mem_filter.2 ⟨mem_univ _, hbad.trans_le
      (hB.eigenvalues₀_antitone (mem_Iic.1 hk))⟩
  have hupp : posIndexAbove hA threshold ≤ j.val := by
    unfold posIndexAbove
    rw [card_eigenvalues_reindex]
    rw [← Fin.card_Iio j]
    apply card_le_card
    intro k hk
    have hval := (mem_filter.1 hk).2
    apply mem_Iio.2
    by_contra! hkj
    exact (not_lt_of_ge (hA.eigenvalues₀_antitone hkj)) hval
  have hcount := positiveCount_compression_le hA W hW threshold
  change posIndexAbove hB threshold ≤ posIndexAbove hA threshold at hcount
  have htotal := hlow.trans (hcount.trans hupp)
  change i.val + 1 ≤ i.val at htotal
  omega

end D5.S3.Quantum.Measurement.Auric.CompressionSpectrum
