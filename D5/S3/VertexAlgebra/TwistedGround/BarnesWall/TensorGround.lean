/- GID: D5/S3/VertexAlgebra/TwistedGround/BarnesWall/TensorGround
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual odd-slot reflection quotient gives the Weyl ground operators. -/

import D5.S3.VertexAlgebra.TwistedGround.BarnesWall.TensorGramDet
import Mathlib.Data.Finset.Sort

/-! The odd-slot tensor Gram supplies the actual negative-sign ground representation. -/

open scoped BigOperators Matrix
set_option autoImplicit false

namespace D5.S3.VertexAlgebra.TwistedGround.BarnesWall.TensorGround

open LatticeGeneratingFieldLocality (LatticeData halfDiagonal)
open LatticeTwistedGroundRealization (Ground actual_twisted_ground_representation sign_zero sign_one)
open LatticeTwistedGroundRealization.SignQuotient
open TailPauliPairing (Word)
open TensorGram (gram gram_comm gram_diagonal_even halfGram)

noncomputable section

variable {ι : Type} [Fintype ι] [LinearOrder ι] [order : LinearOrder (Word ι)]

private def wordLabel : Fin (Fintype.card (Word ι)) ≃ Word ι :=
  (@Fintype.orderIsoFinOfCardEq (Word ι) order _ _ rfl).toEquiv

private abbrev data (hodd : (Fintype.card ι : F₂) = 1) (hm : 3 ≤ Fintype.card ι) : LatticeData where
  rank := Fintype.card (Word ι)
  G := (Matrix.of (gram (ι := ι))).reindex wordLabel.symm wordLabel.symm
  symmetric i j := gram_comm _ _
  even_diagonal i := even_iff_two_dvd.mpr (gram_diagonal_even hodd hm _)

private theorem data_det_one (hodd : (Fintype.card ι : F₂) = 1) (hm : 3 ≤ Fintype.card ι) :
    (data hodd hm).G.det = 1 := by
  change ((Matrix.of (gram (ι := ι))).reindex wordLabel.symm wordLabel.symm).det = 1
  rw [Matrix.det_reindex_self, TensorGramDet.gram_det_one hodd]

private theorem lower_entry (hodd : (Fintype.card ι : F₂) = 1) (hm : 3 ≤ Fintype.card ι)
    (i j : Fin (Fintype.card (Word ι))) :
    (lowerMatrix (data hodd hm) i j : F₂) = halfGram (wordLabel i) (wordLabel j) := by
  have hlt : @LT.lt (Word ι) order.toLT (wordLabel j) (wordLabel i) ↔ j < i :=
    @OrderIso.lt_iff_lt _ _ inferInstance order.toPreorder
      (@Fintype.orderIsoFinOfCardEq (Word ι) order _ _ rfl) j i
  have heq : wordLabel j = wordLabel i ↔ j = i := wordLabel.injective.eq_iff
  unfold lowerMatrix halfGram halfDiagonal
  change (((if j < i then gram (wordLabel i) (wordLabel j) else 0) +
    (if j = i then gram (wordLabel i) (wordLabel i) / 2 else 0) : ℤ) : F₂) = _
  by_cases h : j < i <;> by_cases he : j = i <;> simp [h, he, hlt, heq]

private theorem cocycle_coordinates (hodd : (Fintype.card ι : F₂) = 1) (hm : 3 ≤ Fintype.card ι)
    (a b : Word ι → F₂) :
    modTwoCocycle (data hodd hm) (a ∘ wordLabel) (b ∘ wordLabel) = halfGram.toBilin' a b := by
  change ((lowerMatrix (data hodd hm)).map (Int.castRingHom F₂)).toBilin'
    (a ∘ wordLabel) (b ∘ wordLabel) = halfGram.toBilin' a b
  rw [Matrix.toBilin'_apply, Matrix.toBilin'_apply]
  simp only [Function.comp_apply, Matrix.map_apply, Int.coe_castRingHom, lower_entry hodd hm]
  have h (u : Word ι) :
      (∑ j : Fin (Fintype.card (Word ι)), a u * halfGram u (wordLabel j) * b (wordLabel j)) =
        ∑ v : Word ι, a u * halfGram u v * b v :=
    Equiv.sum_comp wordLabel (fun v => a u * halfGram u v * b v)
  simp only [h]
  exact Equiv.sum_comp wordLabel (fun u => ∑ v : Word ι, a u * halfGram u v * b v)

/-- The actual reflection quotient yields Weyl operators with the Barnes–Wall
half-Gram product and ground dimension at every odd tensor slot count
at least three. -/
theorem exists_tensor_ground (hodd : (Fintype.card ι : F₂) = 1) (hm : 3 ≤ Fintype.card ι) :
    ∃ (n : ℕ) (P : (Word ι → F₂) → Module.End ℂ (Ground n)),
      Fintype.card (Word ι) = n + n ∧
      Module.finrank ℂ (Ground n) = 2 ^ (Fintype.card (Word ι) / 2) ∧
      P 0 = 1 ∧ ∀ a b, P a * P b = complexSign (halfGram.toBilin' a b) • P (a + b) := by
  let D := data hodd hm
  have hu : IsUnit D.G.det := (data_det_one hodd hm) ▸ isUnit_one
  letI : (K D).Normal := K_normal D
  obtain ⟨n, ρ, hr, _, hsign, hd, _, _, _⟩ := actual_twisted_ground_representation D hu
  let R := ρ.comp (quotientEquiv D).symm.toMonoidHom
  let L (a : Word ι → F₂) : ReducedExtension D := ⟨0, a ∘ wordLabel⟩
  let C (s : F₂) : ReducedExtension D := ⟨s, 0⟩
  have hc (s : F₂) : R (C s) = complexSign s • (1 : Module.End ℂ (Ground n)) := by
    rcases (show ∀ s : F₂, s = 0 ∨ s = 1 by decide) s with rfl | rfl
    · change R 1 = _
      rw [map_one, sign_zero, one_smul]
    · have he : (quotientEquiv D).symm (C 1) = QuotientGroup.mk (⟨1, 0⟩ : Extension D) := by
        apply (quotientEquiv D).injective
        rw [MulEquiv.apply_symm_apply]
        change C 1 = reduction D ⟨1, 0⟩
        rfl
      change ρ ((quotientEquiv D).symm (C 1)) = _
      rw [he, hsign, sign_one, neg_one_smul]
  refine ⟨n, R ∘ L, hr, hd, ?_, ?_⟩
  · change R 1 = 1
    exact map_one R
  · intro a b
    have h : L a * L b = C (halfGram.toBilin' a b) * L (a + b) := by
      apply SignExtension.ext
      · change 0 + 0 + modTwoCocycle D (a ∘ wordLabel) (b ∘ wordLabel) =
          halfGram.toBilin' a b + 0 + modTwoCocycle D 0 ((a + b) ∘ wordLabel)
        simp only [zero_add, add_zero, map_zero, AddMonoidHom.zero_apply]
        exact cocycle_coordinates hodd hm a b
      · change (a ∘ wordLabel) + (b ∘ wordLabel) = 0 + ((a + b) ∘ wordLabel)
        rw [zero_add]
        rfl
    change R (L a) * R (L b) = _
    rw [← map_mul, h, map_mul, hc, smul_mul_assoc, one_mul]
    rfl

end
end D5.S3.VertexAlgebra.TwistedGround.BarnesWall.TensorGround
