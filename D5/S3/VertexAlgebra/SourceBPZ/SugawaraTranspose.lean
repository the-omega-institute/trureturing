/- GID: D5/S3/VertexAlgebra/SourceBPZ/SugawaraTranspose
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/SourceBPZ/SugawaraTranspose
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Opposite-mode Sugawara transposition for the native bilinear lattice pairing. -/

import D5.S3.VertexAlgebra.SourceBPZ.SourcePairingLaws
import D5.S3.VertexAlgebra.LatticeSugawaraCurrents

/-!
Two skew current transposes give the transpose of each quadratic summand.
Normal ordering is restored by the Heisenberg law in the two branches that
require a swap. The finite coefficient sum then uses the symmetry of the
matrix of weights. The normal-order proof follows `OriginalMatterHermitian`.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators

namespace D5.S3.VertexAlgebra.SourceBPZ.SugawaraTranspose

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeSugawaraCurrents OriginalSourcePairing SourcePairingLaws

private theorem sourcePairing_neutralMode_comp (D : LatticeData) (i j : Fin D.rank)
    (k l : ℤ) (x y : Carrier D) :
    sourcePairing D (neutralMode D i k (neutralMode D j l x)) y =
      sourcePairing D x (neutralMode D j (-l) (neutralMode D i (-k) y)) := by
  rw [sourcePairing_neutralMode D i k, sourcePairing_neutralMode D j l, neg_neg]

private theorem sourcePairing_normalSummand (D : LatticeData) (i j : Fin D.rank)
    (k l : ℤ) (x y : Carrier D) :
    sourcePairing D (normalSummand D i j k l x) y =
      sourcePairing D x (normalSummand D j i (-l) (-k) y) := by
  have commute (a b : Fin D.rank) (p q : ℤ) (h : p + q ≠ 0) :
      neutralMode D a p (neutralMode D b q y) =
        neutralMode D b q (neutralMode D a p y) := by
    have hc := neutralMode_heisenberg D a b p q
    rw [ite_eq_right h, zero_smul] at hc
    simpa only [Module.End.mul_apply] using
      congrArg (fun f : Module.End ℂ (Carrier D) => f y) (sub_eq_zero.mp hc)
  by_cases hk : k < 0 <;> by_cases hl : -l < 0
  · simpa only [normalSummand, ite_eq_left hk, ite_eq_left hl, Module.End.mul_apply] using
      sourcePairing_neutralMode_comp D i j k l x y
  · simp only [normalSummand, ite_eq_left hk, ite_eq_right hl, Module.End.mul_apply,
      sourcePairing_neutralMode_comp]
    rw [commute j i (-l) (-k) (by omega)]
  · simp only [normalSummand, ite_eq_right hk, ite_eq_left hl, Module.End.mul_apply,
      sourcePairing_neutralMode_comp]
    rw [commute i j (-k) (-l) (by omega)]
  · simpa only [normalSummand, ite_eq_right hk, ite_eq_right hl, Module.End.mul_apply] using
      sourcePairing_neutralMode_comp D j i l k x y

private theorem sourcePairing_normalSummand_finsum (D : LatticeData) (i j : Fin D.rank)
    (m : ℤ) (x y : Carrier D) :
    (∑ᶠ k : ℤ, sourcePairing D (normalSummand D i j k (m - k) x) y) =
      ∑ᶠ k : ℤ, sourcePairing D x (normalSummand D j i k (-m - k) y) := by
  conv_rhs => rw [← finsum_comp_equiv (Equiv.addRight (-m))]
  apply finsum_congr
  intro k
  change _ = sourcePairing D x (normalSummand D j i (k + -m) (-m - (k + -m)) y)
  rw [show k + -m = -(m - k) by omega, show -m - (-(m - k)) = -k by omega]
  exact sourcePairing_normalSummand D i j k (m - k) x y

private theorem linearMap_sugawaraMode (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (m : ℤ) (v : Carrier D)
    (F : Carrier D →ₗ[ℂ] ℂ) :
    F (sugawaraMode D H m v) = (2 : ℂ)⁻¹ •
      ∑ i : Fin D.rank, ∑ j : Fin D.rank, H i j •
        ∑ᶠ k : ℤ, F (normalSummand D i j k (m - k) v) := by
  calc
    F (sugawaraMode D H m v) =
        F ((2 : ℂ)⁻¹ • ∑ i : Fin D.rank, ∑ j : Fin D.rank, H i j •
          ∑ᶠ k : ℤ, normalSummand D i j k (m - k) v) :=
      congrArg (fun w : Carrier D => F w) (sugawaraMode_finsum D H m v)
    _ = _ := by
      simp only [map_smul, map_sum]
      apply congrArg (fun z : ℂ => (2 : ℂ)⁻¹ • z)
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
      exact congrArg (fun z : ℂ => H i j • z)
        (map_finsum F (normalSummand_finite D i j m v))

/-- Every integer Sugawara mode transposes to its opposite mode for symmetric weights. -/
theorem sourcePairing_sugawaraMode (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (hH : H.transpose = H)
    (m : ℤ) (x y : Carrier D) :
    sourcePairing D (sugawaraMode D H m x) y =
      sourcePairing D x (sugawaraMode D H (-m) y) := by
  classical
  have hcoeff (i j : Fin D.rank) : H j i = H i j := by
    simpa only [Matrix.transpose_apply] using
      congrArg (fun M : Matrix (Fin D.rank) (Fin D.rank) ℂ => M i j) hH
  let left : Carrier D →ₗ[ℂ] ℂ := (sourcePairing D).flip y
  let right : Carrier D →ₗ[ℂ] ℂ := sourcePairing D x
  have hsum :
      (∑ i : Fin D.rank, ∑ j : Fin D.rank, H i j •
        ∑ᶠ k : ℤ, left (normalSummand D i j k (m - k) x)) =
      ∑ i : Fin D.rank, ∑ j : Fin D.rank, H i j •
        ∑ᶠ k : ℤ, right (normalSummand D i j k (-m - k) y) := by
    calc
      _ = ∑ i : Fin D.rank, ∑ j : Fin D.rank, H i j •
            ∑ᶠ k : ℤ, right (normalSummand D j i k (-m - k) y) := by
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
        exact congrArg (fun z : ℂ => H i j • z)
          (sourcePairing_normalSummand_finsum D i j m x y)
      _ = _ := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
        rw [hcoeff i j]
  calc
    _ = (2 : ℂ)⁻¹ • ∑ i : Fin D.rank, ∑ j : Fin D.rank, H i j •
          ∑ᶠ k : ℤ, left (normalSummand D i j k (m - k) x) :=
      linearMap_sugawaraMode D H m x left
    _ = (2 : ℂ)⁻¹ • ∑ i : Fin D.rank, ∑ j : Fin D.rank, H i j •
          ∑ᶠ k : ℤ, right (normalSummand D i j k (-m - k) y) :=
      congrArg (fun z : ℂ => (2 : ℂ)⁻¹ • z) hsum
    _ = _ := (linearMap_sugawaraMode D H (-m) y right).symm

#print axioms sourcePairing_sugawaraMode

end D5.S3.VertexAlgebra.SourceBPZ.SugawaraTranspose
