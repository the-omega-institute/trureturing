/- GID: D5/S3/Quantum/Hiai/InverseGeometricIdentification
   generality: G
   mirror-B: D5/B/S3/Quantum/Hiai/InverseGeometricIdentification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Weighted symmetry and inverse sandwich for the genuine spectral geometric mean. -/

import D5.S3.Quantum.Hiai.PsiMeanTraceConcavity
import Mathlib.Algebra.Star.UnitaryStarAlgAut

noncomputable section
namespace D5.S3.Quantum.Hiai.InverseGeometricIdentification

open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder
open PsiMeanTraceConcavity

/-- Real spectral powers intertwine the genuine star automorphism of a unitary. -/
theorem unitary_rpow {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (u : unitary A) {a : A} (ha : IsStrictlyPositive a) (t : ℝ) :
    CFC.rpow ((u : A) * a * star (u : A)) t =
      (u : A) * CFC.rpow a t * star (u : A) := by
  let φ := Unitary.conjStarAlgAut ℂ A u
  have hφa : IsStrictlyPositive (φ a) :=
    (Unitary.isUnit_coe (U := u)).isStrictlyPositive_star_right_conjugate_iff.mpr ha
  change CFC.rpow (φ a) t = φ (CFC.rpow a t)
  unfold CFC.rpow
  exact (StarAlgHomClass.map_cfc φ (fun x : NNReal ↦ x ^ t) a
    (NNReal.continuousOn_rpow_const (.inl (spectrum.zero_notMem NNReal ha.isUnit)))
    (StarAlgEquiv.isometry φ).continuous ha.nonneg hφa.nonneg).symm

variable {d : Type*} [Fintype d] [DecidableEq d]
local instance : Pow (Matrix d d ℂ) ℝ := ⟨CFC.rpow⟩

/-- Both identifications hold for every real weight, without commutation or a dimension bound. -/
theorem geometricMean_identification {X Y : Matrix d d ℂ}
    (hX : X.PosDef) (hY : Y.PosDef) (t : ℝ) :
    geometricMean t X Y = geometricMean (1 - t) Y X ∧
      geometricMean (-t) X Y = X * Ring.inverse (geometricMean t X Y) * X := by
  have hx := hX.isStrictlyPositive
  have hy := hY.isStrictlyPositive
  let C := CFC.conjSqrt (Ring.inverse X) Y
  have hc : IsStrictlyPositive C :=
    (CFC.isStrictlyPositive_conjSqrt_iff _ _ hx.ringInverse).mpr hy
  have hiX : CFC.sqrt (Ring.inverse X) = X ^ (-1 / 2 : ℝ) := by
    rw [CFC.sqrt_ringInverse, CFC.sqrt_eq_rpow,
      CFC.inverse_rpow X (1 / 2) (by norm_num) hx]
    congr 1
    norm_num
  have hiY : CFC.sqrt (Ring.inverse Y) = Y ^ (-1 / 2 : ℝ) := by
    rw [CFC.sqrt_ringInverse, CFC.sqrt_eq_rpow,
      CFC.inverse_rpow Y (1 / 2) (by norm_num) hy]
    congr 1
    norm_num
  have hmean (s : ℝ) : geometricMean s X Y = CFC.conjSqrt X (C ^ s) := by
    simp only [geometricMean, C, CFC.conjSqrt_apply, hiX, CFC.sqrt_eq_rpow]
  have hinv : geometricMean (-t) X Y =
      X * Ring.inverse (geometricMean t X Y) * X := by
    have hpower : Ring.inverse (C ^ t) = C ^ (-t) := by
      by_cases ht : t = 0
      · subst t
        simp [CFC.rpow_zero C hc.nonneg]
      · exact CFC.inverse_rpow C t ht hc
    rw [hmean (-t), hmean t, CFC.ringInverse_conjSqrt X (C ^ t) hx, hpower]
    have hxx : X * CFC.sqrt (Ring.inverse X) = CFC.sqrt X := by
      rw [hiX, CFC.sqrt_eq_rpow]
      conv_lhs => lhs; rw [← CFC.rpow_one X hx.nonneg]
      rw [← CFC.rpow_add hx.isUnit]
      congr 1
      norm_num
    have hxx' : CFC.sqrt (Ring.inverse X) * X = CFC.sqrt X := by
      rw [hiX, CFC.sqrt_eq_rpow]
      conv_lhs => rhs; rw [← CFC.rpow_one X hx.nonneg]
      rw [← CFC.rpow_add hx.isUnit]
      congr 1
      norm_num
    simp only [CFC.conjSqrt_apply]
    symm
    calc
      _ = (X * CFC.sqrt (Ring.inverse X)) * C ^ (-t) *
          (CFC.sqrt (Ring.inverse X) * X) := by simp only [mul_assoc]
      _ = _ := by rw [hxx, hxx']
  let S := CFC.sqrt X
  let T := CFC.sqrt Y
  let J := CFC.sqrt (Ring.inverse Y)
  let R := CFC.sqrt C
  have hS : IsStrictlyPositive S := hx.sqrt X
  have hJ : IsStrictlyPositive J := hy.ringInverse.sqrt _
  have hR : IsStrictlyPositive R := hc.sqrt C
  have hTJ : T * J = 1 := by
    dsimp [T, J]
    rw [CFC.sqrt_ringInverse, Ring.mul_inverse_cancel _ (hy.sqrt Y).isUnit]
  have hJT : J * T = 1 := by
    dsimp [T, J]
    rw [CFC.sqrt_ringInverse, Ring.inverse_mul_cancel _ (hy.sqrt Y).isUnit]
  have hSS : S * S = X := CFC.sqrt_mul_sqrt_self X hx.nonneg
  have hRR : R * R = C := CFC.sqrt_mul_sqrt_self C hc.nonneg
  have hJJ : J * J = Ring.inverse Y :=
    CFC.sqrt_mul_sqrt_self _ hy.ringInverse.nonneg
  have hrestore : S * C * S = Y :=
    CFC.conjSqrt_conjSqrt_ringInverse X Y hx
  have hCinv : Ring.inverse C = S * Ring.inverse Y * S := by
    dsimp [C]
    rw [CFC.ringInverse_conjSqrt _ _ hx.ringInverse, Ring.inverse_inverse hx.isUnit]
    rfl
  have hRinv : R * Ring.inverse C * R = 1 := by
    change CFC.conjSqrt C (Ring.inverse C) = 1
    rw [← CFC.conjSqrt_one (Ring.inverse C) hc.ringInverse.nonneg,
      CFC.conjSqrt_conjSqrt_ringInverse C 1 hc]
  let U := J * S * R
  have hstarU : star U = R * S * J := by
    simp only [U, star_mul, hJ.isSelfAdjoint.star_eq,
      hS.isSelfAdjoint.star_eq, hR.isSelfAdjoint.star_eq, mul_assoc]
  have hUU : U * star U = 1 := by
    rw [hstarU]
    change (J * S * R) * (R * S * J) = 1
    calc
      _ = J * (S * (R * R) * S) * J := by simp only [mul_assoc]
      _ = J * Y * J := by rw [hRR, hrestore]
      _ = 1 := CFC.conjSqrt_ringInverse_self Y hy
  have hUU' : star U * U = 1 := by
    rw [hstarU]
    change (R * S * J) * (J * S * R) = 1
    calc
      _ = R * (S * (J * J) * S) * R := by simp only [mul_assoc]
      _ = R * Ring.inverse C * R := by rw [hJJ, ← hCinv]
      _ = 1 := hRinv
  let u : unitary (Matrix d d ℂ) := ⟨U, Unitary.mem_iff.mpr ⟨hUU', hUU⟩⟩
  have hreverse : J * X * J = U * Ring.inverse C * star U := by
    rw [hstarU]
    change J * X * J = (J * S * R) * Ring.inverse C * (R * S * J)
    calc
      _ = J * (S * (R * Ring.inverse C * R) * S) * J := by rw [hRinv]; simp [hSS]
      _ = _ := by simp only [mul_assoc]
  have hpow : (J * X * J) ^ (1 - t) = U * C ^ (t - 1) * star U := by
    rw [hreverse]
    change CFC.rpow ((u : Matrix d d ℂ) * Ring.inverse C * star (u : Matrix d d ℂ))
      (1 - t) = _
    rw [unitary_rpow u hc.ringInverse]
    change U * (Ring.inverse C) ^ (1 - t) * star U = _
    rw [CFC.inverse_eq_rpow_neg_one hc,
      CFC.rpow_rpow C (-1) (1 - t) (by norm_num) hc]
    rw [show (-1 : ℝ) * (1 - t) = t - 1 by ring]
  have hcombine : R * C ^ (t - 1) * R = C ^ t := by
    dsimp [R]
    rw [CFC.sqrt_eq_rpow, ← CFC.rpow_add hc.isUnit, ← CFC.rpow_add hc.isUnit]
    congr 1
    ring
  have hTU : T * U = S * R := by
    change T * (J * S * R) = S * R
    rw [← mul_assoc, ← mul_assoc, hTJ, one_mul]
  have hUT : star U * T = R * S := by
    rw [hstarU, mul_assoc, hJT, mul_one]
  have hsymm : geometricMean t X Y = geometricMean (1 - t) Y X := by
    rw [hmean]
    change S * C ^ t * S = _
    unfold geometricMean
    rw [← hiY, ← CFC.sqrt_eq_rpow, hpow]
    change S * C ^ t * S = T * (U * C ^ (t - 1) * star U) * T
    calc
      _ = S * (R * C ^ (t - 1) * R) * S := by rw [hcombine]
      _ = (T * U) * C ^ (t - 1) * (star U * T) := by
        rw [hTU, hUT]
        simp only [mul_assoc]
      _ = _ := by simp only [mul_assoc]
  exact ⟨hsymm, hinv⟩

#print axioms unitary_rpow
#print axioms geometricMean_identification

end D5.S3.Quantum.Hiai.InverseGeometricIdentification
