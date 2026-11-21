/- GID: D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Residual
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Residual
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635.result; premises=D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635.finite_certificate
   digest: Characteristic-polynomial closure of the signed scalar strip residual. -/

import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

open scoped BigOperators
open D5.S3.StatisticalMechanics.Potts.StripDefects

namespace D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Residual

open DefectTransfer (forward forward_eq)

def coefficients : Fin 27 → ℤ :=
  ![54, -1140, 11637, -54252, 33192, 658756, -1921212, -1566516, 12850374,
    -7108644, -35018232, 43506046, 38500440, -85687812, -200796, 75241308,
    -31685592, -25769200, 20878068, 213348, -3655770, 608916, 230904,
    -61761, -2790, 1800, -125]

variable {D : ℕ}

def scalar (M : Matrix (Fin D) (Fin D) ℤ) (v e : Fin D → ℤ) (k : ℕ) : ℤ :=
  dotProduct v ((M ^ k).mulVec e)

def residual (M : Matrix (Fin D) (Fin D) ℤ) (v e : Fin D → ℤ) (t : ℕ) : ℤ :=
  scalar M v e (30 + t) -
    ∑ j : Fin 27, coefficients j * scalar M v e (29 - j.val + t)

private theorem scalar_shift (M : Matrix (Fin D) (Fin D) ℤ) (v e : Fin D → ℤ)
    (k t : ℕ) :
    scalar M v e (k + t) = dotProduct (forward M v k) ((M ^ t).mulVec e) := by
  simp only [scalar, forward_eq, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← pow_add]

def residualVector (M : Matrix (Fin D) (Fin D) ℤ) (v : Fin D → ℤ) : Fin D → ℤ :=
  forward M v 30 - ∑ j : Fin 27, coefficients j • forward M v (29 - j.val)

theorem residual_as_power (M : Matrix (Fin D) (Fin D) ℤ) (v e : Fin D → ℤ)
    (t : ℕ) :
    residual M v e t =
      dotProduct (residualVector M v) ((M ^ t).mulVec e) := by
  simp only [residual, residualVector, scalar_shift, sub_dotProduct, sum_dotProduct,
    smul_dotProduct, smul_eq_mul]

private theorem scalar_powers_zero (M : Matrix (Fin D) (Fin D) ℤ) (w e : Fin D → ℤ)
    (hprefix : ∀ t < D, dotProduct w ((M ^ t).mulVec e) = 0) :
    ∀ t, dotProduct w ((M ^ t).mulVec e) = 0 := by
  have hlead : M.charpoly.coeff D = 1 := by
    simpa [Matrix.charpoly_natDegree_eq_dim] using M.charpoly_monic.coeff_natDegree
  have hzero : (∑ k ∈ Finset.range D, M.charpoly.coeff k • M ^ k) + M ^ D = 0 := by
    simpa [Polynomial.aeval_eq_sum_range, Matrix.charpoly_natDegree_eq_dim,
      Finset.sum_range_succ, hlead] using Matrix.aeval_self_charpoly M
  have hpower (m : ℕ) :
      M ^ (D + m) = -∑ k ∈ Finset.range D, M.charpoly.coeff k • M ^ (k + m) := by
    rw [pow_add, eq_neg_of_add_eq_zero_right hzero, Matrix.neg_mul, Finset.sum_mul]
    simp only [Matrix.smul_mul, pow_add]
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih =>
    by_cases ht : t < D
    · exact hprefix t ht
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt ht)
      rw [hpower, Matrix.neg_mulVec, Matrix.sum_mulVec, dotProduct_neg, dotProduct_sum, neg_eq_zero]
      refine Finset.sum_eq_zero fun k hk => ?_
      have hk' := Finset.mem_range.mp hk
      rw [Matrix.smul_mulVec, dotProduct_smul, ih (k + m) (by omega), smul_zero]

theorem residual_zero (M : Matrix (Fin D) (Fin D) ℤ) (v e : Fin D → ℤ)
    (hprefix : ∀ t < D, residual M v e t = 0) :
    ∀ t, residual M v e t = 0 := by
  simp_rw [residual_as_power] at hprefix ⊢
  exact scalar_powers_zero M _ e hprefix

#print axioms residual_zero

end D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Residual
