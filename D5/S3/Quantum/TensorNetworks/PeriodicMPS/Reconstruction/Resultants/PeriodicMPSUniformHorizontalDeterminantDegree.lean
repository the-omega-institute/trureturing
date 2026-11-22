/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Resultants/PeriodicMPSUniformHorizontalDeterminantDegree
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Resultants/PeriodicMPSUniformHorizontalDeterminantDegree
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: Spectral degree of cofactor and resultant determinants. -/
module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-! Spectral degree of cleared minors and fixed-degree resultants. -/

public section

namespace UniformMPSHorizontalSpectral

open scoped BigOperators
open MvPolynomial

variable {σ R : Type*} [CommRing R]

/-- A columnwise total-degree filtration bounds the spectral degree of the determinant. -/
theorem det_totalDegree_le_column_sum {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n (MvPolynomial σ R)) (budget : n → ℕ)
    (hM : ∀ i j, (M i j).totalDegree ≤ budget j) :
    M.det.totalDegree ≤ ∑ j, budget j := by
  classical
  rw [Matrix.det_apply']
  apply totalDegree_finsetSum_le
  intro p _
  apply (totalDegree_mul _ _).trans
  have hsign : ((Equiv.Perm.sign p : MvPolynomial σ R)).totalDegree = 0 := by
    rw [← map_intCast (C : R →+* MvPolynomial σ R), totalDegree_C]
  rw [hsign, zero_add]
  apply (totalDegree_finsetProd _ _).trans
  exact Finset.sum_le_sum fun j _ => hM _ j

/-- The resultant has the specified fixed size even under a degree drop. -/
theorem resultant_totalDegree_le
    (f g : Polynomial (MvPolynomial σ R)) (d e N : ℕ)
    (hf : ∀ r, (f.coeff r).totalDegree ≤ N) (hg : ∀ r, (g.coeff r).totalDegree ≤ N) :
    (f.resultant g d e).totalDegree ≤ (d + e) * N := by
  rw [Polynomial.resultant]
  calc
    _ ≤ ∑ _ : Fin (d + e), N :=
      det_totalDegree_le_column_sum _ _ fun i j => by
        unfold Polynomial.sylvester
        simp only [Matrix.of_apply]
        induction j using Fin.addCases with
        | left j => rw [Fin.addCases_left]; split_ifs <;> first | exact hg _ | simp
        | right j => rw [Fin.addCases_right]; split_ifs <;> first | exact hf _ | simp
    _ = _ := by simp

/-- Four observation columns and five derivative columns give the cleared minor budget. -/
theorem clearedMinor_totalDegree_le (M : Matrix (Fin 9) (Fin 9) (MvPolynomial σ R))
    (hM : ∀ i j, (M i j).totalDegree ≤ 22 + 9 * (if j.val < 5 then 7 else 8)) :
    M.det.totalDegree ≤ 801 := by
  apply (det_totalDegree_le_column_sum M _ hM).trans
  decide +kernel

/-- The paired cleared minors give the common spectral budget for scalar forms. -/
theorem clearedMinorPair_totalDegree_le
    (M N : Matrix (Fin 9) (Fin 9) (MvPolynomial σ R))
    (hM : ∀ i j, (M i j).totalDegree ≤ 22 + 9 * (if j.val < 5 then 7 else 8))
    (hN : ∀ i j, (N i j).totalDegree ≤ 22 + 9 * (if j.val < 5 then 7 else 8)) :
    (M.det * N.det).totalDegree ≤ 1602 :=
  (totalDegree_mul _ _).trans
    (Nat.add_le_add (clearedMinor_totalDegree_le M hM) (clearedMinor_totalDegree_le N hN))

theorem projectionU_resultant_totalDegree_le
    (f g : Polynomial (MvPolynomial σ R))
    (hf : ∀ r, (f.coeff r).totalDegree ≤ 1602) (hg : ∀ r, (g.coeff r).totalDegree ≤ 1602) :
    (f.resultant g 20 20).totalDegree ≤ 64080 :=
  resultant_totalDegree_le f g 20 20 1602 hf hg

theorem projectionK_resultant_totalDegree_le
    (f g : Polynomial (MvPolynomial σ R))
    (hf : ∀ r, (f.coeff r).totalDegree ≤ 1602) (hg : ∀ r, (g.coeff r).totalDegree ≤ 1602) :
    (f.resultant g 18 19).totalDegree ≤ 59274 :=
  resultant_totalDegree_le f g 18 19 1602 hf hg

end UniformMPSHorizontalSpectral
