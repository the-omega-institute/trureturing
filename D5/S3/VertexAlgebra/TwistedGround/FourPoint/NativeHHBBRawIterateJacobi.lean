import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHHBBModeResidue

set_option autoImplicit false

noncomputable section

namespace D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHHBBModeResidue

open scoped BigOperators TensorProduct

/-- Absorb the binomial twist into the outer weight for any signed index and exponent.
For a negative index both sums are empty. -/
theorem modePairs_raw_iterate (rawA : ℕ → ℂ) (q k : ℤ) :
    (∑ ij ∈ modePairs k, ((Ring.choose q ij.2 : ℤ) : ℂ) *
      PowerSeries.coeff ij.1
        (PowerSeries.binomialSeries ℂ (-1 / 2 : ℂ) * PowerSeries.mk rawA)) =
    ∑ ij ∈ modePairs k, Ring.choose ((q : ℂ) - 1 / 2) ij.2 * rawA ij.1 := by
  by_cases hk : 0 ≤ k
  · rw [modePairs, Finset.filter_true_of_mem fun _ _ => hk]
    have coeff_binomial_mul (z : ℂ) (F : PowerSeries ℂ) :
        PowerSeries.coeff k.toNat (PowerSeries.binomialSeries ℂ z * F) =
          ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal k.toNat,
            Ring.choose z ij.2 * PowerSeries.coeff ij.1 F := by
      rw [mul_comm, PowerSeries.coeff_mul]
      simp only [PowerSeries.binomialSeries_coeff, smul_eq_mul, mul_one]
      apply Finset.sum_congr rfl
      intro ij _
      exact mul_comm (PowerSeries.coeff ij.1 F) (Ring.choose z ij.2)
    have cast_choose (j : ℕ) :
        ((Ring.choose q j : ℤ) : ℂ) = Ring.choose (q : ℂ) j :=
      Ring.map_choose (Int.castRingHom ℂ) q j
    calc
      _ = PowerSeries.coeff k.toNat (PowerSeries.binomialSeries ℂ (q : ℂ) *
            (PowerSeries.binomialSeries ℂ (-1 / 2 : ℂ) * PowerSeries.mk rawA)) := by
        rw [coeff_binomial_mul]
        simp only [cast_choose]
      _ = PowerSeries.coeff k.toNat
            (PowerSeries.binomialSeries ℂ ((q : ℂ) - 1 / 2) * PowerSeries.mk rawA) := by
        rw [← mul_assoc, ← PowerSeries.binomialSeries_add, neg_div, ← sub_eq_add_neg]
      _ = _ := by
        rw [coeff_binomial_mul]
        simp only [PowerSeries.coeff_mk]
  · simp [modePairs, hk]

open ActualLeechHyperbolic (leechData)
open LatticeHalfFockChargedTensorCoefficients (ActualGround)
open Orbifold.NativeOddTwistedIntertwiner (TwistedEven TwistedOdd leechUnit)
open NativeFixedPairAIterate (fixedAExponent fixedAIterateCoeff)
open NativeMixedUpperProductCusp (bProductCoeff)
open NativeMixedUpperDLip (dProductCoeff)
open NativeMixedWickChartTransport (MixedParity doubledOccupation)
open OriginalFourMActualChart (Puncture)
open OriginalFourMVariableSupport (wordAt)

/-- Marked HHBB Jacobi with the raw native iterate on the right, for every integer
test monomial and in its outer-residue form on the degree `-2` slice. -/
theorem hhbb_marked_coefficient_jacobi_raw {ι : Type*} [Finite ι]
    (slot : ι → Puncture) (colour : ι → Fin leechData.rank) (n : ι → ℕ) (l : List ι)
    (hl : l.Nodup) (hpar : MixedParity slot n l)
    (u v : TwistedEven) (wState bState : TwistedOdd)
    (gP gQ gR gS : ActualGround leechData leechUnit)
    (hu : u.val = wordAt leechData slot colour n l .P ⊗ₜ[ℂ] gP)
    (hv : v.val = wordAt leechData slot colour n l .Q ⊗ₜ[ℂ] gQ)
    (hw : wState.val = wordAt leechData slot colour n l .R ⊗ₜ[ℂ] gR)
    (hb : bState.val = wordAt leechData slot colour n l .S ⊗ₜ[ℂ] gS)
    (q p r : ℤ) :
    let grade (i : Puncture) := (doubledOccupation slot n l i).toNat
    let M := grade .P
    let K := grade .Q
    let L := grade .R
    let N := grade .S
    let a : ℕ := (5 + K + L) / 2
    let b : ℕ := (6 + M + K) / 2
    let c : ℕ := (M + L + 7) / 2
    let w : ℤ := ((N : ℤ) - M - K - L - 6) / 2
    let B := bProductCoeff false false M K L N v wState u bState
    let D := dProductCoeff false false M K L N u wState v bState
    let rawA (m : ℕ) := fixedAIterateCoeff false M K L N (fixedAExponent M K m)
      u v wState.val bState.val
    let dTerm := ∑ ij ∈ modePairs ((c : ℤ) - q - 1),
      (-1 : ℂ) ^ (r + (ij.2 : ℤ)) * ((Ring.choose r ij.2 : ℤ) : ℂ) * D ij.1
    let aTerm := ∑ ij ∈ modePairs ((b : ℤ) - r - 1),
      Ring.choose ((q : ℂ) - 1 / 2) ij.2 * rawA ij.1
    ((∑ ij ∈ modePairs (w + a + q + r + 1),
        (-1 : ℂ) ^ ij.2 * ((Ring.choose r ij.2 : ℤ) : ℂ) * (-B ij.1)) - dTerm = aTerm) ∧
    (w + q + p + r = -2 →
      (∑ ij ∈ modePairs ((a : ℤ) - p - 1),
        (-1 : ℂ) ^ ij.2 * ((Ring.choose r ij.2 : ℤ) : ℂ) * (-B ij.1)) - dTerm = aTerm) := by
  intro grade M K L N a b c w B D rawA dTerm aTerm
  have hj := hhbb_marked_coefficient_jacobi slot colour n l hl hpar u v wState bState
    gP gQ gR gS hu hv hw hb q p r
  have ha := modePairs_raw_iterate rawA q ((b : ℤ) - r - 1)
  exact ⟨hj.1.trans ha, fun hbalance => (hj.2 hbalance).trans ha⟩

end D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHHBBModeResidue
