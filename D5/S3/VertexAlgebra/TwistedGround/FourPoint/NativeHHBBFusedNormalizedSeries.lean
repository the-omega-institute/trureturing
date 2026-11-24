import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHHBBFormalIterateExpansion
import Mathlib.Algebra.Polynomial.Reverse

/-! Cancellation of the root ratio in the formal HHBB iterate at the fused cusp. -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators TensorProduct Topology
open PowerSeries

namespace D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHHBBFusedNormalizedSeries

open ActualLeechHyperbolic (leechData)
open LatticeHalfFockChargedTensorCoefficients (ActualGround)
open NativeFixedPairAIterate (fixedAExponent fixedAIterateCoeff fixedASlitSewn)
open NativeHHBBFormalIterateExpansion (hhbb_marked_iterate_energy_expansion)
open NativeMixedWickChartTransport (MixedParity doubledOccupation)
open Orbifold.NativeOddTwistedIntertwiner (TwistedEven TwistedOdd leechUnit)
open OriginalFourMActualChart (Puncture)
open OriginalFourMVariableSupport (wordAt)

private theorem cancel_half_power (P : Polynomial ℂ) (a L N : ℕ)
    (hL : (L : ℤ) % 2 = 1) (hN : (N : ℤ) % 2 = 1) :
    let α : ℂ := (a : ℂ) + ((N : ℂ) - L + 1) / 2
    let k : ℤ := (a : ℤ) + ((N : ℤ) - L) / 2
    PowerSeries.binomialSeries ℂ (-1 / 2 : ℂ) *
      (∑ j ∈ P.support, C (P.coeff j) * PowerSeries.binomialSeries ℂ (α - j)) =
      ∑ j ∈ P.support, C (P.coeff j) * PowerSeries.binomialSeries ℂ ((k : ℂ) - j) := by
  intro α k
  have hEven : (N : ℤ) - L = 2 * (((N : ℤ) - L) / 2) := by omega
  have hCast : (N : ℂ) - L = 2 * (↑(((N : ℤ) - L) / 2) : ℂ) := by
    exact_mod_cast hEven
  have hShift : (-1 / 2 : ℂ) + α = (k : ℂ) := by
    dsimp only [α, k]
    push_cast
    rw [hCast]
    ring
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_left_comm, ← binomialSeries_add, ← add_sub_assoc, hShift]

private theorem doubledOccupation_toNat_cast {X : Type*}
    (slot : X → Puncture) (n : X → ℕ) (l : List X) (i : Puncture) :
    ((doubledOccupation slot n l i).toNat : ℤ) = doubledOccupation slot n l i := by
  apply Int.toNat_of_nonneg
  classical
  unfold doubledOccupation
  apply List.sum_nonneg
  intro m hm
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hm
  split <;> omega

/-- In the coordinate `s = (x - z) / z`, multiplication by the formal root ratio
`Z / X = (1 + s)^(-1/2)` makes the exponent of each marked HHBB iterate summand integral. -/
theorem hhbb_marked_iterate_normalized_powerSeries {X : Type*} [Finite X]
    (slot : X → Puncture) (colour : X → Fin leechData.rank) (n : X → ℕ) (l : List X)
    (hl : l.Nodup) (hpar : MixedParity slot n l)
    (u v : TwistedEven) (w bState : TwistedOdd) (p q r d : ActualGround leechData leechUnit)
    (hu : u.val = wordAt leechData slot colour n l .P ⊗ₜ[ℂ] p)
    (hv : v.val = wordAt leechData slot colour n l .Q ⊗ₜ[ℂ] q)
    (hw : w.val = wordAt leechData slot colour n l .R ⊗ₜ[ℂ] r)
    (hb : bState.val = wordAt leechData slot colour n l .S ⊗ₜ[ℂ] d)
    (H : ℂ → ℂ) (P : Polynomial ℂ) :
    let grade (i : Puncture) := (doubledOccupation slot n l i).toNat
    let V := wordAt leechData slot colour n l
    let M := grade .P
    let K := grade .Q
    let L := grade .R
    let N := grade .S
    let a := (5 + K + L) / 2
    let b := (6 + M + K) / 2
    let A (s : ℂ) := fixedASlitSewn M K (V .P) (V .Q) (V .R) (V .S) p q r d (-s)
    let c (E : ℕ) := fixedAIterateCoeff false M K L N (fixedAExponent M K E)
      u v w.val bState.val
    let k : ℤ := (a : ℤ) + ((N : ℤ) - L) / 2
    (∀ᶠ y : ℂ in 𝓝[≠] (1 : ℂ), H y = P.eval y / (y ^ a * (1 - y) ^ b)) →
    (∀ y : ℂ, (1 / 2 : ℝ) < y.re → y ≠ 1 →
      H y = (1 - y) ^ (-((6 + (M : ℤ) + K) / 2)) *
        (Complex.sqrt y * (Complex.sqrt y ^ ((N : ℤ) - L) * A ((1 - y) / y)))) →
    PowerSeries.binomialSeries ℂ (-1 / 2 : ℂ) * PowerSeries.mk c =
      ∑ j ∈ P.support, C (P.coeff j) * PowerSeries.binomialSeries ℂ ((k : ℂ) - j) := by
  intro grade V M K L N a b A c k hRational hNormalized
  have hL : (L : ℤ) % 2 = 1 := by
    simpa only [L, grade, doubledOccupation_toNat_cast] using hpar.2.2.1
  have hN : (N : ℤ) % 2 = 1 := by
    simpa only [N, grade, doubledOccupation_toNat_cast] using hpar.2.2.2
  obtain ⟨hSeries, _⟩ := hhbb_marked_iterate_energy_expansion
    slot colour n l hl hpar u v w bState p q r d hu hv hw hb H P hRational hNormalized
  calc
    PowerSeries.binomialSeries ℂ (-1 / 2 : ℂ) * PowerSeries.mk c =
        PowerSeries.binomialSeries ℂ (-1 / 2 : ℂ) *
          (∑ j ∈ P.support, C (P.coeff j) *
            PowerSeries.binomialSeries ℂ ((a : ℂ) + ((N : ℂ) - L + 1) / 2 - j)) :=
      congrArg (PowerSeries.binomialSeries ℂ (-1 / 2 : ℂ) * ·) hSeries
    _ = _ := cancel_half_power P a L N hL hN

private def binomialUnits : Multiplicative ℂ →* (PowerSeries ℂ)ˣ where
  toFun t := Units.mkOfMulEqOne (PowerSeries.binomialSeries ℂ t.toAdd) (PowerSeries.binomialSeries ℂ (-t.toAdd)) (by
    rw [← binomialSeries_add, add_neg_cancel, binomialSeries_zero])
  map_one' := Units.ext (binomialSeries_zero (R := ℂ))
  map_mul' t u := Units.ext (binomialSeries_add t.toAdd u.toAdd)

/-- The unit `1 + s` in the power series ring of the fused chart. -/
def oneAddXUnit : (PowerSeries ℂ)ˣ :=
  binomialUnits (Multiplicative.ofAdd 1)

@[simp] theorem coe_oneAddXUnit : (oneAddXUnit : PowerSeries ℂ) = 1 + PowerSeries.X := by
  change PowerSeries.binomialSeries ℂ (1 : ℂ) = 1 + PowerSeries.X
  simpa only [Nat.cast_one, pow_one] using (binomialSeries_nat (R := ℂ) (A := ℂ) 1)

private theorem coe_oneAddXUnit_zpow (m : ℤ) :
    (↑(oneAddXUnit ^ m) : PowerSeries ℂ) = PowerSeries.binomialSeries ℂ (m : ℂ) := by
  rw [oneAddXUnit, ← map_zpow]
  change PowerSeries.binomialSeries ℂ (m • (1 : ℂ)) = _
  rw [zsmul_eq_mul, mul_one]

/-- For any degree bound `d`, the integer-exponent sum factors as the unit
`(1 + s)^(k-d)` times the degree-padded reverse numerator evaluated at `1+s`. -/
theorem integral_binomial_sum_eq_reflect (P : Polynomial ℂ) (k : ℤ) (d : ℕ)
    (hd : P.natDegree ≤ d) :
    (∑ j ∈ P.support, C (P.coeff j) * PowerSeries.binomialSeries ℂ ((k : ℂ) - j)) =
      (↑(oneAddXUnit ^ (k - (d : ℤ))) : PowerSeries ℂ) *
        (P.reflect d).eval₂ C (1 + PowerSeries.X) := by
  rw [coe_oneAddXUnit_zpow, Polynomial.eval₂_eq_sum, Polynomial.sum, Polynomial.reflect_support,
    Finset.sum_image (fun _ _ _ _ h => (Polynomial.revAt d).injective h), Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjd : j ≤ d := (Polynomial.le_natDegree_of_mem_supp j hj).trans hd
  rw [Polynomial.coeff_reflect, Polynomial.revAt_invol, Polynomial.revAt_le hjd,
    ← binomialSeries_nat (R := ℂ) (A := ℂ) (d - j), mul_left_comm, ← binomialSeries_add]
  have hExp : (↑(k - (d : ℤ)) : ℂ) + ((d - j : ℕ) : ℂ) = (k : ℂ) - j := by
    push_cast [Nat.cast_sub hjd]
    ring
  rw [hExp]

end D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHHBBFusedNormalizedSeries
