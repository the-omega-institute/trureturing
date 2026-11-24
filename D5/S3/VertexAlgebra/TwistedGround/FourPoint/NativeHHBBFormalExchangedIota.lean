import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHHBBTwoVariableRational
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHHBBFormalInfinityExpansion
import Mathlib.Algebra.Polynomial.Reverse

/-! Exchange the coordinates of the actual HHBB exterior Laurent expansion. -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators TensorProduct

namespace D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHHBBFormalExchangedIota

open CollisionLaurentKernels.LaurentCollision
open CollisionLaurentKernels.PolynomialCollision (iotaXZ_x)
open NativeHHBBTwoVariableRational (commonRational denominator homogenizedNumerator)
open NativeHHBBFormalInfinityExpansion (paddedReverse hhbb_marked_native_d_infinity_powerSeries)
open Polynomial (C X)
open Polynomial.Bivariate (swap swap_C_C swap_X swap_Y)

local notation "xPoly" => (C (X : Polynomial ℂ))
local notation "zPoly" => (X : Bivariate ℂ)

theorem paddedReverse_eq_reflect (P : Polynomial ℂ) (degree : ℕ)
    (hP : P.natDegree ≤ degree) : paddedReverse degree P = P.reflect degree := by
  have hDegree : (P.reflect degree).natDegree ≤ degree :=
    Polynomial.natDegree_reflect_le.trans (max_le le_rfl hP)
  rw [paddedReverse]
  conv_rhs => rw [(P.reflect degree).as_sum_range_C_mul_X_pow' (Nat.lt_succ_of_le hDegree),
    ← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro j hj
  have hjd : j ≤ degree := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  rw [show degree.succ - 1 = degree from rfl, Polynomial.coeff_reflect,
    Polynomial.revAt_le (Nat.sub_le degree j), Nat.sub_sub_self hjd]

set_option maxHeartbeats 1500000 in
/-- The bivariate swap reverses the chosen homogeneous degree, including the padding. -/
theorem swap_homogenizedNumerator (P : Polynomial ℂ) (degree : ℕ)
    (hP : P.natDegree ≤ degree) :
    swap (homogenizedNumerator P degree) =
      homogenizedNumerator (paddedReverse degree P) degree := by
  rw [paddedReverse_eq_reflect P degree hP]
  unfold homogenizedNumerator
  rw [map_sum (swap (R := ℂ))]
  conv_rhs => rw [← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro j hj
  have hjd : j ≤ degree := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  rw [show degree.succ - 1 = degree from rfl, Polynomial.coeff_reflect,
    Polynomial.revAt_le (Nat.sub_le degree j), Nat.sub_sub_self hjd]
  simp only [map_mul, map_pow, swap_C_C, swap_X, swap_Y]
  rw [mul_assoc, mul_assoc, mul_comm (zPoly ^ (degree - j)) (xPoly ^ j)]

private theorem homogenizedNumerator_C_mul (s : ℂ) (P : Polynomial ℂ) (degree : ℕ) :
    homogenizedNumerator (C s * P) degree = C (C s) * homogenizedNumerator P degree := by
  simp only [homogenizedNumerator, Polynomial.coeff_C_mul, map_mul, Finset.mul_sum, mul_assoc]

set_option maxHeartbeats 1500000 in
/-- The diagonal pole contributes one minus sign per power after exchange. -/
theorem swap_denominator (M K L : ℕ) :
    let a := (5 + K + L) / 2
    let b := (6 + M + K) / 2
    let c := (M + L + 7) / 2
    swap (denominator M K L) = (-1 : Bivariate ℂ) ^ b * (xPoly ^ a * zPoly ^ c * (xPoly - zPoly) ^ b) := by
  intro a b c
  simp only [denominator, map_mul, map_pow, map_sub, swap_X, swap_Y]
  change zPoly ^ c * xPoly ^ a * (zPoly - xPoly) ^ b = _
  have hdiag : zPoly - xPoly = (-1 : Bivariate ℂ) * (xPoly - zPoly) :=
    (neg_sub xPoly zPoly).symm.trans (neg_one_mul (xPoly - zPoly)).symm
  rw [hdiag, mul_pow, mul_comm (zPoly ^ c) (xPoly ^ a), ← mul_assoc, mul_comm _ ((-1 : Bivariate ℂ) ^ b),
    mul_assoc]

/-- The existing exterior embedding is the product embedding after the fraction-ring swap. -/
theorem iotaZX_eq_iotaXZ_swap {K : Type*} [Field K] :
    iotaZX K = (iotaXZ K).comp
      (IsFractionRing.ringEquivOfRingEquiv
        (K := Rational K) (L := Rational K) (swap (R := K)).toRingEquiv).toRingHom := by
  apply IsFractionRing.ringHom_ext (A := Bivariate K)
  intro f
  change iotaZX K (algebraMap (Bivariate K) (Rational K) f) =
    iotaXZ K (IsFractionRing.ringEquivOfRingEquiv (K := Rational K) (L := Rational K)
      (swap (R := K)).toRingEquiv (algebraMap (Bivariate K) (Rational K) f))
  rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap, iotaZX, iotaXZ,
    IsFractionRing.lift_algebraMap, IsFractionRing.lift_algebraMap]
  rfl

/-- The inverse of the denominator sign is the same sign, so it multiplies the
reflected numerator in ordinary product coordinates. -/
theorem swap_commonRational (P : Polynomial ℂ) (degree M K L : ℕ)
    (hP : P.natDegree ≤ degree) :
    let a := (5 + K + L) / 2
    let b := (6 + M + K) / 2
    let c := (M + L + 7) / 2
    IsFractionRing.ringEquivOfRingEquiv (K := Rational ℂ) (L := Rational ℂ)
        (swap (R := ℂ)).toRingEquiv (commonRational P degree M K L) =
      algebraMap (Bivariate ℂ) (Rational ℂ)
          (homogenizedNumerator (C ((-1 : ℂ) ^ b) * paddedReverse degree P) degree) /
        (x ℂ ^ a * z ℂ ^ c * (x ℂ - z ℂ) ^ b) := by
  intro a b c
  rw [commonRational, map_div₀, IsFractionRing.ringEquivOfRingEquiv_algebraMap,
    IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  change algebraMap (Bivariate ℂ) (Rational ℂ) (swap (homogenizedNumerator P degree)) /
      algebraMap (Bivariate ℂ) (Rational ℂ) (swap (denominator M K L)) = _
  rw [swap_homogenizedNumerator P degree hP, swap_denominator M K L,
    homogenizedNumerator_C_mul]
  simp only [map_mul, map_pow, map_neg, map_one, map_sub, x, z]
  set sign := (-1 : Rational ℂ) ^ b
  have hsign : sign * sign = 1 := by
    dsimp [sign]
    rw [← mul_pow, neg_mul_neg, one_mul, one_pow]
  have hs : sign ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  calc
    _ = (sign * (sign * algebraMap (Bivariate ℂ) (Rational ℂ)
        (homogenizedNumerator (paddedReverse degree P) degree))) / _ := by
      rw [← mul_assoc sign sign, hsign, one_mul]
    _ = _ := mul_div_mul_left _ _ hs

/-- The exterior embedding has outer coordinate x and inner coordinate z. -/
theorem iotaZX_commonRational_eq_iotaXZ (P : Polynomial ℂ) (degree M K L : ℕ)
    (hP : P.natDegree ≤ degree) :
    let a := (5 + K + L) / 2
    let b := (6 + M + K) / 2
    let c := (M + L + 7) / 2
    iotaZX ℂ (commonRational P degree M K L) =
      iotaXZ ℂ (algebraMap (Bivariate ℂ) (Rational ℂ)
          (homogenizedNumerator (C ((-1 : ℂ) ^ b) * paddedReverse degree P) degree) /
        (x ℂ ^ a * z ℂ ^ c * (x ℂ - z ℂ) ^ b)) := by
  intro a b c
  rw [iotaZX_eq_iotaXZ_swap, RingHom.comp_apply]
  exact congrArg (iotaXZ ℂ) (swap_commonRational P degree M K L hP)

/-- Exchanging the grades in the exact product theorem shifts its poles by one.
Multiplication by x/z corrects that shift at the level of the outer coefficients. -/
theorem iotaXZ_swapped_poles_coeff (Q : Polynomial ℂ) (degree M K L : ℕ) (k : ℤ) :
    let a := (5 + K + L) / 2
    let b := (6 + M + K) / 2
    let c := (M + L + 7) / 2
    (iotaXZ ℂ (algebraMap (Bivariate ℂ) (Rational ℂ) (homogenizedNumerator Q degree) /
        (x ℂ ^ a * z ℂ ^ c * (x ℂ - z ℂ) ^ b))).coeff k =
      T ℂ * (iotaXZ ℂ (commonRational Q degree K M L)).coeff (k + 1) := by
  intro a b c
  let a' := (5 + M + L) / 2
  let numerator := algebraMap (Bivariate ℂ) (Rational ℂ) (homogenizedNumerator Q degree)
  let swapped := numerator / (x ℂ ^ a * z ℂ ^ c * (x ℂ - z ℂ) ^ b)
  let D := x ℂ ^ a * z ℂ ^ a' * (x ℂ - z ℂ) ^ b
  have ha : (K + L + 7) / 2 = a + 1 := by dsimp [a]; omega
  have hb : (6 + K + M) / 2 = b := by dsimp [b]; omega
  have hc : c = a' + 1 := by dsimp [c, a']; omega
  have hzD : x ℂ ^ a * z ℂ ^ c * (x ℂ - z ℂ) ^ b = z ℂ * D := by
    rw [hc, pow_succ]
    dsimp only [D]
    ac_rfl
  have hxD : algebraMap (Bivariate ℂ) (Rational ℂ) (denominator K M L) = x ℂ * D := by
    simp only [denominator, map_pow, map_mul, map_sub]
    change x ℂ ^ ((K + L + 7) / 2) * z ℂ ^ a' * (x ℂ - z ℂ) ^ ((6 + K + M) / 2) = _
    rw [ha, hb, pow_succ]
    dsimp only [D]
    ac_rfl
  have hx : x ℂ ≠ 0 := by
    simpa only [x, map_zero] using
      (IsFractionRing.injective (Bivariate ℂ) (Rational ℂ)).ne (Polynomial.C_ne_zero.mpr Polynomial.X_ne_zero)
  have hz : z ℂ ≠ 0 := by
    simpa only [z, map_zero] using
      (IsFractionRing.injective (Bivariate ℂ) (Rational ℂ)).ne Polynomial.X_ne_zero
  have h : z ℂ * swapped = x ℂ * commonRational Q degree K M L := by
    change z ℂ * (numerator / _) = x ℂ * (numerator / _)
    rw [hzD, hxD, ← mul_div_assoc, ← mul_div_assoc]
    rw [mul_div_mul_left _ _ hz, mul_div_mul_left _ _ hx]
  have hCoeff := congrArg (fun F : Rational ℂ => (iotaXZ ℂ F).coeff (k + 1)) h
  simpa only [map_mul, iotaXZ_z, iotaXZ_x, HahnSeries.C_apply,
    HahnSeries.coeff_single_mul, HahnSeries.coeff_single_zero_mul, add_sub_cancel_right,
    sub_zero, one_mul] using hCoeff

open ActualLeechHyperbolic (leechData)
open Complex (I)
open LatticeHalfFockChargedTensorCoefficients (ActualGround)
open NativeMixedUpperDLip (dProductCoeff)
open NativeMixedUpperProductCusp (bSewnNumerator)
open NativeMixedWickChartTransport (MixedParity doubledOccupation)
open Orbifold.NativeOddTwistedIntertwiner (TwistedEven TwistedOdd leechUnit)
open OriginalFourMActualChart (Puncture)
open OriginalFourMVariableSupport (wordAt)
open OriginalGaussianSewnAnalytic (coefficient)

open private occupationGrade_eq from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedPhysicalOverlap
open private punctureExcitation_cast from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedUpperProductCusp

set_option maxHeartbeats 4000000 in
/-- Transfer the exhaustive product expansion at the swapped poles to the marked
native D coefficients. The outer x power and inner z power are the normalized
D mode exponents after multiplication by the root ratio Z/X. -/
theorem hhbb_marked_iotaZX_native_d_of_product {ι : Type*} [Finite ι]
    (slot : ι → Puncture) (colour : ι → Fin leechData.rank) (n : ι → ℕ) (l : List ι)
    (hl : l.Nodup) (hpar : MixedParity slot n l)
    (u v : TwistedEven) (w bState : TwistedOdd) (p q r s : ActualGround leechData leechUnit)
    (hu : u.val = wordAt leechData slot colour n l .P ⊗ₜ[ℂ] p)
    (hv : v.val = wordAt leechData slot colour n l .Q ⊗ₜ[ℂ] q)
    (hw : w.val = wordAt leechData slot colour n l .R ⊗ₜ[ℂ] r)
    (hb : bState.val = wordAt leechData slot colour n l .S ⊗ₜ[ℂ] s) :
    let grade (i : Puncture) := (doubledOccupation slot n l i).toNat
    let V := wordAt leechData slot colour n l
    let M := grade .P
    let K := grade .Q
    let L := grade .R
    let N := grade .S
    let a := (5 + K + L) / 2
    let b := (6 + M + K) / 2
    let c := (M + L + 7) / 2
    let degree := (12 + M + K + L + N) / 2
    let GInf (t : ℂ) := I ^ ((L : ℤ) + N - K - 2 * (M : ℤ) - 3) *
      bSewnNumerator M L N (V .Q) (V .P) (V .R) (V .S) q p r s t
    let P : Polynomial ℂ := ∑ j ∈ Finset.range (degree + 1),
      C (coefficient j (fun t => (t - 1) ^ b * GInf t)) * X ^ (degree - j)
    let Q := C ((-1 : ℂ) ^ b) * paddedReverse degree P
    let product := iotaXZ ℂ
      (algebraMap (Bivariate ℂ) (Rational ℂ) (homogenizedNumerator Q degree) /
        (x ℂ ^ a * z ℂ ^ c * (x ℂ - z ℂ) ^ b))
    let exterior := iotaZX ℂ (commonRational P degree M K L)
    (∀ E : ℕ, product.coeff ((E : ℤ) - c) =
      HahnSeries.single ((degree : ℤ) - a - b - E)
        (PowerSeries.coeff E (Q.toPowerSeries * (PowerSeries.invOneSubPow ℂ b).val))) →
    (∀ k : ℤ, k < -(c : ℤ) → product.coeff k = 0) →
    (∀ E : ℕ, exterior.coeff ((E : ℤ) - c) =
      HahnSeries.single ((1 + (N : ℤ) - K) / 2 - E)
        (dProductCoeff false false M K L N u w v bState E)) ∧
    (∀ k : ℤ, k < -(c : ℤ) → exterior.coeff k = 0) := by
  intro grade V M K L N a b c degree GInf P Q product exterior hProduct hBelow
  have hP : P.natDegree ≤ degree := by
    dsimp only [P]
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro j _
    exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (Nat.sub_le ..)
  have hExterior : exterior = product := iotaZX_commonRational_eq_iotaXZ P degree M K L hP
  have hSeries : PowerSeries.mk (dProductCoeff false false M K L N u w v bState) =
      Q.toPowerSeries * ↑(PowerSeries.invOneSubPow ℂ b) :=
    (hhbb_marked_native_d_infinity_powerSeries slot colour n l hl hpar
      u v w bState p q r s hu hv hw hb).2
  have hgrade (i : Puncture) : (grade i : ℤ) = doubledOccupation slot n l i := by
    change (((doubledOccupation slot n l i).toNat : ℕ) : ℤ) = _
    rw [occupationGrade_eq slot colour n l i, punctureExcitation_cast]
  have hM : (M : ℤ) % 2 = 0 := by simpa only [M, hgrade] using hpar.1
  have hK : (K : ℤ) % 2 = 0 := by simpa only [K, hgrade] using hpar.2.1
  have hL : (L : ℤ) % 2 = 1 := by simpa only [L, hgrade] using hpar.2.2.1
  have hN : (N : ℤ) % 2 = 1 := by simpa only [N, hgrade] using hpar.2.2.2
  have hMode : (degree : ℤ) - a - b = (1 + (N : ℤ) - K) / 2 := by
    dsimp only [degree, a, b]
    push_cast
    omega
  rw [hExterior]
  refine ⟨fun E => ?_, hBelow⟩
  rw [hProduct E, hMode, ← hSeries, PowerSeries.coeff_mk]

end D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHHBBFormalExchangedIota
