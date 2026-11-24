import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHHBBTwoVariableRational
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHHBBFormalZeroExpansion

/-! The formal product expansion of the common HHBB rational function for `|x| > |z|`. -/

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

namespace D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHHBBFormalProductIota

open CollisionLaurentKernels.LaurentCollision
  (Bivariate Rational XZ T T_ne_zero iotaXZ polyXZ polyXZ_C_X polyXZ_X)
open CollisionLaurentKernels.PolynomialCollision (polyXZ_constant)
open NativeHHBBTwoVariableRational
  (commonRational commonRational_mul_denominator denominator homogenizedNumerator)
open HahnSeries (single)

local notation "xL" => (HahnSeries.C (T ℂ) : XZ ℂ)
local notation "zL" => (single (1 : ℤ) (1 : LaurentSeries ℂ) : XZ ℂ)
local notation "atRatio" =>
  (RingHom.comp (HahnSeries.ofPowerSeries ℤ (LaurentSeries ℂ))
    (RingHom.comp (PowerSeries.rescale (T ℂ)⁻¹)
      (PowerSeries.map (HahnSeries.C : ℂ →+* LaurentSeries ℂ))))

private theorem atRatio_C (r : ℂ) :
    atRatio (PowerSeries.C r) = HahnSeries.C (HahnSeries.C r) := by
  have h (s : LaurentSeries ℂ) :
      PowerSeries.rescale (T ℂ)⁻¹ (PowerSeries.C s) = PowerSeries.C s := by
    ext n
    simp only [PowerSeries.coeff_rescale, PowerSeries.coeff_C]
    split_ifs with hn
    · subst n
      simp
    · simp
  simp only [RingHom.comp_apply, PowerSeries.map_C, h, HahnSeries.ofPowerSeries_C]

private theorem x_mul_atRatio_X : xL * atRatio PowerSeries.X = zL := by
  simp only [RingHom.comp_apply, PowerSeries.map_X, PowerSeries.rescale_X,
    map_mul, HahnSeries.ofPowerSeries_C, HahnSeries.ofPowerSeries_X, HahnSeries.C_apply,
    HahnSeries.single_mul_single, zero_add, mul_one, mul_inv_cancel₀ (T_ne_zero ℂ)]

private theorem atRatio_coeff_nat (F : PowerSeries ℂ) (m : ℕ) :
    (atRatio F).coeff (m : ℤ) = single (-(m : ℤ)) (PowerSeries.coeff m F) := by
  change ((PowerSeries.rescale (T ℂ)⁻¹ (PowerSeries.map HahnSeries.C F) :
    PowerSeries (LaurentSeries ℂ)) : XZ ℂ).coeff (m : ℤ) = _
  rw [LaurentSeries.coeff_coe_powerSeries, PowerSeries.coeff_rescale, PowerSeries.coeff_map]
  rw [inv_pow, ← zpow_natCast (T ℂ) m, ← zpow_neg]
  simp only [T, ← RatFunc.single_zpow, HahnSeries.C_apply, HahnSeries.single_mul_single,
    add_zero, one_mul]

private theorem atRatio_coeff_neg (F : PowerSeries ℂ) (k : ℤ) (hk : k < 0) :
    (atRatio F).coeff k = 0 := by
  change ((PowerSeries.rescale (T ℂ)⁻¹ (PowerSeries.map HahnSeries.C F) :
    PowerSeries (LaurentSeries ℂ)) : XZ ℂ).coeff k = _
  rw [PowerSeries.coeff_coe, ite_eq_left hk]

private theorem iotaXZ_algebraMap (p : Bivariate ℂ) :
    iotaXZ ℂ (algebraMap (Bivariate ℂ) (Rational ℂ) p) = polyXZ ℂ p :=
  IsFractionRing.lift_algebraMap _ _

private theorem polyXZ_homogenizedNumerator (P : Polynomial ℂ) (d : ℕ)
    (hP : P.natDegree ≤ d) :
    polyXZ ℂ (homogenizedNumerator P d) = xL ^ d * atRatio P.toPowerSeries := by
  have hsum := P.as_sum_range_C_mul_X_pow' (Nat.lt_succ_of_le hP)
  have hSeries : P.toPowerSeries =
      ∑ j ∈ Finset.range (d + 1), PowerSeries.C (P.coeff j) * PowerSeries.X ^ j := by
    change Polynomial.coeToPowerSeries.ringHom P = _
    rw [congrArg Polynomial.coeToPowerSeries.ringHom hsum]
    simp only [map_sum, map_mul, map_pow, Polynomial.coeToPowerSeries.ringHom_apply,
      Polynomial.coe_C, Polynomial.coe_X]
  rw [hSeries, homogenizedNumerator, map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjd : j ≤ d := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hx : xL ^ d = xL ^ (d - j) * xL ^ j := by
    rw [← pow_add, Nat.sub_add_cancel hjd]
  simp only [map_mul, map_pow, polyXZ_constant, polyXZ_C_X, polyXZ_X, atRatio_C]
  rw [hx, ← x_mul_atRatio_X, mul_pow]
  ac_rfl

private theorem iotaXZ_commonRational_factor (P : Polynomial ℂ) (d M K L : ℕ)
    (hP : P.natDegree ≤ d) :
    let a := (5 + K + L) / 2
    let b := (6 + M + K) / 2
    let c := (M + L + 7) / 2
    iotaXZ ℂ (commonRational P d M K L) =
      single (-(a : ℤ)) (single ((d : ℤ) - c - b) (1 : ℂ)) *
        atRatio (P.toPowerSeries * (PowerSeries.invOneSubPow ℂ b).val) := by
  intro a b c
  let e : ℤ := (d : ℤ) - c - b
  have hx : xL ≠ 0 := by simp [HahnSeries.C_apply, T_ne_zero]
  have hz : zL ≠ 0 := by simp
  have hSep : xL - zL ≠ 0 := by
    intro h
    have heq := congrArg (fun F : XZ ℂ => F.coeff 0) h
    exact T_ne_zero ℂ (by simpa [HahnSeries.C_apply] using heq)
  have hFactor : xL - zL = xL * atRatio (1 - PowerSeries.X) := by
    rw [map_sub, map_one atRatio, mul_sub, mul_one, x_mul_atRatio_X]
  have hDen : polyXZ ℂ (denominator M K L) =
      xL ^ c * zL ^ a * (xL - zL) ^ b := by
    simp only [denominator, map_mul, map_pow, map_sub, polyXZ_C_X, polyXZ_X, a, b, c]
  have hDen₀ : polyXZ ℂ (denominator M K L) ≠ 0 := by
    rw [hDen]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hx) (pow_ne_zero _ hz)) (pow_ne_zero _ hSep)
  have hClear := congrArg (iotaXZ ℂ) (commonRational_mul_denominator P d M K L)
  simp only [map_mul, iotaXZ_algebraMap, polyXZ_homogenizedNumerator P d hP] at hClear
  apply (mul_left_inj' hDen₀).mp
  rw [hClear, hDen, hFactor, mul_pow]
  have hScale : xL ^ e * xL ^ c * xL ^ b = xL ^ d := by
    rw [← zpow_natCast xL c, ← zpow_natCast xL b, ← zpow_natCast xL d,
      ← zpow_add₀ hx, ← zpow_add₀ hx]
    congr 1
    dsimp only [e]
    omega
  have hShift : zL ^ (-(a : ℤ)) * zL ^ a = 1 := by
    rw [← zpow_natCast zL a, ← zpow_add₀ hz, neg_add_cancel, zpow_zero]
  have hMono : single (-(a : ℤ)) (single e (1 : ℂ)) = xL ^ e * zL ^ (-(a : ℤ)) := by
    have hC : (HahnSeries.C : LaurentSeries ℂ →+* XZ ℂ) (T ℂ ^ e) = xL ^ e :=
      map_zpow₀ (G₀ := LaurentSeries ℂ) (G₀' := XZ ℂ) HahnSeries.C (T ℂ) e
    have ht : T ℂ ^ e = single e (1 : ℂ) := (RatFunc.single_zpow e).symm
    have hzpow : zL ^ (-(a : ℤ)) = single (-(a : ℤ)) (1 : LaurentSeries ℂ) :=
      (RatFunc.single_zpow _).symm
    rw [← hC, ht, hzpow,
      HahnSeries.C_apply, HahnSeries.single_mul_single, zero_add, mul_one]
  have hInv :
      atRatio (PowerSeries.invOneSubPow ℂ b).val *
        atRatio (1 - PowerSeries.X) ^ b = 1 := by
    rw [← map_pow, ← map_mul, ← PowerSeries.invOneSubPow_inv_eq_one_sub_pow,
      Units.val_inv, map_one]
  change xL ^ d * atRatio P.toPowerSeries =
    single (-(a : ℤ)) (single e (1 : ℂ)) *
      atRatio (P.toPowerSeries * (PowerSeries.invOneSubPow ℂ b).val) *
        (xL ^ c * zL ^ a * (xL ^ b * atRatio (1 - PowerSeries.X) ^ b))
  rw [hMono, map_mul]
  calc
    _ = (xL ^ e * xL ^ c * xL ^ b) * atRatio P.toPowerSeries *
        (zL ^ (-(a : ℤ)) * zL ^ a) *
        (atRatio (PowerSeries.invOneSubPow ℂ b).val *
          atRatio (1 - PowerSeries.X) ^ b) := by rw [hScale, hShift, hInv, mul_one, mul_one]
    _ = _ := by ring

/-- The outer coefficient at `z^(m-a)` is a single inner monomial. -/
theorem iotaXZ_commonRational_coeff (P : Polynomial ℂ) (d M K L : ℕ)
    (hP : P.natDegree ≤ d) (m : ℕ) :
    let a := (5 + K + L) / 2
    let b := (6 + M + K) / 2
    let c := (M + L + 7) / 2
    (iotaXZ ℂ (commonRational P d M K L)).coeff ((m : ℤ) - a) =
      single ((d : ℤ) - c - b - m)
        (PowerSeries.coeff m (P.toPowerSeries * (PowerSeries.invOneSubPow ℂ b).val)) := by
  intro a b c
  rw [iotaXZ_commonRational_factor P d M K L hP, HahnSeries.coeff_single_mul]
  rw [show (m : ℤ) - a - (-(a : ℤ)) = (m : ℤ) by omega,
    atRatio_coeff_nat, HahnSeries.single_mul_single, one_mul]
  simp only [b, c, sub_eq_add_neg]

/-- All outer coefficients below the pole bound vanish. Every index at or above
the bound is `m-a` for some natural number `m`. -/
theorem iotaXZ_commonRational_coeff_of_lt (P : Polynomial ℂ) (d M K L : ℕ)
    (hP : P.natDegree ≤ d) (k : ℤ) (hk : k < -(((5 + K + L) / 2 : ℕ) : ℤ)) :
    (iotaXZ ℂ (commonRational P d M K L)).coeff k = 0 := by
  rw [iotaXZ_commonRational_factor P d M K L hP, HahnSeries.coeff_single_mul,
    atRatio_coeff_neg _ _ (sub_neg.mpr hk), mul_zero]

open Complex (I)
open ActualLeechHyperbolic (leechData)
open LatticeHalfFockChargedTensorCoefficients (ActualGround)
open Orbifold.NativeOddTwistedIntertwiner (TwistedEven TwistedOdd leechUnit)
open OriginalFourMActualChart (Puncture)
open OriginalFourMVariableSupport (wordAt)
open OriginalGaussianSewnAnalytic (coefficient)
open NativeMixedWickChartTransport (MixedParity doubledOccupation)
open NativeMixedUpperProductCusp (bJointTerm bProductCoeff bSewnNumerator)
open NativeHHBBFormalZeroExpansion (hhbb_marked_b_zero_powerSeries)

/-- The product coefficient of the marked amplitude, with the sign of the common
rational function and the polynomial from the cleared infinity germ. -/
theorem hhbb_marked_iotaXZ_bProductCoeff {ι : Type*} [Finite ι]
    (slot : ι → Puncture) (colour : ι → Fin leechData.rank) (n : ι → ℕ) (l : List ι)
    (hl : l.Nodup) (hpar : MixedParity slot n l)
    (u v : TwistedEven) (w bState : TwistedOdd) (p q r s : ActualGround leechData leechUnit)
    (hu : u.val = wordAt leechData slot colour n l .P ⊗ₜ[ℂ] p)
    (hv : v.val = wordAt leechData slot colour n l .Q ⊗ₜ[ℂ] q)
    (hw : w.val = wordAt leechData slot colour n l .R ⊗ₜ[ℂ] r)
    (hb : bState.val = wordAt leechData slot colour n l .S ⊗ₜ[ℂ] s) (m : ℕ) :
    let grade (i : Puncture) := (doubledOccupation slot n l i).toNat
    let V := wordAt leechData slot colour n l
    let M := grade .P
    let K := grade .Q
    let L := grade .R
    let N := grade .S
    let a := (5 + K + L) / 2
    let b := (6 + M + K) / 2
    let c := (M + L + 7) / 2
    let d := (12 + M + K + L + N) / 2
    let GInf (z : ℂ) := I ^ ((L : ℤ) + N - K - 2 * (M : ℤ) - 3) *
      bSewnNumerator M L N (V .Q) (V .P) (V .R) (V .S) q p r s z
    let G (z : ℂ) := (z - 1) ^ b * GInf z
    let P := ∑ j ∈ Finset.range (d + 1),
      Polynomial.C (coefficient j G) * Polynomial.X ^ (d - j)
    (iotaXZ ℂ (commonRational P d M K L)).coeff ((m : ℤ) - a) =
      single ((d : ℤ) - c - b - m) (-bProductCoeff false false M K L N v w u bState m) := by
  intro grade V M K L N a b c d GInf G P
  have hP : P.natDegree ≤ d := by
    exact Polynomial.natDegree_sum_le_of_forall_le _ _ fun j _ =>
      (Polynomial.natDegree_C_mul_X_pow_le (coefficient j G) (d - j)).trans (Nat.sub_le d j)
  have hB : PowerSeries.mk (fun E : ℕ => -bProductCoeff false false M K L N v w u bState E) =
      P.toPowerSeries * (PowerSeries.invOneSubPow ℂ b).val :=
    hhbb_marked_b_zero_powerSeries slot colour n l hl hpar u v w bState p q r s hu hv hw hb
  rw [iotaXZ_commonRational_coeff P d M K L hP, ← hB, PowerSeries.coeff_mk]

/-- Multiplication by `Z/X` puts the actual B term at the same squared-coordinate
exponents as the formal coefficient. -/
theorem bJointTerm_mul_rootRatio (M K L N m : ℕ)
    (hM : (M : ℤ) % 2 = 0) (hK : (K : ℤ) % 2 = 0)
    (hL : (L : ℤ) % 2 = 1) (hN : (N : ℤ) % 2 = 1)
    (v u : TwistedEven) (w bState : TwistedOdd) {X Z : ℂ} (hX : X ≠ 0) (hZ : Z ≠ 0) :
    let a := (5 + K + L) / 2
    let b := (6 + M + K) / 2
    let c := (M + L + 7) / 2
    let d := (12 + M + K + L + N) / 2
    let j := 2 * (m : ℤ) - (6 + (K : ℤ) + L)
    let k := (N : ℤ) - M - 2 * (m : ℤ)
    (Z / X) * bJointTerm false false v w u bState X Z (j, k) =
      bProductCoeff false false M K L N v w u bState m *
        ((Z ^ (2 : ℕ)) ^ ((m : ℤ) - a) * (X ^ (2 : ℕ)) ^ ((d : ℤ) - c - b - m)) := by
  intro a b c d j k
  have hj : 1 + j = 2 * ((m : ℤ) - a) := by
    dsimp only [j, a]
    push_cast
    omega
  have hk : k - 1 = 2 * ((d : ℤ) - c - b - m) := by
    dsimp only [k, d, c, b]
    push_cast
    omega
  have hZpow : Z * Z ^ j = (Z ^ (2 : ℕ)) ^ ((m : ℤ) - a) := by
    calc
      Z * Z ^ j = Z ^ ((1 : ℤ) + j) := by rw [zpow_add₀ hZ, zpow_one]
      _ = _ := by rw [hj, zpow_mul, zpow_ofNat]
  have hXpow : X ^ k * X⁻¹ = (X ^ (2 : ℕ)) ^ ((d : ℤ) - c - b - m) := by
    calc
      X ^ k * X⁻¹ = X ^ (k - 1) := by rw [zpow_sub₀ hX k 1, zpow_one, div_eq_mul_inv]
      _ = _ := by rw [hk, zpow_mul, zpow_ofNat]
  have hTerm : bJointTerm false false v w u bState X Z (j, k) =
      bProductCoeff false false M K L N v w u bState m * (Z ^ j * X ^ k) := rfl
  rw [← hZpow, ← hXpow, hTerm, div_eq_mul_inv]
  ac_rfl

end D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHHBBFormalProductIota
