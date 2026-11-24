import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHHBBTwoVariableRational
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHHBBFormalChannels

/-! The formal HHBB expansion at the physical diagonal, with physical z fixed. -/

set_option autoImplicit false

noncomputable section

open scoped PowerSeries LaurentSeries TensorProduct
open HahnSeries

namespace D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHHBBFormalFusedIota

open CollisionLaurentKernels.LaurentCollision
open CollisionLaurentKernels.PolynomialCollision (iotaFused_x)
open NativeHHBBTwoVariableRational (commonRational denominator homogenizedNumerator)

/-- Lift the polynomial swap to the rational function field. This places physical
`x` in the outer variable and physical `z` in the coefficient ring. -/
def swapRational : Rational ℂ →+* Rational ℂ :=
  IsFractionRing.lift
    (g := (algebraMap (Bivariate ℂ) (Rational ℂ)).comp
      (Polynomial.Bivariate.swap (R := ℂ)).toRingHom)
    ((IsFractionRing.injective (Bivariate ℂ) (Rational ℂ)).comp
      (Polynomial.Bivariate.swap (R := ℂ)).injective)

private theorem swapRational_algebraMap (p : Bivariate ℂ) :
    swapRational (algebraMap (Bivariate ℂ) (Rational ℂ) p) =
      algebraMap (Bivariate ℂ) (Rational ℂ) (Polynomial.Bivariate.swap p) := by
  rw [swapRational, IsFractionRing.lift_algebraMap]
  rfl

/-- The HHBB rational function embedded in the chart `t=x-z` at fixed physical `z`. -/
def fusedLaurent (P : Polynomial ℂ) (degree M K L : ℕ) : XZ ℂ :=
  iotaFused ℂ (swapRational (commonRational P degree M K L))

/-- The power series in `s=t/z` left after extracting the pole and the homogeneous weight. -/
def fusedNumeratorSeries (P : Polynomial ℂ) (degree c : ℕ) : PowerSeries ℂ :=
  ∑ j ∈ Finset.range (degree + 1),
    PowerSeries.C (P.coeff j) * PowerSeries.binomialSeries ℂ ((degree : ℂ) - c - j)

private def fusedSeriesMap : PowerSeries ℂ →+* XZ ℂ :=
  (HahnSeries.ofPowerSeries ℤ (LaurentSeries ℂ)).comp
    ((PowerSeries.rescale (T ℂ)⁻¹).comp
      (PowerSeries.map (HahnSeries.C : ℂ →+* LaurentSeries ℂ)))

private theorem rescale_C (v : LaurentSeries ℂ) :
    PowerSeries.rescale (T ℂ)⁻¹ (PowerSeries.C v) = PowerSeries.C v := by
  ext n
  rw [PowerSeries.coeff_rescale, PowerSeries.coeff_C]
  split_ifs with h
  · simp [h]
  · simp

private theorem fusedSeriesMap_C (v : ℂ) :
    fusedSeriesMap (PowerSeries.C v) = HahnSeries.C (HahnSeries.C v) := by
  simp only [fusedSeriesMap, RingHom.comp_apply, PowerSeries.map_C, rescale_C,
    HahnSeries.ofPowerSeries_C]

private theorem fusedSeriesMap_binomial (k : ℤ) :
    fusedSeriesMap (PowerSeries.binomialSeries ℂ (k : ℂ)) =
      (1 + HahnSeries.single 1 (T ℂ)⁻¹ : XZ ℂ) ^ k := by
  rw [← binomial_zpow]
  have hm :
      PowerSeries.map (HahnSeries.C : ℂ →+* LaurentSeries ℂ)
        (PowerSeries.binomialSeries ℂ (k : ℂ)) =
      PowerSeries.binomialSeries (LaurentSeries ℂ) k := by
    ext1 n
    simp only [PowerSeries.coeff_map, PowerSeries.binomialSeries_coeff, smul_eq_mul, mul_one,
      Ring.map_choose, map_intCast, zsmul_eq_mul]
    exact (Ring.map_choose (Int.castRingHom (LaurentSeries ℂ)) k n).symm
  simp only [fusedSeriesMap, binomial, RingHom.comp_apply, hm]

private theorem iotaFused_constant (v : ℂ) :
    iotaFused ℂ (algebraMap (Bivariate ℂ) (Rational ℂ) (Polynomial.C (Polynomial.C v))) =
      HahnSeries.C (HahnSeries.C v) := by
  simp [iotaFused, fusedPoly, Polynomial.algEquivAevalXAddC_apply, polyXZ,
    Polynomial.algebraMap_hahnSeries_apply, Polynomial.map_C]

private theorem fused_x_factor :
    (HahnSeries.C (T ℂ) : XZ ℂ) * (1 + HahnSeries.single 1 (T ℂ)⁻¹) =
      HahnSeries.single 1 1 + HahnSeries.C (T ℂ) := by
  simp [mul_add, HahnSeries.C_apply, HahnSeries.single_mul_single,
    mul_inv_cancel₀ (T_ne_zero ℂ), add_comm]

private theorem homogeneous_monomial {F : Type*} [Field F] (v Z B U : F)
    (degree a b c j : ℕ) (hj : j ≤ degree) (hz : Z ≠ 0) (hb : B ≠ 0) :
    v * (Z * B) ^ (degree - j) * Z ^ j / ((Z * B) ^ c * Z ^ a * U ^ b) =
      U ^ (-(b : ℤ)) * Z ^ ((degree : ℤ) - a - c) *
        (v * B ^ ((degree : ℤ) - c - j)) := by
  rw [← zpow_natCast (Z * B) (degree - j), ← zpow_natCast Z j,
    ← zpow_natCast (Z * B) c, ← zpow_natCast Z a, ← zpow_natCast U b,
    div_eq_mul_inv, mul_inv_rev, mul_inv_rev, ← zpow_neg, ← zpow_neg, ← zpow_neg,
    mul_zpow, mul_zpow]
  calc
    _ = U ^ (-(b : ℤ)) *
        (Z ^ ((degree - j : ℕ) : ℤ) * Z ^ (j : ℤ) * Z ^ (-(a : ℤ)) * Z ^ (-(c : ℤ))) *
        (v * (B ^ ((degree - j : ℕ) : ℤ) * B ^ (-(c : ℤ)))) := by ring
    _ = _ := by
      rw [← zpow_add₀ hz, ← zpow_add₀ hz, ← zpow_add₀ hz, ← zpow_add₀ hb]
      rw [show ((degree - j : ℕ) : ℤ) + j + -(a : ℤ) + -(c : ℤ) =
          (degree : ℤ) - a - c by omega,
        show ((degree - j : ℕ) : ℤ) + -(c : ℤ) = (degree : ℤ) - c - j by omega]

private theorem fusedLaurent_factor (P : Polynomial ℂ) (degree M K L : ℕ) :
    let a : ℕ := (5 + K + L) / 2
    let b : ℕ := (6 + M + K) / 2
    let c : ℕ := (M + L + 7) / 2
    fusedLaurent P degree M K L =
      HahnSeries.single (-(b : ℤ)) 1 *
        HahnSeries.C ((T ℂ) ^ ((degree : ℤ) - a - c)) *
        fusedSeriesMap (fusedNumeratorSeries P degree c) := by
  intro a b c
  have hnum :
      swapRational (algebraMap (Bivariate ℂ) (Rational ℂ) (homogenizedNumerator P degree)) =
        ∑ j ∈ Finset.range (degree + 1),
          algebraMap (Bivariate ℂ) (Rational ℂ) (Polynomial.C (Polynomial.C (P.coeff j))) *
            z ℂ ^ (degree - j) * x ℂ ^ j := by
    rw [swapRational_algebraMap, homogenizedNumerator]
    simp only [map_sum, map_mul, map_pow, Polynomial.Bivariate.swap_C_C,
      Polynomial.Bivariate.swap_X, Polynomial.Bivariate.swap_Y, z, x]
  have hden :
      swapRational (algebraMap (Bivariate ℂ) (Rational ℂ) (denominator M K L)) =
        z ℂ ^ c * x ℂ ^ a * diagonal ℂ ^ b := by
    rw [swapRational_algebraMap, denominator]
    simp only [map_mul, map_pow, map_sub, Polynomial.Bivariate.swap_X,
      Polynomial.Bivariate.swap_Y, z, x, diagonal, a, b, c]
  rw [fusedLaurent, commonRational, map_div₀, hnum, hden, map_div₀]
  simp only [map_sum, map_mul, map_pow, iotaFused_constant, iotaFused_z, iotaFused_x,
    iotaFused_diagonal, fusedNumeratorSeries, Finset.sum_div, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjd : j ≤ degree := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hcast : (↑((degree : ℤ) - c - j) : ℂ) = (degree : ℂ) - c - j := by push_cast; rfl
  rw [← hcast, fusedSeriesMap_C, fusedSeriesMap_binomial]
  rw [← fused_x_factor]
  have hZpow : HahnSeries.C ((T ℂ) ^ ((degree : ℤ) - a - c)) =
      (HahnSeries.C (T ℂ) : XZ ℂ) ^ ((degree : ℤ) - a - c) :=
    map_zpow₀ (HahnSeries.C : LaurentSeries ℂ →+* XZ ℂ) (T ℂ) _
  rw [hZpow, RatFunc.single_zpow (-(b : ℤ))]
  exact homogeneous_monomial (F := XZ ℂ) _ _ _ _ degree a b c j hjd
    (by simp [T_ne_zero ℂ]) (one_add_single_ne_zero _ _)

/-- The coefficient of `t^(m-b)` is a single physical `z` monomial. -/
theorem fusedLaurent_coeff (P : Polynomial ℂ) (degree M K L m : ℕ) :
    let a : ℕ := (5 + K + L) / 2
    let b : ℕ := (6 + M + K) / 2
    let c : ℕ := (M + L + 7) / 2
    (fusedLaurent P degree M K L).coeff ((m : ℤ) - b) =
      HahnSeries.single ((degree : ℤ) - a - c - m)
        (PowerSeries.coeff m (fusedNumeratorSeries P degree c)) := by
  intro a b c
  rw [fusedLaurent_factor, mul_assoc, HahnSeries.coeff_single_mul, one_mul,
    sub_neg_eq_add, sub_add_cancel, HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul]
  simp only [fusedSeriesMap, RingHom.comp_apply, LaurentSeries.coeff_coe_powerSeries,
    PowerSeries.coeff_rescale, PowerSeries.coeff_map]
  rw [← mul_assoc, inv_pow, ← zpow_natCast (T ℂ) m, ← zpow_neg,
    ← zpow_add₀ (T_ne_zero ℂ), ← sub_eq_add_neg]
  rw [T, ← RatFunc.single_zpow, HahnSeries.C_apply, HahnSeries.single_mul_single]
  simp only [one_mul, add_zero, a, c]

/-- The diagonal pole bound rules out all outer exponents strictly below `-b`. -/
theorem fusedLaurent_coeff_below (P : Polynomial ℂ) (degree M K L : ℕ) (q : ℤ)
    (hq : q < -(((6 + M + K) / 2 : ℕ) : ℤ)) :
    (fusedLaurent P degree M K L).coeff q = 0 := by
  have h : q - (-(((6 + M + K) / 2 : ℕ) : ℤ)) < 0 := by omega
  rw [fusedLaurent_factor, mul_assoc, HahnSeries.coeff_single_mul, one_mul,
    HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul]
  simp only [fusedSeriesMap, RingHom.comp_apply, PowerSeries.coeff_coe, h, ↓reduceIte, mul_zero]

/-- The homogeneous degree turns the exponent of `1+s` into the normalized A exponent. -/
theorem fused_degree_sub_pole (M K L N : ℕ)
    (hM : (M : ℤ) % 2 = 0) (hK : (K : ℤ) % 2 = 0)
    (hL : (L : ℤ) % 2 = 1) (hN : (N : ℤ) % 2 = 1) :
    (((12 + M + K + L + N) / 2 : ℕ) : ℤ) - (((M + L + 7) / 2 : ℕ) : ℤ) =
      (((5 + K + L) / 2 : ℕ) : ℤ) + ((N : ℤ) - L) / 2 := by
  push_cast
  omega

private theorem fusedNumeratorSeries_eq_support (P : Polynomial ℂ) (degree c : ℕ)
    (hP : P.natDegree ≤ degree) :
    fusedNumeratorSeries P degree c =
      ∑ j ∈ P.support,
        PowerSeries.C (P.coeff j) * PowerSeries.binomialSeries ℂ ((degree : ℂ) - c - j) := by
  classical
  unfold fusedNumeratorSeries
  symm
  apply Finset.sum_subset
  · intro j hj
    exact Finset.mem_range.mpr ((Polynomial.le_natDegree_of_mem_supp j hj).trans_lt
      (Nat.lt_succ_of_le hP))
  · intro j _ hj
    rw [Polynomial.notMem_support_iff.mp hj, map_zero, zero_mul]

open ActualLeechHyperbolic (leechData)
open LatticeHalfFockChargedTensorCoefficients (ActualGround)
open NativeFixedPairAIterate (fixedAExponent fixedAIterateCoeff)
open NativeHHBBFormalChannels (hhbb_marked_formal_channels)
open NativeMixedUpperProductCusp (bSewnNumerator)
open NativeMixedWickChartTransport (MixedParity doubledOccupation)
open Orbifold.NativeOddTwistedIntertwiner (TwistedEven TwistedOdd leechUnit)
open OriginalFourMActualChart (Puncture)
open OriginalFourMVariableSupport (wordAt)
open OriginalGaussianSewnAnalytic (coefficient)

private theorem occupation_cast {ι : Type*} (slot : ι → Puncture) (n : ι → ℕ)
    (l : List ι) (i : Puncture) :
    ((doubledOccupation slot n l i).toNat : ℤ) = doubledOccupation slot n l i := by
  apply Int.toNat_of_nonneg
  classical
  unfold doubledOccupation
  apply List.sum_nonneg
  intro m hm
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hm
  split <;> omega

/-- For the canonical marked HHBB numerator, the fused rational coefficients are
the actual A iterate coefficients after the formal root-ratio normalization in
`s=(x-z)/z`. The A series uses the existing `fixedASlitSewn` convention at `-s`. -/
theorem hhbb_marked_fusedLaurent_coeff {ι : Type*} [Finite ι]
    (slot : ι → Puncture) (colour : ι → Fin leechData.rank) (n : ι → ℕ) (l : List ι)
    (hl : l.Nodup) (hpar : MixedParity slot n l)
    (u v : TwistedEven) (w bState : TwistedOdd) (p q r d : ActualGround leechData leechUnit)
    (hu : u.val = wordAt leechData slot colour n l .P ⊗ₜ[ℂ] p)
    (hv : v.val = wordAt leechData slot colour n l .Q ⊗ₜ[ℂ] q)
    (hw : w.val = wordAt leechData slot colour n l .R ⊗ₜ[ℂ] r)
    (hb : bState.val = wordAt leechData slot colour n l .S ⊗ₜ[ℂ] d) :
    let grade (i : Puncture) := (doubledOccupation slot n l i).toNat
    let V := wordAt leechData slot colour n l
    let M := grade .P
    let K := grade .Q
    let L := grade .R
    let N := grade .S
    let b : ℕ := (6 + M + K) / 2
    let degree : ℕ := (12 + M + K + L + N) / 2
    let GInf (y : ℂ) := Complex.I ^ ((L : ℤ) + N - K - 2 * (M : ℤ) - 3) *
      bSewnNumerator M L N (V .Q) (V .P) (V .R) (V .S) q p r d y
    let G (y : ℂ) := (y - 1) ^ b * GInf y
    let P : Polynomial ℂ := ∑ j ∈ Finset.range (degree + 1),
      Polynomial.C (coefficient j G) * Polynomial.X ^ (degree - j)
    let A (E : ℕ) := fixedAIterateCoeff false M K L N (fixedAExponent M K E)
      u v w.val bState.val
    ∀ m : ℕ, (fusedLaurent P degree M K L).coeff ((m : ℤ) - b) =
      HahnSeries.single (((N : ℤ) - L) / 2 - m)
        (PowerSeries.coeff m
          (PowerSeries.binomialSeries ℂ (-1 / 2 : ℂ) * PowerSeries.mk A)) := by
  intro grade V M K L N b degree GInf G P A m
  let a : ℕ := (5 + K + L) / 2
  let c : ℕ := (M + L + 7) / 2
  obtain ⟨hP, _, _, _, hA, _⟩ :=
    hhbb_marked_formal_channels slot colour n l hl hpar u v w bState p q r d hu hv hw hb
  have hgrade (i : Puncture) : (grade i : ℤ) = doubledOccupation slot n l i :=
    occupation_cast slot n l i
  have hM : (M : ℤ) % 2 = 0 := by simpa only [M, hgrade] using hpar.1
  have hK : (K : ℤ) % 2 = 0 := by simpa only [K, hgrade] using hpar.2.1
  have hL : (L : ℤ) % 2 = 1 := by simpa only [L, hgrade] using hpar.2.2.1
  have hN : (N : ℤ) % 2 = 1 := by simpa only [N, hgrade] using hpar.2.2.2
  have hDegree : (degree : ℤ) - c = (a : ℤ) + ((N : ℤ) - L) / 2 :=
    fused_degree_sub_pole M K L N hM hK hL hN
  have hWeight : (degree : ℤ) - a - c - m = ((N : ℤ) - L) / 2 - m := by omega
  have hCast : (degree : ℂ) - c = (↑((a : ℤ) + ((N : ℤ) - L) / 2) : ℂ) := by
    exact_mod_cast hDegree
  have hSeries :
      fusedNumeratorSeries P degree c =
        PowerSeries.binomialSeries ℂ (-1 / 2 : ℂ) * PowerSeries.mk A := by
    rw [fusedNumeratorSeries_eq_support P degree c hP, hCast]
    exact hA.symm
  change (fusedLaurent P degree M K L).coeff ((m : ℤ) - b) = _
  calc
    _ = HahnSeries.single ((degree : ℤ) - a - c - m)
        (PowerSeries.coeff m (fusedNumeratorSeries P degree c)) :=
      fusedLaurent_coeff P degree M K L m
    _ = _ := by rw [hWeight, hSeries]

end D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHHBBFormalFusedIota
