import D5.S3.VertexAlgebra.TwistedGround.FourPoint.HHBB.NativeHHBBModeResidue

/-! The algebraic Laurent expansions and weighted residues for the normalized BBHH
numerator. In the residue coordinates, the kernel variables `x,z` are physical `Z,X`. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeBBHHFormalAlgebra

open CollisionLaurentKernels.LaurentCollision
open CollisionRationalExpansions.PartialFractionCollision (Compatible)
open NativeHHBBTwoVariableRational (commonRational denominator homogenizedNumerator)
open NativeHHBBFormalProductIota (iotaXZ_commonRational_coeff iotaXZ_commonRational_coeff_of_lt)
open NativeHHBBFormalExchangedIota (paddedReverse_eq_reflect swap_homogenizedNumerator)
open NativeHHBBFormalInfinityExpansion (paddedReverse)
open NativeHHBBFormalFusedIota (swapRational fusedLaurent fusedLaurent_coeff
  fusedLaurent_coeff_below fusedNumeratorSeries)
open NativeHHBBModeResidue (modePairs weighted swapped_commonRational_weighted_collision
  coefficient_jacobi)
open private swapRational_algebraMap from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.HHBB.NativeHHBBFormalFusedIota
open private iotaZX_swapRational from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.HHBB.NativeHHBBActualThreeIota

local notation "xPoly" => (Polynomial.C (Polynomial.X : Polynomial ℂ))

/-- Padding the numerator by one zero coefficient raises its homogeneous degree by
multiplication by physical `X`. -/
theorem homogenizedNumerator_succ (p : Polynomial ℂ) (d : ℕ) (hp : p.natDegree ≤ d) :
    homogenizedNumerator p (d + 1) = xPoly * homogenizedNumerator p d := by
  rw [homogenizedNumerator, Finset.sum_range_succ,
    Polynomial.coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_of_le hp)]
  simp only [map_zero, zero_mul, add_zero, homogenizedNumerator, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjd : j ≤ d := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  rw [show d + 1 - j = (d - j) + 1 by omega, pow_succ]
  ac_rfl

/-- The rational expression in physical product coordinates `(X,Z)`. -/
def physicalRational (p : Polynomial ℂ) (d M H K : ℕ) : Rational ℂ :=
  algebraMap (Bivariate ℂ) (Rational ℂ) (homogenizedNumerator p d) /
    (x ℂ ^ ((5 + M + K) / 2) * z ℂ ^ ((5 + H + K) / 2) * (x ℂ - z ℂ) ^ ((6 + M + H) / 2))

/-- The same rational function in the coordinates of the weighted residue kernel. -/
def residueRational (p : Polynomial ℂ) (d M H K : ℕ) : Rational ℂ :=
  swapRational (physicalRational p d M H K)

/-- The added numerator factor cancels the extra HHBB pole even at `K = 0`. -/
theorem physicalRational_eq_commonRational (p : Polynomial ℂ) (d M H K : ℕ)
    (hp : p.natDegree ≤ d) :
    physicalRational p d M H K = commonRational p (d + 1) M H K := by
  have hc : (M + K + 7) / 2 = (5 + M + K) / 2 + 1 := by omega
  have hx : x ℂ ≠ 0 := by
    simpa only [x, map_zero] using
      (IsFractionRing.injective (Bivariate ℂ) (Rational ℂ)).ne
        (Polynomial.C_ne_zero.mpr (Polynomial.X_ne_zero (R := ℂ)))
  rw [commonRational, homogenizedNumerator_succ p d hp, denominator]
  simp only [map_mul, map_pow, map_sub]
  change physicalRational p d M H K =
    x ℂ * algebraMap (Bivariate ℂ) (Rational ℂ) (homogenizedNumerator p d) /
      (x ℂ ^ ((M + K + 7) / 2) * z ℂ ^ ((5 + H + K) / 2) * (x ℂ - z ℂ) ^ ((6 + M + H) / 2))
  rw [hc, pow_succ]
  rw [show x ℂ ^ ((5 + M + K) / 2) * x ℂ * z ℂ ^ ((5 + H + K) / 2) *
      (x ℂ - z ℂ) ^ ((6 + M + H) / 2) =
      x ℂ * (x ℂ ^ ((5 + M + K) / 2) * z ℂ ^ ((5 + H + K) / 2) *
      (x ℂ - z ℂ) ^ ((6 + M + H) / 2)) by ac_rfl]
  rw [mul_div_mul_left _ _ hx]
  rfl

/-- Polynomial numerator in the reversed product chart. The sign comes from
`(Z-X)^b` after exchanging the coordinates. -/
def exchangedNumerator (p : Polynomial ℂ) (d b : ℕ) : Polynomial ℂ :=
  Polynomial.C ((-1 : ℂ) ^ b) * paddedReverse d p

private theorem exchangedNumerator_natDegree_le (p : Polynomial ℂ) {d : ℕ} (b : ℕ)
    (hp : p.natDegree ≤ d) :
    (exchangedNumerator p d b).natDegree ≤ d := by
  unfold exchangedNumerator
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  rw [paddedReverse_eq_reflect p d hp]
  exact Polynomial.natDegree_reflect_le.trans (max_le le_rfl hp)

/-- Exchanging physical variables reverses the degree-`d` numerator and exchanges
the two physical pole orders. -/
theorem residueRational_eq_exchanged (p : Polynomial ℂ) (d M H K : ℕ)
    (hp : p.natDegree ≤ d) :
    residueRational p d M H K =
      physicalRational (exchangedNumerator p d ((6 + M + H) / 2)) d H M K := by
  let b := (6 + M + H) / 2
  have hb : (6 + H + M) / 2 = b := by dsimp [b]; omega
  have hScale (s : ℂ) :
      homogenizedNumerator (Polynomial.C s * paddedReverse d p) d =
        Polynomial.C (Polynomial.C s) * homogenizedNumerator (paddedReverse d p) d := by
    simp only [homogenizedNumerator, Polynomial.coeff_C_mul, map_mul, Finset.mul_sum, mul_assoc]
  have hx : swapRational (x ℂ) = z ℂ := by
    exact (swapRational_algebraMap _).trans (congrArg _ Polynomial.Bivariate.swap_X)
  have hz : swapRational (z ℂ) = x ℂ := by
    exact (swapRational_algebraMap _).trans (congrArg _ Polynomial.Bivariate.swap_Y)
  rw [residueRational, physicalRational, map_div₀, swapRational_algebraMap,
    swap_homogenizedNumerator p d hp]
  simp only [map_mul, map_pow, map_sub, hx, hz]
  rw [physicalRational, hb, exchangedNumerator, hScale]
  simp only [map_mul, map_pow, map_neg, map_one]
  change _ / (z ℂ ^ ((5 + M + K) / 2) * x ℂ ^ ((5 + H + K) / 2) *
    (z ℂ - x ℂ) ^ b) = _
  rw [show z ℂ - x ℂ = (-1 : Rational ℂ) * (x ℂ - z ℂ) by simp]
  rw [mul_pow, mul_comm (z ℂ ^ ((5 + M + K) / 2)), ← mul_assoc, mul_comm _ ((-1 : Rational ℂ) ^ b),
    mul_assoc]
  let s : Rational ℂ := (-1) ^ b
  have hs : s ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  have hs₂ : s * s = 1 := by dsimp [s]; rw [← mul_pow, neg_mul_neg, one_mul, one_pow]
  rw [← mul_div_mul_left _ _ hs, ← mul_assoc, hs₂, one_mul]

private theorem fusedNumeratorSeries_succ (p : Polynomial ℂ) (d c : ℕ)
    (hp : p.natDegree ≤ d) :
    fusedNumeratorSeries p (d + 1) (c + 1) = fusedNumeratorSeries p d c := by
  rw [fusedNumeratorSeries, Finset.sum_range_succ,
    Polynomial.coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_of_le hp)]
  simp only [map_zero, zero_mul, add_zero, fusedNumeratorSeries]
  apply Finset.sum_congr rfl
  intro j _
  rw [show ((d + 1 : ℕ) : ℂ) - ((c + 1 : ℕ) : ℂ) = (d : ℂ) - c by push_cast; ring]

/-- The two product and collision expansions, with their complete lower support
bounds. All three retain total physical degree `d-a-b-c`. -/
theorem three_iota_coefficients (p : Polynomial ℂ) (d M H K : ℕ) (hp : p.natDegree ≤ d) :
    let a : ℕ := (5 + H + K) / 2
    let b : ℕ := (6 + M + H) / 2
    let c : ℕ := (5 + M + K) / 2
    let w : ℤ := (d : ℤ) - a - b - c
    let F := residueRational p d M H K
    ((∀ m : ℕ, (iotaZX ℂ F).coeff ((m : ℤ) - a) =
      HahnSeries.single (w + a - m)
        (PowerSeries.coeff m (p.toPowerSeries * (PowerSeries.invOneSubPow ℂ b).val))) ∧
      (∀ i : ℤ, i < -(a : ℤ) → (iotaZX ℂ F).coeff i = 0)) ∧
    ((∀ m : ℕ, (iotaXZ ℂ F).coeff ((m : ℤ) - c) =
      HahnSeries.single (w + c - m)
        (PowerSeries.coeff m ((exchangedNumerator p d b).toPowerSeries *
          (PowerSeries.invOneSubPow ℂ b).val))) ∧
      (∀ i : ℤ, i < -(c : ℤ) → (iotaXZ ℂ F).coeff i = 0)) ∧
    ((∀ m : ℕ, (iotaFused ℂ F).coeff ((m : ℤ) - b) =
      HahnSeries.single (w + b - m) (PowerSeries.coeff m (fusedNumeratorSeries p d c))) ∧
      (∀ i : ℤ, i < -(b : ℤ) → (iotaFused ℂ F).coeff i = 0)) := by
  intro a b c w F
  have hB : iotaZX ℂ F = iotaXZ ℂ (commonRational p (d + 1) M H K) := by
    change iotaZX ℂ (residueRational p d M H K) = _
    rw [residueRational, iotaZX_swapRational, physicalRational_eq_commonRational p d M H K hp]
  let Q := exchangedNumerator p d b
  have hQ := exchangedNumerator_natDegree_le p b hp
  have hD : iotaXZ ℂ F = iotaXZ ℂ (commonRational Q (d + 1) H M K) := by
    change iotaXZ ℂ (residueRational p d M H K) = _
    rw [residueRational_eq_exchanged p d M H K hp,
      physicalRational_eq_commonRational Q d H M K hQ]
  have hA : iotaFused ℂ F = fusedLaurent p (d + 1) M H K := by
    change iotaFused ℂ (residueRational p d M H K) = _
    rw [residueRational, physicalRational_eq_commonRational p d M H K hp, fusedLaurent]
  have hb : (6 + H + M) / 2 = b := by dsimp [b]; omega
  have hc' : (M + K + 7) / 2 = c + 1 := by dsimp [c]; omega
  have ha' : (H + K + 7) / 2 = a + 1 := by dsimp [a]; omega
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro m
    rw [hB]
    have h := iotaXZ_commonRational_coeff p (d + 1) M H K (hp.trans (Nat.le_succ d)) m
    dsimp only at h
    rw [hc'] at h
    have he : ((d + 1 : ℕ) : ℤ) - ((c + 1 : ℕ) : ℤ) - b - m = w + a - m := by
      dsimp [w]; omega
    simpa only [← he] using h
  · intro i hi
    rw [hB]
    exact iotaXZ_commonRational_coeff_of_lt p (d + 1) M H K (hp.trans (Nat.le_succ d)) i hi
  · intro m
    rw [hD]
    have h := iotaXZ_commonRational_coeff Q (d + 1) H M K (hQ.trans (Nat.le_succ d)) m
    dsimp only at h
    rw [hb, ha'] at h
    have he : ((d + 1 : ℕ) : ℤ) - ((a + 1 : ℕ) : ℤ) - b - m = w + c - m := by
      dsimp [w]; omega
    simpa only [← he] using h
  · intro i hi
    rw [hD]
    exact iotaXZ_commonRational_coeff_of_lt Q (d + 1) H M K (hQ.trans (Nat.le_succ d)) i hi
  · intro m
    rw [hA]
    have h := fusedLaurent_coeff p (d + 1) M H K m
    dsimp only at h
    rw [hc', fusedNumeratorSeries_succ p d c hp] at h
    have he : ((d + 1 : ℕ) : ℤ) - a - ((c + 1 : ℕ) : ℤ) - m = w + b - m := by
      dsimp [w]; omega
    simpa only [← he] using h
  · intro i hi
    rw [hA]
    exact fusedLaurent_coeff_below p (d + 1) M H K i hi

/-- Compatibility holds for every Laurent test monomial in the physical
diagonal orientation `X-Z`. -/
theorem weighted_collision (p : Polynomial ℂ) (d M H K : ℕ) (hp : p.natDegree ≤ d)
    (q r s : ℤ) :
    Compatible ℂ (weighted (residueRational p d M H K) q r s) := by
  rw [residueRational, physicalRational_eq_commonRational p d M H K hp]
  exact swapped_commonRational_weighted_collision p (d + 1) M H K
    (hp.trans (Nat.le_succ d)) q r s

open Orbifold.NativeOddTwistedIntertwiner (TwistedOdd TwistedEven)
open NativeFixedPairAIterate (fixedAExponent fixedAIterateCoeff)
open NativeMixedUpperProductCusp (bProductCoeff)
open OriginalGaussianSewnAnalytic (coefficient)

/-- The degree used in the finite reversed Taylor readout of the BBHH germ. -/
def numeratorDegree (M K H J : ℕ) : ℕ :=
  let a : ℕ := (5 + H + K) / 2
  let b : ℕ := (M + H + 6) / 2
  ((a : ℤ) + b + (1 + (J : ℤ) - H) / 2).toNat

/-- The polynomial numerator of the committed normalized BBHH germ. -/
def numerator (M K H J : ℕ) (P R : TwistedOdd) (Q S : TwistedEven) : Polynomial ℂ :=
  let d := numeratorDegree M K H J
  let b : ℕ := (M + H + 6) / 2
  let G (t : ℂ) := (t - 1) ^ b * (-(∑' m : ℕ, bProductCoeff true true H M K J P Q R S m * t ^ m))
  ∑ n ∈ Finset.range (d + 1), Polynomial.C (coefficient n G) * Polynomial.X ^ (d - n)

/-- The finite reversed Taylor readout has the degree used to homogenize it. -/
theorem numerator_natDegree_le (M K H J : ℕ) (P R : TwistedOdd) (Q S : TwistedEven) :
    (numerator M K H J P R Q S).natDegree ≤ numeratorDegree M K H J := by
  unfold numerator
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro n _
  exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (Nat.sub_le ..)

/-- The geometric degree and the three Laurent exponents agree with the BBHH
doubled grades. In particular the collision unit has exponent
`w + b - (J-K+1)/2 = 1/2`. -/
theorem cusp_exponents (M K H J : ℕ)
    (hM : M % 2 = 1) (hK : K % 2 = 0) (hH : H % 2 = 1) (hJ : J % 2 = 0) :
    let a : ℕ := (5 + H + K) / 2
    let b : ℕ := (6 + M + H) / 2
    let c : ℕ := (5 + M + K) / 2
    let w : ℤ := ((J : ℤ) - M - H - K - 4) / 2
    (numeratorDegree M K H J : ℤ) = w + a + b + c ∧
      w + a = (1 + (J : ℤ) - M) / 2 ∧
      w + c = (1 + (J : ℤ) - H) / 2 ∧
      (w : ℂ) + b - ((J : ℂ) - K + 1) / 2 = 1 / 2 := by
  intro a b c w
  have ha : (a : ℤ) = (5 + (H : ℤ) + K) / 2 := by
    simp only [a, Int.natCast_ediv, Int.natCast_add, Nat.cast_ofNat]
  have hb : (b : ℤ) = (6 + (M : ℤ) + H) / 2 := by
    simp only [b, Int.natCast_ediv, Int.natCast_add, Nat.cast_ofNat]
  have hc : (c : ℤ) = (5 + (M : ℤ) + K) / 2 := by
    simp only [c, Int.natCast_ediv, Int.natCast_add, Nat.cast_ofNat]
  have hd : (numeratorDegree M K H J : ℤ) = (a : ℤ) + b + (1 + (J : ℤ) - H) / 2 := by
    unfold numeratorDegree
    rw [show (M + H + 6) / 2 = b by dsimp [b]; omega]
    apply Int.toNat_of_nonneg
    change 0 ≤ (a : ℤ) + b + (1 + (J : ℤ) - H) / 2
    omega
  have hcollision : 2 * (w + b) = (J : ℤ) - K + 2 := by dsimp only [w]; omega
  have hcollisionC := congrArg (fun n : ℤ => (n : ℂ)) hcollision
  push_cast at hcollisionC
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp only [w] at *
    omega
  · dsimp only [w]; omega
  · dsimp only [w]; omega
  · linear_combination (1 / 2 : ℂ) * hcollisionC

/-- Weighted scalar BBHH mode relation from the three formal cusp identities.
The zero and infinity series carry the negative native product scalars. In
the collision chart the positive native iterate is multiplied by the
binomial unit for `(1+s)^(1/2)`, with `s = (X-Z)/Z`. -/
theorem coefficient_jacobi_of_cusp_series (M K H J : ℕ)
    (P R : TwistedOdd) (Q S : TwistedEven)
    (hM : M % 2 = 1) (hK : K % 2 = 0) (hH : H % 2 = 1) (hJ : J % 2 = 0)
    (q p r : ℤ) :
    let a : ℕ := (5 + H + K) / 2
    let b : ℕ := (6 + M + H) / 2
    let c : ℕ := (5 + M + K) / 2
    let w : ℤ := ((J : ℤ) - M - H - K - 4) / 2
    let d := numeratorDegree M K H J
    let N := numerator M K H J P R Q S
    let B := bProductCoeff true true M H K J R Q P S
    let D := bProductCoeff true true H M K J P Q R S
    let A (m : ℕ) := fixedAIterateCoeff true M H K J (fixedAExponent M H m) P R Q.val S.val
    let C := PowerSeries.binomialSeries ℂ (1 / 2 : ℂ) * PowerSeries.mk A
    N.toPowerSeries * (PowerSeries.invOneSubPow ℂ b).val =
      PowerSeries.mk (fun m => -B m) →
    (exchangedNumerator N d b).toPowerSeries * (PowerSeries.invOneSubPow ℂ b).val =
      PowerSeries.mk (fun m => -D m) →
    fusedNumeratorSeries N d c = C →
    (∑ ij ∈ modePairs (w + a + q + r + 1),
      (-1 : ℂ) ^ ij.2 * ((Ring.choose r ij.2 : ℤ) : ℂ) * (-B ij.1)) -
    (∑ ij ∈ modePairs ((c : ℤ) - q - 1),
      (-1 : ℂ) ^ (r + (ij.2 : ℤ)) * ((Ring.choose r ij.2 : ℤ) : ℂ) * (-D ij.1)) =
    ∑ ij ∈ modePairs ((b : ℤ) - r - 1),
      ((Ring.choose q ij.2 : ℤ) : ℂ) * PowerSeries.coeff ij.1 C := by
  intro a b c w d N B D A C hB hD hA
  have hN : N.natDegree ≤ d := numerator_natDegree_le M K H J P R Q S
  have hw : (d : ℤ) - a - b - c = w := by
    have hd := (cusp_exponents M K H J hM hK hH hJ).1
    change (d : ℤ) = w + a + b + c at hd
    omega
  obtain ⟨⟨hBc, hB0⟩, ⟨hDc, hD0⟩, ⟨hAc, hA0⟩⟩ := three_iota_coefficients N d M H K hN
  rw [hw, hB] at hBc
  rw [hw, hD] at hDc
  rw [hw, hA] at hAc
  simp only [PowerSeries.coeff_mk] at hBc hDc
  exact coefficient_jacobi (residueRational N d M H K) B (fun m => -D m)
    (fun m => PowerSeries.coeff m C) a b c w q p r
    hBc hB0 hDc hD0 hAc hA0 (weighted_collision N d M H K hN q p r)

end D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeBBHHFormalAlgebra
