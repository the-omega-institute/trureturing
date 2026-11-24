import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHHBBWeightedResidue
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHHBBActualThreeIota

/-! Finite coefficient Jacobi for the normalized marked HHBB channels. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHHBBModeResidue

open scoped BigOperators LaurentSeries PowerSeries TensorProduct
open CollisionLaurentKernels.LaurentCollision
open CollisionLaurentKernels.PolynomialCollision (iotaZX_x iotaXZ_x iotaFused_x)
open CollisionRationalExpansions.PartialFractionCollision (Compatible)
open HahnSeries (single)

local notation "Series" => LaurentSeries (LaurentSeries ℂ)

/-- Sum over natural pairs with integer sum (n). A negative target has no pairs. -/
def modePairs (n : ℤ) : Finset (ℕ × ℕ) :=
  (Finset.HasAntidiagonal.antidiagonal n.toNat).filter fun _ => 0 ≤ n

@[simp] theorem mem_modePairs {n : ℤ} {ij : ℕ × ℕ} :
    ij ∈ modePairs n ↔ (ij.1 : ℤ) + ij.2 = n := by
  simp only [modePairs, Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal]
  omega

private theorem coeff_mul_modes (F G : Series) (a w d h s : ℤ) (U V : ℕ → ℂ)
    (hF : ∀ m : ℕ, F.coeff ((m : ℤ) - a) = single (w + a - m) (U m))
    (hF0 : ∀ k : ℤ, k < -a → F.coeff k = 0)
    (hG : ∀ j : ℕ, G.coeff j = single (d - j) (V j))
    (hG0 : ∀ k : ℤ, k < 0 → G.coeff k = 0) :
    ((F * G).coeff h).coeff s =
      if s = w + d - h then ∑ ij ∈ modePairs (h + a), U ij.1 * V ij.2 else 0 := by
  classical
  let f : ℕ × ℕ ↪ ℤ × ℤ :=
    ⟨fun ij => ((ij.1 : ℤ) - a, (ij.2 : ℤ)), by
      rintro ⟨m, j⟩ ⟨m', j'⟩ he
      have hm := congrArg Prod.fst he
      have hj := congrArg Prod.snd he
      simp only at hm hj
      congr <;> omega⟩
  have hsubset :
      Finset.antidiagonal F.isPWO_support G.isPWO_support h ⊆ (modePairs (h + a)).map f := by
    intro ij hij
    rcases Finset.mem_antidiagonal.mp hij with ⟨hFne, hGne, hsum⟩
    have hleft : -a ≤ ij.1 := by
      by_contra! hk
      rw [HahnSeries.mem_support, hF0 _ hk] at hFne
      exact hFne rfl
    have hright : 0 ≤ ij.2 := by
      by_contra! hk
      rw [HahnSeries.mem_support, hG0 _ hk] at hGne
      exact hGne rfl
    apply Finset.mem_map.mpr
    refine ⟨((ij.1 + a).toNat, ij.2.toNat), mem_modePairs.mpr (by dsimp; omega), ?_⟩
    change (((((ij.1 + a).toNat : ℕ) : ℤ) - a), (ij.2.toNat : ℤ)) = ij
    apply Prod.ext <;> dsimp <;> omega
  have hcoeff : (F * G).coeff h =
      ∑ ij ∈ modePairs (h + a), F.coeff (f ij).1 * G.coeff (f ij).2 := by
    rw [HahnSeries.coeff_mul, ← Finset.sum_map (modePairs (h + a)) f
      (fun uv => F.coeff uv.1 * G.coeff uv.2)]
    refine Finset.sum_subset hsubset ?_
    intro ij hij hnot
    obtain ⟨uv, huv, rfl⟩ := Finset.mem_map.mp hij
    have he := mem_modePairs.mp huv
    have hadd : (f uv).1 + (f uv).2 = h := by
      change (uv.1 : ℤ) - a + (uv.2 : ℤ) = h
      omega
    rw [Finset.mem_antidiagonal] at hnot
    simp only [HahnSeries.mem_support, hadd, and_true, not_and, not_not] at hnot
    by_cases hf : F.coeff (f uv).1 = 0
    · rw [hf, zero_mul]
    · rw [hnot hf, mul_zero]
  rw [hcoeff]
  change (HahnSeries.coeff.addMonoidHom (R := ℂ) s) (∑ ij ∈ modePairs (h + a), _) = _
  simp only [map_sum, HahnSeries.coeff.addMonoidHom_apply]
  by_cases hs : s = w + d - h
  · rw [ite_eq_left hs]
    apply Finset.sum_congr rfl
    intro ij hij
    have he := mem_modePairs.mp hij
    have hexp : w + a - (ij.1 : ℤ) + (d - (ij.2 : ℤ)) = s := by omega
    change (F.coeff ((ij.1 : ℤ) - a) * G.coeff (ij.2 : ℤ)).coeff s = _
    rw [hF, hG, HahnSeries.single_mul_single, hexp, HahnSeries.coeff_single_same]
  · rw [ite_eq_right hs]
    apply Finset.sum_eq_zero
    intro ij hij
    have he := mem_modePairs.mp hij
    have hexp : s ≠ w + a - (ij.1 : ℤ) + (d - (ij.2 : ℤ)) := by omega
    change (F.coeff ((ij.1 : ℤ) - a) * G.coeff (ij.2 : ℤ)).coeff s = _
    rw [hF, hG, HahnSeries.single_mul_single, HahnSeries.coeff_single_of_ne hexp]

private def binomialWeight (epsilon sign : ℂ) (k d : ℤ) : Series :=
  HahnSeries.C (single d sign) *
    binomial (LaurentSeries ℂ) (single (-1) epsilon) k

private theorem binomialWeight_coeff (epsilon sign : ℂ) (k d : ℤ) (j : ℕ) :
    (binomialWeight epsilon sign k d).coeff j =
      single (d - j) (sign * (epsilon ^ j * ((Ring.choose k j : ℤ) : ℂ))) := by
  rw [binomialWeight, HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul,
    binomial, LaurentSeries.coeff_coe_powerSeries]
  simp only [PowerSeries.coeff_rescale, PowerSeries.binomialSeries_coeff, zsmul_eq_mul, mul_one,
    HahnSeries.single_pow]
  rw [← map_intCast (HahnSeries.C : ℂ →+* LaurentSeries ℂ), HahnSeries.C_apply,
    HahnSeries.single_mul_single, HahnSeries.single_mul_single]
  congr 1
  simp [sub_eq_add_neg]

private theorem binomialWeight_coeff_neg (epsilon sign : ℂ) (k d h : ℤ) (hh : h < 0) :
    (binomialWeight epsilon sign k d).coeff h = 0 := by
  rw [binomialWeight, HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul]
  simp [binomial, PowerSeries.coeff_coe, hh]

private theorem T_zpow (i : ℤ) : T ℂ ^ i = single i 1 := (RatFunc.single_zpow i).symm

private theorem T_inv : (T ℂ)⁻¹ = single (-1) 1 := by
  rw [← zpow_neg_one, T_zpow]

private theorem T_neg_inv : -(T ℂ)⁻¹ = single (-1) (-1) := by
  rw [T_inv, HahnSeries.single_neg]

/-- The collision variables `x,z` are physical `Z,X`, respectively.
The weight is `X^q Z^p (X-Z)^r` for arbitrary integers `q,p,r`. -/
def weighted (R : Rational ℂ) (q p r : ℤ) : Rational ℂ :=
  x ℂ ^ p * z ℂ ^ q * diagonal ℂ ^ r * R

private theorem weight_ZX (q p r : ℤ) :
    iotaZX ℂ (x ℂ ^ p * z ℂ ^ q * diagonal ℂ ^ r) =
      single p 1 * binomialWeight (-1) 1 r (q + r) := by
  simp only [map_mul, map_zpow₀, iotaZX_x, iotaZX_z, iotaZX_diagonal, ← RatFunc.single_zpow]
  rw [← kernelZX_zpow, kernelZX, ← map_zpow₀]
  simp only [mul_assoc]
  congr 1
  rw [← mul_assoc, ← map_mul,
    ← zpow_add₀ (T_ne_zero ℂ), T_zpow, T_neg_inv, binomialWeight]

private theorem weight_XZ (q p r : ℤ) :
    iotaXZ ℂ (x ℂ ^ p * z ℂ ^ q * diagonal ℂ ^ r) =
      single q 1 * binomialWeight (-1) ((-1 : ℂ) ^ r) r (p + r) := by
  simp only [map_mul, map_zpow₀, iotaXZ_x, iotaXZ_z, iotaXZ_diagonal, ← RatFunc.single_zpow]
  rw [mul_comm _ (single q 1), ← kernelXZ_zpow, kernelXZ, ← map_zpow₀]
  simp only [mul_assoc]
  congr 1
  rw [← mul_assoc, ← map_mul, show -T ℂ = HahnSeries.C (-1 : ℂ) * T ℂ by simp,
    mul_zpow, ← map_zpow₀, mul_left_comm, ← zpow_add₀ (T_ne_zero ℂ), T_zpow,
    T_neg_inv, binomialWeight]
  congr 2
  rw [HahnSeries.C_apply, HahnSeries.single_mul_single, zero_add, mul_one]

private theorem weight_fused (q p r : ℤ) :
    iotaFused ℂ (x ℂ ^ p * z ℂ ^ q * diagonal ℂ ^ r) =
      single r 1 * binomialWeight 1 1 q (p + q) := by
  have hf : (single (1 : ℤ) 1 + HahnSeries.C (T ℂ) : Series) =
      HahnSeries.C (T ℂ) * (1 + single 1 (T ℂ)⁻¹) := by
    simp [mul_add, HahnSeries.C_apply, HahnSeries.single_mul_single,
      mul_inv_cancel₀ (T_ne_zero ℂ), add_comm]
  simp only [map_mul, map_zpow₀, iotaFused_x, iotaFused_z, iotaFused_diagonal,
    ← RatFunc.single_zpow]
  rw [hf, mul_zpow, ← binomial_zpow, mul_comm _ (single r 1), ← map_zpow₀,
    ← map_zpow₀, ← mul_assoc (HahnSeries.C _), ← map_mul, ← zpow_add₀ (T_ne_zero ℂ),
    T_zpow, T_inv, binomialWeight]

private theorem coeff_weighted (F : Series) (epsilon sign : ℂ) (k d o a w h s : ℤ)
    (U : ℕ → ℂ)
    (hF : ∀ m : ℕ, F.coeff ((m : ℤ) - a) = single (w + a - m) (U m))
    (hF0 : ∀ i : ℤ, i < -a → F.coeff i = 0) :
    ((((single o 1 : Series) * binomialWeight epsilon sign k d) * F).coeff h).coeff s =
      if s = w + d - (h - o) then
        ∑ ij ∈ modePairs (h - o + a),
          U ij.1 * (sign * (epsilon ^ ij.2 * ((Ring.choose k ij.2 : ℤ) : ℂ)))
      else 0 := by
  have hmul : ((single o 1 : Series) * binomialWeight epsilon sign k d) * F =
      (single o 1 : Series) * (binomialWeight epsilon sign k d * F) :=
    @mul_assoc Series _ (single o 1) (binomialWeight epsilon sign k d) F
  rw [hmul, HahnSeries.coeff_single_mul, one_mul,
    @mul_comm Series _ (binomialWeight epsilon sign k d) F]
  exact coeff_mul_modes _ _ a w d (h - o) s U _
    hF hF0 (binomialWeight_coeff epsilon sign k d) (binomialWeight_coeff_neg epsilon sign k d)

/-- The B expansion has outer physical `z` and inner physical `x`. -/
theorem weighted_b_coeff (R : Rational ℂ) (B : ℕ → ℂ) (a w q p r h : ℤ)
    (hB : ∀ m : ℕ, (iotaZX ℂ R).coeff ((m : ℤ) - a) = single (w + a - m) (-B m))
    (hB0 : ∀ i : ℤ, i < -a → (iotaZX ℂ R).coeff i = 0) :
    ((iotaZX ℂ (weighted R q p r)).coeff h).coeff (w + q + p + r - h) =
      ∑ ij ∈ modePairs (h - p + a),
        (-1 : ℂ) ^ ij.2 * ((Ring.choose r ij.2 : ℤ) : ℂ) * (-B ij.1) := by
  rw [weighted, map_mul, weight_ZX, coeff_weighted _ _ _ _ _ _ a w _ _ _ hB hB0,
    ite_eq_left (by omega)]
  apply Finset.sum_congr rfl
  intro ij _
  simp only [one_mul]
  ring

/-- The D expansion has outer physical `x` and inner physical `z`. -/
theorem weighted_d_coeff (R : Rational ℂ) (D : ℕ → ℂ) (c w q p r h : ℤ)
    (hD : ∀ m : ℕ, (iotaXZ ℂ R).coeff ((m : ℤ) - c) = single (w + c - m) (D m))
    (hD0 : ∀ i : ℤ, i < -c → (iotaXZ ℂ R).coeff i = 0) :
    ((iotaXZ ℂ (weighted R q p r)).coeff h).coeff (w + q + p + r - h) =
      ∑ ij ∈ modePairs (h - q + c),
        (-1 : ℂ) ^ (r + (ij.2 : ℤ)) * ((Ring.choose r ij.2 : ℤ) : ℂ) * D ij.1 := by
  rw [weighted, map_mul, weight_XZ, coeff_weighted _ _ _ _ _ _ c w _ _ _ hD hD0,
    ite_eq_left (by omega)]
  apply Finset.sum_congr rfl
  intro ij _
  rw [zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_natCast]
  ring

/-- The fused expansion has outer `t=x-z` and inner physical `z`. -/
theorem weighted_a_coeff (R : Rational ℂ) (C : ℕ → ℂ) (b w q p r h : ℤ)
    (hA : ∀ m : ℕ, (iotaFused ℂ R).coeff ((m : ℤ) - b) = single (w + b - m) (C m))
    (hA0 : ∀ i : ℤ, i < -b → (iotaFused ℂ R).coeff i = 0) :
    ((iotaFused ℂ (weighted R q p r)).coeff h).coeff (w + q + p + r - h) =
      ∑ ij ∈ modePairs (h - r + b), ((Ring.choose q ij.2 : ℤ) : ℂ) * C ij.1 := by
  rw [weighted, map_mul, weight_fused, coeff_weighted _ _ _ _ _ _ b w _ _ _ hA hA0,
    ite_eq_left (by omega)]
  apply Finset.sum_congr rfl
  intro ij _
  simp only [one_pow, one_mul, mul_comm]

/-- The collision identity takes the physical `x` residue in both products.
In B this is an inner residue, so its outer index is the spectator index. -/
theorem coefficient_jacobi (R : Rational ℂ) (B D C : ℕ → ℂ) (a b c w q p r : ℤ)
    (hB : ∀ m : ℕ, (iotaZX ℂ R).coeff ((m : ℤ) - a) = single (w + a - m) (-B m))
    (hB0 : ∀ i : ℤ, i < -a → (iotaZX ℂ R).coeff i = 0)
    (hD : ∀ m : ℕ, (iotaXZ ℂ R).coeff ((m : ℤ) - c) = single (w + c - m) (D m))
    (hD0 : ∀ i : ℤ, i < -c → (iotaXZ ℂ R).coeff i = 0)
    (hA : ∀ m : ℕ, (iotaFused ℂ R).coeff ((m : ℤ) - b) = single (w + b - m) (C m))
    (hA0 : ∀ i : ℤ, i < -b → (iotaFused ℂ R).coeff i = 0)
    (hcol : Compatible ℂ (weighted R q p r)) :
    (∑ ij ∈ modePairs (w + a + q + r + 1),
      (-1 : ℂ) ^ ij.2 * ((Ring.choose r ij.2 : ℤ) : ℂ) * (-B ij.1)) -
    (∑ ij ∈ modePairs (c - q - 1),
      (-1 : ℂ) ^ (r + (ij.2 : ℤ)) * ((Ring.choose r ij.2 : ℤ) : ℂ) * D ij.1) =
    ∑ ij ∈ modePairs (b - r - 1), ((Ring.choose q ij.2 : ℤ) : ℂ) * C ij.1 := by
  let s := w + q + p + r + 1
  have hc := congrArg (fun F : LaurentSeries ℂ => F.coeff s) hcol
  simp only [HahnSeries.coeff_sub, coeff_resZ_ZX, coeffZX, resZ_XZ] at hc
  have h1 : w + q + p + r - s = -1 := by dsimp [s]; omega
  have h2 : w + q + p + r - (-1) = s := by dsimp [s]; omega
  have h3 : s - p + a = w + a + q + r + 1 := by dsimp [s]; omega
  have h4 : -1 - q + c = c - q - 1 := by omega
  have h5 : -1 - r + b = b - r - 1 := by omega
  rw [← h1, weighted_b_coeff R B a w q p r s hB hB0, h3] at hc
  have hd := weighted_d_coeff R D c w q p r (-1) hD hD0
  have ha := weighted_a_coeff R C b w q p r (-1) hA hA0
  rw [h2, h4] at hd
  rw [h2, h5] at ha
  rwa [h1, hd, ha] at hc

open NativeHHBBWeightedResidue (commonRational_weighted_collision)
open NativeHHBBTwoVariableRational (commonRational denominator homogenizedNumerator)
open NativeHHBBActualThreeIota (hhbb_marked_three_iota_coefficients)
open NativeHHBBFormalFusedIota (swapRational)
open NativeHHBBFormalExchangedIota (swap_commonRational)
open NativeHHBBFormalInfinityExpansion (paddedReverse)

private theorem swap_eq_ringEquiv :
    swapRational = (IsFractionRing.ringEquivOfRingEquiv
      (K := Rational ℂ) (L := Rational ℂ)
      (Polynomial.Bivariate.swap (R := ℂ)).toRingEquiv).toRingHom := by
  apply IsFractionRing.ringHom_ext (A := Bivariate ℂ)
  intro f
  rw [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
    IsFractionRing.ringEquivOfRingEquiv_algebraMap, swapRational,
    IsFractionRing.lift_algebraMap]
  rfl

set_option maxHeartbeats 2000000 in
/-- Apply the weighted residue theorem after swapping the two physical variables. -/
theorem swapped_commonRational_weighted_collision (P : Polynomial ℂ) (d M K L : ℕ)
    (hP : P.natDegree ≤ d) (q p r : ℤ) :
    Compatible ℂ (weighted (swapRational (commonRational P d M K L)) q p r) := by
  let a : ℕ := (5 + K + L) / 2
  let b : ℕ := (6 + M + K) / 2
  let c : ℕ := (M + L + 7) / 2
  let Q := Polynomial.C ((-1 : ℂ) ^ b) * paddedReverse d P
  let num := algebraMap (Bivariate ℂ) (Rational ℂ) (homogenizedNumerator Q d)
  let delta := x ℂ - z ℂ
  have hx : x ℂ ≠ 0 := by
    simpa only [x, map_zero] using
      (IsFractionRing.injective (Bivariate ℂ) (Rational ℂ)).ne
        (Polynomial.C_ne_zero.mpr Polynomial.X_ne_zero)
  have hz : z ℂ ≠ 0 := by
    simpa only [z, map_zero] using
      (IsFractionRing.injective (Bivariate ℂ) (Rational ℂ)).ne Polynomial.X_ne_zero
  have hδ : delta ≠ 0 := by
    intro h
    have hzero : diagonal ℂ = 0 := sub_eq_zero.mpr (sub_eq_zero.mp h).symm
    have hi := congrArg (iotaFused ℂ) hzero
    simp only [iotaFused_diagonal, map_zero, HahnSeries.single_eq_zero_iff, one_ne_zero] at hi
  have ha : (K + L + 7) / 2 = a + 1 := by dsimp [a]; omega
  have hb : (6 + K + M) / 2 = b := by dsimp [b]; omega
  have hc : (5 + M + L) / 2 = c - 1 := by dsimp [c]; omega
  have hc' : 0 < c := by dsimp [c]; omega
  have hswap : swapRational (commonRational P d M K L) =
      (x ℂ * (z ℂ)⁻¹) * commonRational Q d K M L := by
    have hSw : swapRational (commonRational P d M K L) =
        num / (x ℂ ^ a * z ℂ ^ c * delta ^ b) := by
      rw [swap_eq_ringEquiv, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
      exact swap_commonRational P d M K L hP
    have hCommon : commonRational Q d K M L =
        num / (x ℂ ^ ((K + L + 7) / 2) * z ℂ ^ ((5 + M + L) / 2) *
          delta ^ ((6 + K + M) / 2)) := by
      simp only [commonRational, denominator, map_mul, map_pow, map_sub]
      rfl
    rw [hSw, hCommon, ha, hb, hc, pow_succ, show z ℂ ^ c = z ℂ ^ (c - 1) * z ℂ by
      rw [← pow_succ, Nat.sub_add_cancel hc']]
    field_simp
  have hweight : weighted (swapRational (commonRational P d M K L)) q p r =
      x ℂ ^ (p + 1) * z ℂ ^ (q - 1) * (x ℂ - z ℂ) ^ r *
        commonRational (Polynomial.C ((-1 : ℂ) ^ b * (-1 : ℂ) ^ r) * paddedReverse d P) d K M L := by
    rw [weighted, hswap, zpow_add_one₀ hx, zpow_sub₀ hz, zpow_one, div_eq_mul_inv]
    have hdiag : diagonal ℂ ^ r = (-1 : Rational ℂ) ^ r * delta ^ r := by
      rw [show diagonal ℂ = (-1 : Rational ℂ) * delta by simp [delta, diagonal], mul_zpow]
    rw [hdiag]
    have hC (k : ℂ) :
        commonRational (Polynomial.C k * Q) d K M L =
          (algebraMap (Bivariate ℂ) (Rational ℂ) (Polynomial.C (Polynomial.C k))) *
            commonRational Q d K M L := by
      have hNum : homogenizedNumerator (Polynomial.C k * Q) d =
          Polynomial.C (Polynomial.C k) * homogenizedNumerator Q d := by
        simp only [homogenizedNumerator, Polynomial.coeff_C_mul, map_mul,
          Finset.mul_sum, mul_assoc]
      simp only [commonRational, hNum, map_mul, mul_div_assoc]
    have hsign : (algebraMap (Bivariate ℂ) (Rational ℂ)
        (Polynomial.C (Polynomial.C ((-1 : ℂ) ^ r)))) = (-1 : Rational ℂ) ^ r := by
      let f : ℂ →+* Rational ℂ := (algebraMap (Bivariate ℂ) (Rational ℂ)).comp
        (Polynomial.C.comp (Polynomial.C : ℂ →+* Polynomial ℂ))
      change f ((-1 : ℂ) ^ r) = _
      rw [map_zpow₀, map_neg, map_one]
    have hPoly : Polynomial.C ((-1 : ℂ) ^ b * (-1 : ℂ) ^ r) * paddedReverse d P =
        Polynomial.C ((-1 : ℂ) ^ r) * Q := by
      dsimp only [Q]
      rw [mul_comm ((-1 : ℂ) ^ b), map_mul, mul_assoc]
    rw [hPoly, hC, hsign]
    change _ = _ * delta ^ r * _
    ring
  rw [hweight]
  exact commonRational_weighted_collision _ d K M L (p + 1) (q - 1) r

open ActualLeechHyperbolic (leechData)
open LatticeHalfFockChargedTensorCoefficients (ActualGround)
open Orbifold.NativeOddTwistedIntertwiner (TwistedEven TwistedOdd leechUnit)
open NativeFixedPairAIterate (fixedAExponent fixedAIterateCoeff)
open NativeMixedUpperProductCusp (bProductCoeff bSewnNumerator)
open NativeMixedUpperDLip (dProductCoeff)
open NativeMixedWickChartTransport (MixedParity doubledOccupation)
open OriginalFourMActualChart (Puncture)
open OriginalFourMVariableSupport (wordAt)
open OriginalGaussianSewnAnalytic (coefficient)

private theorem cast_occupation {ι : Type*} (slot : ι → Puncture) (n : ι → ℕ)
    (l : List ι) (i : Puncture) :
    ((doubledOccupation slot n l i).toNat : ℤ) = doubledOccupation slot n l i := by
  apply Int.toNat_of_nonneg
  classical
  unfold doubledOccupation
  apply List.sum_nonneg
  intro m hm
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hm
  split <;> omega

set_option maxHeartbeats 4000000 in
/-- Finite Jacobi for actual marked HHBB modes with integer test monomial
`X^q Z^p (X-Z)^r` in physical coordinates. The collision rational is
`swapRational (commonRational P d M K L)`. The B term uses the native minus
sign, and the A term uses the iterate convolved with the binomial series of
exponent `-1/2`. On the degree `-2` slice, both product extractions are outer
residues. -/
theorem hhbb_marked_coefficient_jacobi {ι : Type*} [Finite ι]
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
    let C (m : ℕ) := PowerSeries.coeff m (PowerSeries.binomialSeries ℂ (-1 / 2 : ℂ) *
      PowerSeries.mk (fun j => fixedAIterateCoeff false M K L N (fixedAExponent M K j)
        u v wState.val bState.val))
    let dTerm := ∑ ij ∈ modePairs ((c : ℤ) - q - 1),
      (-1 : ℂ) ^ (r + (ij.2 : ℤ)) * ((Ring.choose r ij.2 : ℤ) : ℂ) * D ij.1
    let aTerm := ∑ ij ∈ modePairs ((b : ℤ) - r - 1), ((Ring.choose q ij.2 : ℤ) : ℂ) * C ij.1
    ((∑ ij ∈ modePairs (w + a + q + r + 1),
        (-1 : ℂ) ^ ij.2 * ((Ring.choose r ij.2 : ℤ) : ℂ) * (-B ij.1)) - dTerm = aTerm) ∧
    (w + q + p + r = -2 →
      (∑ ij ∈ modePairs ((a : ℤ) - p - 1),
        (-1 : ℂ) ^ ij.2 * ((Ring.choose r ij.2 : ℤ) : ℂ) * (-B ij.1)) - dTerm = aTerm) := by
  intro grade M K L N a b c w B D C dTerm aTerm
  let d := (12 + M + K + L + N) / 2
  let V := wordAt leechData slot colour n l
  let GInf (y : ℂ) := Complex.I ^ ((L : ℤ) + N - K - 2 * (M : ℤ) - 3) *
    bSewnNumerator M L N (V .Q) (V .P) (V .R) (V .S) gQ gP gR gS y
  let G (y : ℂ) := (y - 1) ^ b * GInf y
  let P : Polynomial ℂ := ∑ j ∈ Finset.range (d + 1),
    Polynomial.C (coefficient j G) * Polynomial.X ^ (d - j)
  let R := swapRational (commonRational P d M K L)
  have hP : P.natDegree ≤ d := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro j _
    exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (Nat.sub_le ..)
  have hgrade (i : Puncture) : (grade i : ℤ) = doubledOccupation slot n l i :=
    cast_occupation slot n l i
  have hM : (M : ℤ) % 2 = 0 := by simpa only [M, hgrade] using hpar.1
  have hK : (K : ℤ) % 2 = 0 := by simpa only [K, hgrade] using hpar.2.1
  have hL : (L : ℤ) % 2 = 1 := by simpa only [L, hgrade] using hpar.2.2.1
  have hN : (N : ℤ) % 2 = 1 := by simpa only [N, hgrade] using hpar.2.2.2
  have hDegree : (d : ℤ) = w + a + b + c := by
    dsimp [d, w, a, b, c]
    omega
  obtain ⟨⟨hB', hB0⟩, ⟨hD', hD0⟩, ⟨hA', hA0⟩⟩ :=
    hhbb_marked_three_iota_coefficients slot colour n l hl hpar u v wState bState
      gP gQ gR gS hu hv hw hb
  have hB (m : ℕ) : (iotaZX ℂ R).coeff ((m : ℤ) - a) = single (w + a - m) (-B m) := by
    rw [← show (d : ℤ) - c - b - m = w + a - m by omega]
    exact hB' m
  have hD (m : ℕ) : (iotaXZ ℂ R).coeff ((m : ℤ) - c) = single (w + c - m) (D m) := by
    rw [← show (1 + (N : ℤ) - K) / 2 - m = w + c - m by
      dsimp only [w, c]
      omega]
    exact hD' m
  have hA (m : ℕ) : (iotaFused ℂ R).coeff ((m : ℤ) - b) = single (w + b - m) (C m) := by
    rw [← show ((N : ℤ) - L) / 2 - m = w + b - m by
      dsimp only [w, b]
      omega]
    exact hA' m
  have hJacobi := coefficient_jacobi R B D C a b c w q p r hB hB0 hD hD0 hA hA0
    (swapped_commonRational_weighted_collision P d M K L hP q p r)
  refine ⟨hJacobi, fun hbalance => ?_⟩
  rw [show (a : ℤ) - p - 1 = w + a + q + r + 1 by omega]
  exact hJacobi

end D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHHBBModeResidue
