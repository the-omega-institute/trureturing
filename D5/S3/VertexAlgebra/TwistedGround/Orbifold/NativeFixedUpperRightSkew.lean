/- GID: D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeFixedUpperRightSkew
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/Orbifold/NativeFixedUpperRightSkew
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual fixed-source upper opposite field and its finite ordered tensor pairing. -/

import D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddUpperRightSkew
import D5.S3.VertexAlgebra.TwistedGround.OriginalRightSkew

/-!
The fixed-source opposite field is the coefficient convolution of the upper
half-turn with the physical translation exponential. Its physical exponent
`-m-1` corresponds to the doubled Hahn exponent `-2*m-2`. The result stays
in the original twisted parity of the input.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators VertexOperator

namespace D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeFixedUpperRightSkew

open LatticeGeneratingFieldLocality (LatticeData)
open LatticeInvolution (FixedCarrier fixedVacuum)
open LatticeHalfFockChargedTensorCoefficients (ActualTensor)
open LatticeHalfFockCorrectedField (correctedField)
open LatticeHalfFockGradedTrace (actualGrade)
open HalfFock.LatticeHalfFockParityField (fixedParitySlice paritySpace)
open ActualChargedAdjoint (actualForm)
open NativeOddTwistedIntertwiner (Twisted paritySign)
open NativeOddUpperRightSkew (translation)
open private fixedParityMode_val from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddTwistedIntertwiner
open private translation_power_pairing lowering_tail from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddUpperRightSkew
open private T from D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner
open private rightTerm from D5.S3.VertexAlgebra.TwistedGround.OriginalRightSkew
open private vacuum_coeff from D5.S3.VertexAlgebra.LatticeHalfFockCurrentBorcherds

/-- The fixed-source mode on either actual twisted parity. -/
def J (D : LatticeData) (hu : IsUnit D.G.det) (s : Bool) (m : ℤ) :
    FixedCarrier D →ₗ[ℂ] Module.End ℂ (Twisted D hu s) where
  toFun a := (fixedParitySlice D hu (paritySign s) a)[[m]]
  map_add' a b := by
    apply LinearMap.ext
    intro u
    apply Subtype.ext
    change (correctedField D hu (a.val + b.val)).coeff (2 * (-m - 1)) u.val =
      (correctedField D hu a.val).coeff (2 * (-m - 1)) u.val +
        (correctedField D hu b.val).coeff (2 * (-m - 1)) u.val
    simp only [map_add, Pi.add_apply, LinearMap.add_apply]
  map_smul' c a := by
    apply LinearMap.ext
    intro u
    apply Subtype.ext
    change (correctedField D hu (c • a.val)).coeff (2 * (-m - 1)) u.val =
      c • (correctedField D hu a.val).coeff (2 * (-m - 1)) u.val
    simp only [map_smul, Pi.smul_apply, LinearMap.smul_apply, RingHom.id_apply]

theorem J_val (D : LatticeData) (hu : IsUnit D.G.det) (s : Bool) (m : ℤ)
    (a : FixedCarrier D) (u : Twisted D hu s) :
    (J D hu s m a u).val = (correctedField D hu a.val).coeff (-2 * m - 2) u.val :=
  fixedParityMode_val D hu (paritySign s) a m u

/-- The raw mode tail follows from the Hahn order of the actual corrected field. -/
theorem J_truncation (D : LatticeData) (hu : IsUnit D.G.det) (s : Bool)
    (a : FixedCarrier D) (u : Twisted D hu s) :
    ∃ B : ℤ, ∀ m ≥ B, J D hu s m a u = 0 := by
  let order := ((HahnModule.of ℂ).symm ((correctedField D hu a.val) u.val)).order
  refine ⟨-(order / 2), fun m hm => Subtype.ext ?_⟩
  rw [J_val]
  change ((HahnModule.of ℂ).symm ((correctedField D hu a.val) u.val)).coeff
    (-2 * m - 2) = 0
  apply HahnSeries.coeff_eq_zero_of_lt_order
  change -2 * m - 2 < order
  omega

/-- The contribution of translation order `ell` to the fixed right mode. -/
def rightSummand (D : LatticeData) (hu : IsUnit D.G.det) (s : Bool) (m : ℤ)
    (u : Twisted D hu s) (a : FixedCarrier D) (ell : ℕ) : Twisted D hu s :=
  (Complex.I ^ (-2 * (m + (ell : ℤ)) - 2) * (ell.factorial : ℂ)⁻¹) •
    (translation D hu s ^ ell) (J D hu s (m + (ell : ℤ)) a u)

private theorem rightSummand_support (D : LatticeData) (hu : IsUnit D.G.det) (s : Bool)
    (m B : ℤ) (u : Twisted D hu s) (a : FixedCarrier D)
    (hB : ∀ n ≥ B, J D hu s n a u = 0) :
    Function.support (rightSummand D hu s m u a) ⊆
      (Finset.range (B - m).toNat : Set ℕ) := by
  intro ell hell
  by_contra hout
  have hbound : (B - m).toNat ≤ ell :=
    Nat.le_of_not_gt (fun h => hout (Finset.mem_range.mpr h))
  exact hell (by simp only [rightSummand, hB (m + (ell : ℤ)) (by omega), map_zero, smul_zero])

theorem rightSummand_finite (D : LatticeData) (hu : IsUnit D.G.det)
    (s : Bool) (m : ℤ) (u : Twisted D hu s) (a : FixedCarrier D) :
    Function.HasFiniteSupport (rightSummand D hu s m u a) := by
  obtain ⟨B, hB⟩ := J_truncation D hu s a u
  exact (Finset.range (B - m).toNat).finite_toSet.subset
    (rightSummand_support D hu s m B u a hB)

/-- The bilinear coefficient of `exp(z L(-1)) Y^T(a, e^(πi) z) u`. -/
def R (D : LatticeData) (hu : IsUnit D.G.det) (s : Bool) (m : ℤ) :
    Twisted D hu s →ₗ[ℂ] FixedCarrier D →ₗ[ℂ] Twisted D hu s where
  toFun u := {
    toFun a := ∑ᶠ ell : ℕ, rightSummand D hu s m u a ell
    map_add' a b := by
      simp only [rightSummand, map_add, LinearMap.add_apply, smul_add]
      exact finsum_add_distrib (rightSummand_finite D hu s m u a)
        (rightSummand_finite D hu s m u b)
    map_smul' c a := by
      simpa only [rightSummand, map_smul, LinearMap.smul_apply, RingHom.id_apply,
        smul_smul, mul_comm] using
        (smul_finsum c (rightSummand D hu s m u a)).symm }
  map_add' u v := by
    apply LinearMap.ext
    intro a
    change (∑ᶠ ell : ℕ, rightSummand D hu s m (u + v) a ell) =
      (∑ᶠ ell : ℕ, rightSummand D hu s m u a ell) +
        (∑ᶠ ell : ℕ, rightSummand D hu s m v a ell)
    simp only [rightSummand, map_add, smul_add]
    exact finsum_add_distrib (rightSummand_finite D hu s m u a)
      (rightSummand_finite D hu s m v a)
  map_smul' c u := by
    apply LinearMap.ext
    intro a
    change (∑ᶠ ell : ℕ, rightSummand D hu s m (c • u) a ell) =
      c • (∑ᶠ ell : ℕ, rightSummand D hu s m u a ell)
    simpa only [rightSummand, map_smul, RingHom.id_apply, smul_smul, mul_comm] using
      (smul_finsum c (rightSummand D hu s m u a)).symm

theorem R_eq_sum (D : LatticeData) (hu : IsUnit D.G.det) (s : Bool)
    (m B : ℤ) (u : Twisted D hu s) (a : FixedCarrier D)
    (hB : ∀ n ≥ B, J D hu s n a u = 0) :
    R D hu s m u a =
      ∑ ell ∈ Finset.range (B - m).toNat, rightSummand D hu s m u a ell := by
  change (∑ᶠ ell : ℕ, rightSummand D hu s m u a ell) = _
  exact finsum_eq_sum_of_support_subset _ (rightSummand_support D hu s m B u a hB)

theorem R_truncation (D : LatticeData) (hu : IsUnit D.G.det) (s : Bool)
    (u : Twisted D hu s) (a : FixedCarrier D) :
    ∃ B : ℤ, ∀ m ≥ B, R D hu s m u a = 0 := by
  obtain ⟨B, hB⟩ := J_truncation D hu s a u
  refine ⟨B, fun m hm => ?_⟩
  rw [R_eq_sum D hu s m B u a hB, show (B - m).toNat = 0 by omega] <;> simp

private def doubledCoefficient (D : LatticeData) (hu : IsUnit D.G.det) (s : Bool) (e : ℤ) :
    Twisted D hu s →ₗ[ℂ] FixedCarrier D →ₗ[ℂ] Twisted D hu s :=
  if Even e then R D hu s ((-e - 2) / 2) else 0

private theorem doubled_support (D : LatticeData) (hu : IsUnit D.G.det) (s : Bool)
    (u : Twisted D hu s) (a : FixedCarrier D) :
    (Function.support (fun e => doubledCoefficient D hu s e u a)).IsPWO := by
  obtain ⟨B, hB⟩ := R_truncation D hu s u a
  apply Set.isPWO_iff_isWF.mpr
  apply BddBelow.isWF
  refine ⟨-2 * B - 2, ?_⟩
  intro e he
  change -2 * B - 2 ≤ e
  by_contra h
  have hz := hB ((-e - 2) / 2) (by omega)
  exact he (by by_cases hEven : Even e <;> simp [doubledCoefficient, hEven, hz])

/-- The actual parity-preserving opposite field in the doubled Hahn coordinate. -/
def rightField (D : LatticeData) (hu : IsUnit D.G.det) (s : Bool) :
    Twisted D hu s →ₗ[ℂ] HVertexOperator ℤ ℂ (FixedCarrier D) (Twisted D hu s) where
  toFun u := HVertexOperator.of_coeff (fun e => doubledCoefficient D hu s e u)
    (doubled_support D hu s u)
  map_add' u v := by
    apply HVertexOperator.coeff_inj
    funext e
    rw [map_add, Pi.add_apply]
    exact (doubledCoefficient D hu s e).map_add u v
  map_smul' c u := by
    apply HVertexOperator.coeff_inj
    funext e
    rw [map_smul, Pi.smul_apply]
    exact (doubledCoefficient D hu s e).map_smul c u

theorem rightField_coeff (D : LatticeData) (hu : IsUnit D.G.det) (s : Bool)
    (m : ℤ) (u : Twisted D hu s) (a : FixedCarrier D) :
    (rightField D hu s u).coeff (-2 * m - 2) a = R D hu s m u a := by
  have he : Even (-2 * m - 2) := ⟨-m - 1, by omega⟩
  change doubledCoefficient D hu s (-2 * m - 2) u a = _
  rw [doubledCoefficient, if_pos he, show (-(-2 * m - 2) - 2) / 2 = m by omega]

theorem rightField_odd_zero (D : LatticeData) (hu : IsUnit D.G.det) (s : Bool)
    (e : ℤ) (he : Odd e) (u : Twisted D hu s) (a : FixedCarrier D) :
    (rightField D hu s u).coeff e a = 0 := by
  change doubledCoefficient D hu s e u a = 0
  simp only [doubledCoefficient, if_neg (Int.not_even_iff_odd.mpr he), LinearMap.zero_apply]

/-- Move translation to the detector by the actual stress transpose. For
detector grade `N`, every lowering order `ell ≥ N / 2 + 1` vanishes. -/
theorem R_pairing_finite (D : LatticeData) (hu : IsUnit D.G.det)
    (s : Bool) (m : ℤ) (N : ℕ) (u : Twisted D hu s) (a : FixedCarrier D)
    (d : ActualTensor D hu) (hd : d ∈ actualGrade D hu N) :
    actualForm D hu d (R D hu s m u a).val =
      ∑ ell ∈ Finset.range (N / 2 + 1),
        (Complex.I ^ (-2 * (m + (ell : ℤ)) - 2) * (ell.factorial : ℂ)⁻¹) *
          actualForm D hu ((T D hu ^ ell) d)
            ((correctedField D hu a.val).coeff (-2 * (m + (ell : ℤ)) - 2) u.val) := by
  classical
  let pair : Twisted D hu s →ₗ[ℂ] ℂ :=
    (actualForm D hu d).comp (paritySpace D hu (paritySign s)).subtype
  let term (ell : ℕ) : ℂ :=
    (Complex.I ^ (-2 * (m + (ell : ℤ)) - 2) * (ell.factorial : ℂ)⁻¹) *
      actualForm D hu ((T D hu ^ ell) d)
        ((correctedField D hu a.val).coeff (-2 * (m + (ell : ℤ)) - 2) u.val)
  have htranspose (ell : ℕ) : pair (rightSummand D hu s m u a ell) = term ell := by
    change actualForm D hu d (rightSummand D hu s m u a ell).val = _
    simp only [rightSummand, Submodule.coe_smul, map_smul, smul_eq_mul,
      translation_power_pairing, term, J_val]
  have hsupport : Function.support term ⊆ (Finset.range (N / 2 + 1) : Set ℕ) := by
    intro ell hell
    apply Finset.mem_range.mpr
    by_contra hout
    have hz := lowering_tail D hu N d hd ell (Nat.le_of_not_gt hout)
    exact hell (by simp [term, hz])
  change pair (∑ᶠ ell : ℕ, rightSummand D hu s m u a ell) = _
  rw [map_finsum pair (rightSummand_finite D hu s m u a)]
  calc
    (∑ᶠ ell : ℕ, pair (rightSummand D hu s m u a ell)) = ∑ᶠ ell : ℕ, term ell := by
      simp only [htranspose]
    _ = _ := finsum_eq_sum_of_support_subset term hsupport

private theorem I_zpow_neg_two : Complex.I ^ (-2 : ℤ) = -1 := by
  rw [show (-2 : ℤ) = -((2 : ℕ) : ℤ) by decide, zpow_neg, zpow_natCast,
    Complex.I_sq, inv_neg, inv_one]

/-- The detector range and raw mode in the energy indexing of the four-field
product. The upper phase splits into the diagonal phase and the sign of
`E + ell`. -/
theorem R_pairing_energy_diagonal (D : LatticeData) (hu : IsUnit D.G.det)
    (s : Bool) (L N E : ℕ) (n₀ : ℤ) (u : Twisted D hu s)
    (a : FixedCarrier D) (d : ActualTensor D hu) (hd : d ∈ actualGrade D hu N)
    (hn₀ : -2 * n₀ - 2 = (N : ℤ) - (L : ℤ)) :
    actualForm D hu d (R D hu s (n₀ + (E : ℤ)) u a).val =
      Complex.I ^ ((N : ℤ) - (L : ℤ)) *
        ∑ ell ∈ Finset.range (N / 2 + 1),
          ((-1 : ℂ) ^ (E + ell) * (ell.factorial : ℂ)⁻¹) *
            actualForm D hu ((T D hu ^ ell) d)
              ((correctedField D hu a.val).coeff
                ((N : ℤ) - (L : ℤ) - 2 * (E : ℤ) - 2 * (ell : ℤ)) u.val) := by
  rw [R_pairing_finite D hu s _ N u a d hd, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ell _
  have he : -2 * (n₀ + (E : ℤ) + (ell : ℤ)) - 2 =
      (N : ℤ) - (L : ℤ) - 2 * (E : ℤ) - 2 * (ell : ℤ) := by omega
  have hphase :
      Complex.I ^ ((N : ℤ) - (L : ℤ) - 2 * (E : ℤ) - 2 * (ell : ℤ)) =
        Complex.I ^ ((N : ℤ) - (L : ℤ)) * (-1 : ℂ) ^ (E + ell) := by
    rw [show (N : ℤ) - (L : ℤ) - 2 * (E : ℤ) - 2 * (ell : ℤ) =
        ((N : ℤ) - (L : ℤ)) + (-2) * ((E + ell : ℕ) : ℤ) by omega,
      zpow_add₀ Complex.I_ne_zero, zpow_mul Complex.I (-2), I_zpow_neg_two, zpow_natCast]
  rw [he, hphase]
  ring

/-- For negative twisted parity the upper even phase gives the sign of the
original right coefficient. -/
theorem R_eq_originalRightCoefficient (D : LatticeData) (hu : IsUnit D.G.det)
    (m : ℤ) (u : Twisted D hu true) (a : FixedCarrier D) :
    R D hu true m u a = MixedIntertwiner.originalRightCoefficient D hu m u a := by
  have phase (n : ℤ) : Complex.I ^ (-2 * n - 2) = (-1 : ℂ) ^ (n + 1) := by
    rw [show -2 * n - 2 = (-2) * (n + 1) by ring, zpow_mul, I_zpow_neg_two]
  change (∑ᶠ ell : ℕ, rightSummand D hu true m u a ell) =
    ∑ᶠ ell : ℕ, rightTerm D hu m u a ell
  apply finsum_congr
  intro ell
  rw [rightSummand, rightTerm, phase] <;> rfl

private theorem J_vacuum (D : LatticeData) (hu : IsUnit D.G.det) (s : Bool)
    (n : ℤ) (u : Twisted D hu s) :
    J D hu s n (fixedVacuum D) u = if n = -1 then u else 0 := by
  apply Subtype.ext
  rw [J_val]
  change (correctedField D hu (LatticeAllStateField.vacuum D)).coeff
    (-2 * n - 2) u.val = _
  rw [vacuum_coeff]
  by_cases h : n = -1
  · norm_num [h]
  · have he : -2 * n - 2 ≠ 0 := by omega
    simp only [ite_eq_right he, ite_eq_right h, Submodule.coe_zero]

/-- The fixed vacuum gives the input at physical degree zero and vanishes
at every negative physical power, in both twisted parities. -/
theorem R_vacuum (D : LatticeData) (hu : IsUnit D.G.det) (s : Bool)
    (m : ℤ) (hm : -1 ≤ m) (u : Twisted D hu s) :
    R D hu s m u (fixedVacuum D) = if m = -1 then u else 0 := by
  classical
  change (∑ᶠ ell : ℕ, rightSummand D hu s m u (fixedVacuum D) ell) = _
  rw [finsum_eq_single _ 0]
  · by_cases h : m = -1
    · norm_num [h, rightSummand, J_vacuum]
    · simp [h, rightSummand, J_vacuum]
  · intro ell hell
    have h : m + (ell : ℤ) ≠ -1 := by omega
    simp [rightSummand, J_vacuum, h]

end D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeFixedUpperRightSkew
