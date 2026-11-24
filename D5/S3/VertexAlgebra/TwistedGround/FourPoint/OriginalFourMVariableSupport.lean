/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMVariableSupport
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMVariableSupport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Variable native occupation support after four inverse oscillator lowerings. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMNativeLaurent

/-! Native occupation support, Laurent projection, and crossing after inverse lowering. -/

set_option autoImplicit false
set_option maxRecDepth 4096
noncomputable section
open scoped BigOperators Matrix TensorProduct Topology

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalFourMVariableSupport

open LatticeGeneratingFieldLocality LatticeHalfFock
open LatticeDiscriminantTheta (gramReal)
open LatticePositiveEnergy (Exponent)
open LatticeTwistedGroundRealization.SignQuotient (ModTwoCharge)
open FourPoint.OriginalFourMActualChart
open OriginalFourMEnergyCoefficient (doubledWeight)
open OriginalFourMChargeCoset (fourierSign quadraticSign)
open OriginalFourMSpatialWickPartition (liftedScale)
open LatticeHalfFockChargedTensorCoefficients (ActualGround)
open LatticeHalfFockGradedTrace (actualTensorL0)
open OriginalFourMChargeCoset (slitChannelA slitChannelB dLipChannel)

open private oscillatorWord laurentPower laurentPhase from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMNativeLaurent
open private determinant from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMLoweredNormalization
open private product_native from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMNativeOccupation
open private lowering_weight from
  D5.S3.VertexAlgebra.TwistedGround.OriginalFourMEnergyCoefficient

open OriginalFourMPhysicalCovariance (relative)
open OriginalFourMChartProduct (chartPeriod chart_charge_data)
open OriginalFourMSignedOverlap (chart_parameter_ne_one)
open NativeAffineExternalCoefficient (jetOccupation)
open LatticeHalfFockChargedCoefficients (omega)
open private word_slots from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMCompactLowering
open private relative_same_slot from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMPhysicalCovariance
open private chartA_normalization chartB_normalization chartA_radius slot from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMAFourCurrent
open private d_chart_normalization from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMDFourCurrent

private theorem word_monomial (D : LatticeData) (l : List (Index D)) :
    oscillatorWord D l = MvPolynomial.monomial (jetOccupation l) 1 := by
  induction l with
  | nil => simp [oscillatorWord, jetOccupation]
  | cons i l ih =>
    change MvPolynomial.monomial (Finsupp.single i 1) 1 * oscillatorWord D l =
      MvPolynomial.monomial (jetOccupation l + Finsupp.single i 1) 1
    rw [ih, MvPolynomial.monomial_mul_monomial, mul_one]
    exact congrArg (fun d => MvPolynomial.monomial d (1 : ℂ)) (add_comm _ _)

private theorem word_weight (D : LatticeData) (l : List (Index D)) :
    doubledWeight D (jetOccupation l) = (((l.map fun a => (2 * a.2 + 1 : ℕ)).sum : ℕ) : ℤ) := by
  induction l with
  | nil => simp [jetOccupation]
  | cons a l ih =>
    have ha : doubledWeight D (Finsupp.single a 1) = (omega D a : ℤ) := by
      simp [Finsupp.weight_apply, Finsupp.sum_single_index]
    change doubledWeight D (jetOccupation l + Finsupp.single a 1) = _
    rw [show doubledWeight D (jetOccupation l + Finsupp.single a 1) =
      doubledWeight D (jetOccupation l) + doubledWeight D (Finsupp.single a 1) from map_add _ _ _,
      ih, ha, omega]
    simp only [List.map_cons, List.sum_cons, Nat.cast_add]
    ring

private def baseScale (c : Chart) (x : ℝ) (i : Puncture) : ℂ :=
  relative c i * (scaleRoot c x i)⁻¹

private theorem baseScale_sq (c : Chart) {x : ℝ} (hx : 0 < x) (hx₁ : x < 1) (i : Puncture) :
    baseScale c x i ^ 2 = (scale c (x : ℂ) i)⁻¹ := by
  rw [baseScale, mul_pow, relative_same_slot, one_mul, inv_pow, (chosen_roots hx hx₁ c i).1]

private theorem baseScale_ne (c : Chart) {x : ℝ} (hx : 0 < x) (hx₁ : x < 1) (i : Puncture) :
    baseScale c x i ≠ 0 := by
  have hs := baseScale_sq c hx hx₁ i
  have h := (chosen_roots hx hx₁ c i).1
  rw [← h, ← inv_pow] at hs
  intro hz
  exact (pow_ne_zero 2 (inv_ne_zero (OriginalFourMOccupationTransport.root_ne hx hx₁ c i)))
    (hs.symm.trans (by simp [hz]))

private theorem word_scale (D : LatticeData) (c : Chart) {x : ℝ} (hx : 0 < x) (hx₁ : x < 1)
    (i : Puncture) (l : List (Index D)) :
    (l.map fun a => liftedScale c x i a.2).prod =
      baseScale c x i ^ (doubledWeight D (jetOccupation l)) := by
  have hl (a : Index D) : liftedScale c x i a.2 = baseScale c x i ^ (2 * a.2 + 1) := by
    rw [pow_succ, pow_mul, baseScale_sq c hx hx₁ i]
    unfold liftedScale baseScale
    ring
  rw [word_weight, zpow_natCast]
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, ih, hl a, List.map_cons, List.sum_cons]
    simp only [pow_add]

private theorem puncture_weight_scale (D : LatticeData) (hu : IsUnit D.G.det)
    (h24 : D.rank = 24) (c : Chart) {x : ℝ} (hx : 0 < x) (hx₁ : x < 1)
    (i : Puncture) (l : List (Index D)) (H : ℕ)
    (p : ActualGround D hu) (hp : p ≠ 0)
    (hP : actualTensorL0 D hu (oscillatorWord D l ⊗ₜ[ℂ] p) =
      (H : ℂ) • (oscillatorWord D l ⊗ₜ[ℂ] p)) :
    (l.map fun a => liftedScale c x i a.2).prod =
      baseScale c x i * (scale c (x : ℂ) i) ^ (2 - (H : ℤ)) := by
  have hmem : jetOccupation l ∈ (oscillatorWord D l).support := by
    rw [word_monomial]
    simp [MvPolynomial.support_monomial]
  have he := lowering_weight D hu h24 H 0 (oscillatorWord D l) p hP hp (jetOccupation l)
    (by simpa [Module.End.one_apply] using hmem)
  rw [word_scale D c hx hx₁ i, he, Nat.cast_zero]
  rw [show 2 * (H : ℤ) - 3 - 2 * (0 : ℤ) = 1 + 2 * ((H : ℤ) - 2) by ring,
    zpow_add₀ (baseScale_ne c hx hx₁ i), zpow_one, zpow_mul]
  have hs : baseScale c x i ^ (2 : ℤ) = (scale c (x : ℂ) i)⁻¹ :=
    baseScale_sq c hx hx₁ i
  rw [hs, inv_zpow', show -((H : ℤ) - 2) = 2 - (H : ℤ) by ring]

private def lowestFactor (c : Chart) (x : ℝ) : ℂ :=
  match c with
  | .A => -Complex.I / ((x : ℂ) ^ 3 * (1 - (x : ℂ)))
  | .B => -Complex.I * (1 - (x : ℂ)) ^ 3 / (x : ℂ)
  | .D => -Complex.I * (1 - (x : ℂ)) ^ 3 / (x : ℂ) ^ 3

private theorem lowestFactor_eq (c : Chart) {x : ℝ} (hx : 0 < x) (hx₁ : x < 1) :
    (1 - parameter c (x : ℂ)) ^ (3 : ℕ) *
      (baseScale c x .P * (baseScale c x .Q * (baseScale c x .R * baseScale c x .S))) =
      lowestFactor c x := by
  let z := (1 - parameter c (x : ℂ)) ^ (3 : ℕ)
  let p := (chartPeriod true c x ^ (12 : ℕ))⁻¹
  let b := baseScale c x .P * (baseScale c x .Q * (baseScale c x .R * baseScale c x .S))
  have hz : z ≠ 0 := pow_ne_zero _ (chart_parameter_ne_one hx hx₁ c)
  have hp : p ≠ 0 := inv_ne_zero (pow_ne_zero _ (chart_charge_data true c hx hx₁).1)
  have hd : determinant c x = z⁻¹ * p := by cases c <;> rfl
  have hb : p * b = lowestFactor c x * determinant c x := by
    have hv : (∏ i : Fin 4, baseScale c x (slot i)) = b := by
      simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one] <;> rfl
    rw [← hv]
    cases c
    · simpa only [p, lowestFactor, determinant, baseScale, relative, one_mul]
        using chartA_normalization true hx hx₁
    · exact chartB_normalization true hx hx₁
    · exact d_chart_normalization hx hx₁
  change z * b = _
  apply mul_right_cancel₀ hp
  calc
    z * b * p = z * (p * b) := by ring
    _ = z * (lowestFactor c x * (z⁻¹ * p)) := by rw [hb, hd]
    _ = (z * z⁻¹) * (lowestFactor c x * p) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hz, one_mul]

private theorem neg_base_zpow (u : ℂ) (k : ℤ) : (-u) ^ k = (-1 : ℂ) ^ k * u ^ k := by
  rw [← mul_zpow, neg_one_mul]

private theorem neg_one_even (k : ℤ) : (-1 : ℂ) ^ (2 * k) = 1 := by
  rw [zpow_mul]
  norm_num

private def channelFactor (c : Chart) (x : ℝ) (s : ℤ) : ℂ :=
  -Complex.I * (1 - (x : ℂ)) ^ (3 : ℕ) *
    (x : ℂ) ^ (match c with | .A | .D => -s - 5 | .B => 3)

private theorem scalar_laurent (c : Chart) {x : ℝ} (hx : 0 < x) (hx₁ : x < 1)
    (H K L J : ℕ) (s : ℤ) (hs : (J : ℤ) = H + K + L - s - 2) :
    lowestFactor c x *
      (scale c (x : ℂ) .P ^ (2 - (H : ℤ)) * (scale c (x : ℂ) .Q ^ (2 - (K : ℤ)) *
        (scale c (x : ℂ) .R ^ (2 - (L : ℤ)) * scale c (x : ℂ) .S ^ (2 - (J : ℤ))))) *
      ((-parameter c (x : ℂ)) ^ laurentPower H K L c * laurentPhase K L s c) =
      channelFactor c x s := by
  let X : ℂ := x
  let Y : ℂ := 1 - X
  have hX : X ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hY : Y ≠ 0 := by
    change 1 - (x : ℂ) ≠ 0
    exact sub_ne_zero.mpr (by exact_mod_cast hx₁.ne')
  have hN : (-1 : ℂ) ≠ 0 := by norm_num
  have ha : -(1 - X⁻¹) = Y / X := by
    dsimp [Y]
    field_simp [hX]
    ring
  have hi : X ^ (-3 : ℤ) = (X ^ (3 : ℕ))⁻¹ := rfl
  cases c with
  | A =>
    change (-Complex.I / (X ^ (3 : ℕ) * Y)) *
        (Y ^ (2 - (H : ℤ)) * ((-Y) ^ (2 - (K : ℤ)) *
          (X ^ (2 - (L : ℤ)) * X⁻¹ ^ (2 - (J : ℤ))))) *
        ((-(1 - X⁻¹)) ^ ((H : ℤ) + K) * (-1 : ℂ) ^ (K : ℤ)) = _
    have hLaurent : (-(1 - X⁻¹)) ^ ((H : ℤ) + K) =
        Y ^ ((H : ℤ) + K) * X ^ (-((H : ℤ) + K)) := by
      rw [ha, div_zpow, div_eq_mul_inv, zpow_neg]
    rw [hLaurent, neg_base_zpow Y, inv_zpow' X]
    calc
      _ = -Complex.I * ((-1 : ℂ) ^ (2 - (K : ℤ)) * (-1 : ℂ) ^ (K : ℤ)) *
          ((Y ^ (-1 : ℤ) * Y ^ (2 - (H : ℤ))) *
            (Y ^ (2 - (K : ℤ)) * Y ^ ((H : ℤ) + K))) *
          ((X ^ (-3 : ℤ) * X ^ (2 - (L : ℤ))) *
            (X ^ (- (2 - (J : ℤ))) * X ^ (-((H : ℤ) + K)))) := by
        rw [div_eq_mul_inv, mul_inv_rev, ← hi, zpow_neg_one]
        ring
      _ = _ := by
        simp only [← zpow_add₀ hN, ← zpow_add₀ hX, ← zpow_add₀ hY]
        have hsign : (2 - (K : ℤ)) + K = 2 * 1 := by ring
        have hy : -1 + (2 - (H : ℤ)) + (2 - (K : ℤ) + (H + K)) = (3 : ℤ) := by ring
        have hx' : -3 + (2 - (L : ℤ)) + (-(2 - (J : ℤ)) + -(H + K)) = -s - 5 := by omega
        rw [hsign, hy, hx', neg_one_even, mul_one] <;> rfl
  | B =>
    change (-Complex.I * Y ^ (3 : ℕ) / X) *
        ((-1 : ℂ) ^ (2 - (H : ℤ)) * (X ^ (2 - (K : ℤ)) *
          ((-X) ^ (2 - (L : ℤ)) * (-1 : ℂ) ^ (2 - (J : ℤ))))) *
        ((-X) ^ ((K : ℤ) + L) * ((-1 : ℂ) ^ (s + 2) * (-1 : ℂ) ^ (L : ℤ))) = _
    rw [neg_base_zpow X (2 - (L : ℤ)), neg_base_zpow X ((K : ℤ) + L)]
    calc
      _ = (-Complex.I * Y ^ (3 : ℕ)) *
          (((-1 : ℂ) ^ (2 - (H : ℤ)) * (-1 : ℂ) ^ (2 - (L : ℤ))) *
            (((-1 : ℂ) ^ (2 - (J : ℤ)) * (-1 : ℂ) ^ ((K : ℤ) + L)) *
              ((-1 : ℂ) ^ (s + 2) * (-1 : ℂ) ^ (L : ℤ)))) *
          ((X ^ (-1 : ℤ) * X ^ (2 - (K : ℤ))) *
            (X ^ (2 - (L : ℤ)) * X ^ ((K : ℤ) + L))) := by
        simp only [zpow_neg_one, div_eq_mul_inv]
        ring
      _ = _ := by
        simp only [← zpow_add₀ hN, ← zpow_add₀ hX]
        have hsign : (2 - (H : ℤ)) + (2 - (L : ℤ)) +
            ((2 - (J : ℤ)) + (K + L) + (s + 2 + L)) = 2 * (5 - (H : ℤ) + s) := by omega
        have hx' : -1 + (2 - (K : ℤ)) + (2 - (L : ℤ) + (K + L)) = (3 : ℤ) := by ring
        rw [hsign, hx', neg_one_even, mul_one] <;> rfl
  | D =>
    change (-Complex.I * Y ^ (3 : ℕ) / X ^ (3 : ℕ)) *
        ((1 : ℂ) ^ (2 - (H : ℤ)) * ((-X) ^ (2 - (K : ℤ)) *
          ((-1 : ℂ) ^ (2 - (L : ℤ)) * (-X⁻¹) ^ (2 - (J : ℤ))))) *
        ((-X⁻¹) ^ ((H : ℤ) + L) * ((-1 : ℂ) ^ (s + 2) * (-1 : ℂ) ^ (L : ℤ))) = _
    simp only [one_zpow, one_mul, neg_base_zpow X, neg_base_zpow X⁻¹, inv_zpow']
    calc
      _ = (-Complex.I * Y ^ (3 : ℕ)) *
          (((-1 : ℂ) ^ (2 - (K : ℤ)) * (-1 : ℂ) ^ (2 - (L : ℤ))) *
            (((-1 : ℂ) ^ (2 - (J : ℤ)) * (-1 : ℂ) ^ ((H : ℤ) + L)) *
              ((-1 : ℂ) ^ (s + 2) * (-1 : ℂ) ^ (L : ℤ)))) *
          ((X ^ (-3 : ℤ) * X ^ (2 - (K : ℤ))) *
            (X ^ (-(2 - (J : ℤ))) * X ^ (-((H : ℤ) + L)))) := by
        rw [div_eq_mul_inv, ← hi]
        ring
      _ = _ := by
        simp only [← zpow_add₀ hN, ← zpow_add₀ hX]
        have hsign : (2 - (K : ℤ)) + (2 - (L : ℤ)) +
            ((2 - (J : ℤ)) + (H + L) + (s + 2 + L)) = 2 * (5 - (K : ℤ) + s) := by omega
        have hx' : -3 + (2 - (K : ℤ)) + (-(2 - (J : ℤ)) + -(H + L)) = -s - 5 := by omega
        rw [hsign, hx', neg_one_even, mul_one] <;> rfl

private theorem word_laurent_normalization {X : Type*} (D : LatticeData)
    (hu : IsUnit D.G.det) (h24 : D.rank = 24) (slot : X → Puncture)
    (colour : X → Fin D.rank) (n : X → ℕ) (l : List X)
    (e : Puncture → ℕ) (g : Puncture → ActualGround D hu) (hg : ∀ i, g i ≠ 0)
    (he : ∀ i, actualTensorL0 D hu (wordAt D slot colour n l i ⊗ₜ[ℂ] g i) =
      (e i : ℂ) • (wordAt D slot colour n l i ⊗ₜ[ℂ] g i))
    (s : ℤ) (hmode : (e .S : ℤ) = e .P + e .Q + e .R - s - 2)
    (c : Chart) {x : ℝ} (hx : 0 < x) (hx₁ : x < 1) :
    ((1 - parameter c (x : ℂ)) ^ (3 : ℕ) *
        (l.map fun j => liftedScale c x (slot j) (n j)).prod) *
      ((-parameter c (x : ℂ)) ^ laurentPower (e .P) (e .Q) (e .R) c *
        laurentPhase (e .Q) (e .R) s c) =
      channelFactor c x s := by
  classical
  let slots : Finset Puncture := {.P, .Q, .R, .S}
  have hm (i : Puncture) : i ∈ slots := by cases i <;> simp [slots]
  have hprod (i : Puncture) :
      ((l.filter fun a => decide (slot a = i)).map fun a => liftedScale c x (slot a) (n a)).prod =
        baseScale c x i * scale c (x : ℂ) i ^ (2 - (e i : ℤ)) := by
    have h := puncture_weight_scale D hu h24 c hx hx₁ i
      ((l.filter fun a => decide (slot a = i)).map fun a => (colour a, n a))
      (e i) (g i) (hg i) (he i)
    rw [← h]
    simp only [List.map_map, Function.comp_apply]
    apply congrArg List.prod
    apply List.map_congr_left
    intro a ha
    rw [of_decide_eq_true (List.mem_filter.mp ha).2]
    rfl
  rw [word_slots slot slots _ l (fun a _ => hm (slot a))]
  change ((1 - parameter c (x : ℂ)) ^ (3 : ℕ) * (∏ i ∈ ({.P, .Q, .R, .S} : Finset Puncture),
    ((l.filter fun a => decide (slot a = i)).map fun a => liftedScale c x (slot a) (n a)).prod)) *
    _ = _
  rw [product_native .A]
  change ((1 - parameter c (x : ℂ)) ^ (3 : ℕ) * _) * _ = _
  rw [show nativePuncture .A 0 = .P from rfl, show nativePuncture .A 1 = .Q from rfl,
    show nativePuncture .A 2 = .R from rfl, show nativePuncture .A 3 = .S from rfl]
  simp only [hprod]
  calc
    _ = ((1 - parameter c (x : ℂ)) ^ (3 : ℕ) *
        (baseScale c x .P * (baseScale c x .Q * (baseScale c x .R * baseScale c x .S)))) *
      (scale c (x : ℂ) .P ^ (2 - (e .P : ℤ)) * (scale c (x : ℂ) .Q ^ (2 - (e .Q : ℤ)) *
        (scale c (x : ℂ) .R ^ (2 - (e .R : ℤ)) * scale c (x : ℂ) .S ^ (2 - (e .S : ℤ))))) *
      ((-parameter c (x : ℂ)) ^ laurentPower (e .P) (e .Q) (e .R) c *
        laurentPhase (e .Q) (e .R) s c) := by ring
    _ = _ := by
      rw [lowestFactor_eq c hx hx₁]
      exact scalar_laurent c hx hx₁ (e .P) (e .Q) (e .R) (e .S) s hmode

private theorem fourier_factor (D : LatticeData) (k : ℂ) (f g : ModTwoCharge D → ℂ) :
    (∑ b, f b * (k * g b)) = k * ∑ b, f b * g b := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => by ring

/-- Both native Laurent Fourier identities after cancelling the explicit
half-coordinate scales of all four homogeneous oscillator words. -/
theorem native_laurent_crossing {X : Type*} [Fintype X] [DecidableEq X]
    (D : LatticeData) (hu : IsUnit D.G.det) (hD : (gramReal D).PosDef)
    (h24 : D.rank = 24) (slot : X → Puncture) (colour : X → Fin D.rank)
    (n : X → ℕ) (l : List X) (hl : l.Nodup)
    (e : Puncture → ℕ) (g : Puncture → ActualGround D hu) (hg : ∀ i, g i ≠ 0)
    (he : ∀ i, actualTensorL0 D hu (wordAt D slot colour n l i ⊗ₜ[ℂ] g i) =
      (e i : ℂ) • (wordAt D slot colour n l i ⊗ₜ[ℂ] g i))
    (s : ℤ) (hmode : (e .S : ℤ) = e .P + e .Q + e .R - s - 2)
    {x : ℝ} (hx : 1 / 2 < x) (hx₁ : x < 1) (a : ModTwoCharge D) :
    let W := wordAt D slot colour n l
    let V := fun c b =>
      nativeLaurent D c (e .P) (e .Q) (e .R) (e .S) s (W .P) (W .Q) (W .R) (W .S) b
        (parameter c (x : ℂ))
    V .D a = ((2 : ℂ) ^ (12 : ℕ))⁻¹ * (∑ b, fourierSign D a b * V .A b) ∧
    (x : ℂ) ^ (s + 2) * V .B a =
      ((2 : ℂ) ^ (12 : ℕ))⁻¹ * ∑ b, fourierSign D a b * quadraticSign D b * V .A b := by
  let W := wordAt D slot colour n l
  let V c b := nativeLaurent D c (e .P) (e .Q) (e .R) (e .S) s (W .P) (W .Q) (W .R) (W .S) b
    (parameter c (x : ℂ))
  let w := Complex.sqrt (parameter .A (x : ℂ))
  have hwA : w ^ 2 = parameter .A (x : ℂ) :=
    Complex.cpow_nat_inv_pow _ (by decide : (2 : ℕ) ≠ 0)
  have hw : ‖w‖ < 1 := by
    have h : ‖w‖ ^ 2 < 1 := by rw [← norm_pow, hwA]; exact chartA_radius hx hx₁
    nlinarith [norm_nonneg w]
  have hx₀ : 0 < x := by linarith
  have hX : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx₀.ne'
  have hY : 1 - (x : ℂ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hx₁.ne')
  let k := channelFactor .A x s
  let p := (periodRoot .A x ^ (12 : ℕ))⁻¹
  have hk : k ≠ 0 := mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero)
    (pow_ne_zero _ hY)) (zpow_ne_zero _ hX)
  have hp : p = (x : ℂ) ^ (6 : ℤ) := by
    have hroot : periodRoot .A x ^ 2 = (x : ℂ)⁻¹ := by
      have h := (chosen_roots hx₀ hx₁ .A .P).2
      change periodRoot .A x ^ 2 = 1 - (1 - (x : ℂ)⁻¹) at h
      simpa only [sub_sub_cancel] using h
    change (periodRoot .A x ^ (12 : ℕ))⁻¹ = (x : ℂ) ^ (6 : ℤ)
    rw [show (12 : ℕ) = 2 * 6 by decide, pow_mul, hroot, inv_pow, inv_inv] <;> rfl
  have hp₀ : p ≠ 0 := by rw [hp]; exact zpow_ne_zero _ hX
  have hB : channelFactor .B x s = (p * k) * (x : ℂ) ^ (s + 2) := by
    rw [hp]
    change _ = (x : ℂ) ^ (6 : ℤ) *
      (-Complex.I * (1 - (x : ℂ)) ^ (3 : ℕ) * (x : ℂ) ^ (-s - 5)) * (x : ℂ) ^ (s + 2)
    calc
      _ = (-Complex.I * (1 - (x : ℂ)) ^ (3 : ℕ)) *
          (((x : ℂ) ^ (6 : ℤ) * (x : ℂ) ^ (-s - 5)) * (x : ℂ) ^ (s + 2)) := by
        rw [← zpow_add₀ hX, ← zpow_add₀ hX]
        rw [show (6 : ℤ) + (-s - 5) + (s + 2) = 3 by ring]
        rfl
      _ = _ := by ring
  have h := native_laurent_fourier_overlap D hu hD h24 slot colour n l hl e g hg he
    s hmode hx₀ hx₁ hwA hw a
  let F c b :=
    ((1 - parameter c (x : ℂ)) ^ (3 : ℕ) *
      (l.map fun j => liftedScale c x (slot j) (n j)).prod) *
      ((-parameter c (x : ℂ)) ^ laurentPower (e .P) (e .Q) (e .R) c *
        laurentPhase (e .Q) (e .R) s c * V c b)
  have hn (c : Chart) (b : ModTwoCharge D) : F c b = channelFactor c x s * V c b := by
    dsimp only [F]
    rw [← mul_assoc, word_laurent_normalization D hu h24 slot colour n l e g hg he s hmode c hx₀ hx₁]
  change (F .D a = _ * ∑ b, fourierSign D a b * F .A b) ∧
    (F .B a = p * (_ * ∑ b, fourierSign D a b * quadraticSign D b * F .A b)) at h
  simp only [hn] at h
  dsimp only
  constructor
  · apply mul_left_cancel₀ hk
    have hd : k * V .D a =
        ((2 : ℂ) ^ (12 : ℕ))⁻¹ * ∑ b, fourierSign D a b * (k * V .A b) := h.1
    rw [fourier_factor D k (fourierSign D a) (V .A)] at hd
    calc
      k * V .D a = _ := hd
      _ = _ := by ring
  · apply mul_left_cancel₀ (mul_ne_zero hp₀ hk)
    have hb : channelFactor .B x s * V .B a =
        p * (((2 : ℂ) ^ (12 : ℕ))⁻¹ * ∑ b,
          fourierSign D a b * quadraticSign D b * (k * V .A b)) := h.2
    rw [hB, fourier_factor D k (fun b => fourierSign D a b * quadraticSign D b) (V .A)] at hb
    calc
      _ = ((p * k) * (x : ℂ) ^ (s + 2)) * V .B a := by ring
      _ = _ := hb
      _ = _ := by ring

open Filter Set
open OriginalFourMChargeCoset (slitChannelD slit_AD_overlap identityK identityK_of_slitChart_crossing)
open OriginalFourPointChartGluing (U_A U_D)
open D5.S3.Analytic.OriginalHalfBinomialSlitPeriod (doubleSlit)
open private translated_gauss_sum fourierSign_swap from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMDFourCurrent

/-- The actual signed channels agree on the real A/B and true A/D overlaps
for arbitrary integer-weight oscillator words at the selected output mode. -/
theorem occupation_word_real_crossing {X : Type*} [Fintype X] [DecidableEq X]
    (D : LatticeData) (hu : IsUnit D.G.det) (hD : (gramReal D).PosDef)
    (h24 : D.rank = 24) (slot : X → Puncture) (colour : X → Fin D.rank)
    (n : X → ℕ) (l : List X) (hl : l.Nodup)
    (e : Puncture → ℕ) (g : Puncture → ActualGround D hu) (hg : ∀ i, g i ≠ 0)
    (he : ∀ i, actualTensorL0 D hu (wordAt D slot colour n l i ⊗ₜ[ℂ] g i) =
      (e i : ℂ) • (wordAt D slot colour n l i ⊗ₜ[ℂ] g i))
    (m n₀ r : ℤ) (hmode : (e .S : ℤ) = e .P + e .Q + e .R - (m + n₀ + r) - 2)
    {x : ℝ} (hx : 1 / 2 < x) (hx₁ : x < 1) (b : ModTwoCharge D) :
    let W := wordAt D slot colour n l
    let A := slitChannelA D (e .P) (e .Q) (m + n₀ + r) (W .P) (W .Q) (W .R) (W .S)
      b (parameter .A (x : ℂ))
    A = (2 : ℂ) ^ (12 : ℕ) * (x : ℂ) ^ (m + n₀ + r + 2) *
      slitChannelB D (e .P) (e .Q) (e .R) m n₀ r (W .P) (W .Q) (W .R) (W .S)
        b (parameter .B (x : ℂ)) ∧
    A = dLipChannel D true (e .P) (e .Q) (e .R) m n₀ r (W .P) (W .Q) (W .R) (W .S)
      b (parameter .D (x : ℂ)) := by
  let W := wordAt D slot colour n l
  let s := m + n₀ + r
  let V c a := nativeLaurent D c (e .P) (e .Q) (e .R) (e .S) s (W .P) (W .Q) (W .R) (W .S)
    a (parameter c (x : ℂ))
  let T : ℂ := (2 : ℂ) ^ (12 : ℕ)
  have hT : T ≠ 0 := pow_ne_zero _ (by norm_num)
  have h (a : ModTwoCharge D) :
      V .D a = T⁻¹ * (∑ c, fourierSign D a c * V .A c) ∧
      (x : ℂ) ^ (s + 2) * V .B a =
        T⁻¹ * ∑ c, fourierSign D a c * quadraticSign D c * V .A c :=
    native_laurent_crossing D hu hD h24 slot colour n l hl e g hg he s hmode hx hx₁ a
  have hB : V .B b = slitChannelB D (e .P) (e .Q) (e .R) m n₀ r
      (W .P) (W .Q) (W .R) (W .S) b (parameter .B (x : ℂ)) :=
    (nativeLaurent_eq_transported_channels D (e .P) (e .Q) (e .R) (e .S) m n₀ r hmode
      (W .P) (W .Q) (W .R) (W .S) b (parameter .B (x : ℂ))).1
  have hD' : (∑ a, quadraticSign D (a + b) * V .D a) =
      dLipChannel D true (e .P) (e .Q) (e .R) m n₀ r
        (W .P) (W .Q) (W .R) (W .S) b (parameter .D (x : ℂ)) :=
    (nativeLaurent_eq_transported_channels D (e .P) (e .Q) (e .R) (e .S) m n₀ r hmode
      (W .P) (W .Q) (W .R) (W .S) b (parameter .D (x : ℂ))).2
  change ((∑ c, quadraticSign D c * fourierSign D c b * V .A c) = _) ∧
    ((∑ c, quadraticSign D c * fourierSign D c b * V .A c) = _)
  constructor
  · rw [← hB, mul_assoc, (h b).2, ← mul_assoc, mul_inv_cancel₀ hT, one_mul]
    exact Finset.sum_congr rfl fun c _ => by
      rw [fourierSign_swap D b c]
      ring
  · rw [← hD']
    symm
    calc
      _ = T⁻¹ * (∑ a, ∑ c, (quadraticSign D (a + b) * fourierSign D a c) * V .A c) := by
        simp only [fun a => (h a).1, Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => by ring
      _ = _ := by
        rw [Finset.sum_comm, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro c _
        rw [← Finset.sum_mul, translated_gauss_sum D hu h24 b c]
        calc
          _ = (T⁻¹ * T) * (quadraticSign D c * fourierSign D c b * V .A c) := by
            dsimp only [T]
            ring
          _ = _ := by rw [inv_mul_cancel₀ hT, one_mul]

/-- The original three-channel identity at arbitrary occupation words of
integer tensor weights in a positive unimodular rank-24 lattice. -/
theorem occupation_word_identityK {X : Type*} [Fintype X] [DecidableEq X]
    (D : LatticeData) (hu : IsUnit D.G.det) (hD : (gramReal D).PosDef)
    (h24 : D.rank = 24) (slot : X → Puncture) (colour : X → Fin D.rank)
    (n : X → ℕ) (l : List X) (hl : l.Nodup)
    (e : Puncture → ℕ) (g : Puncture → ActualGround D hu) (hg : ∀ i, g i ≠ 0)
    (he : ∀ i, actualTensorL0 D hu (wordAt D slot colour n l i ⊗ₜ[ℂ] g i) =
      (e i : ℂ) • (wordAt D slot colour n l i ⊗ₜ[ℂ] g i))
    (m n₀ r : ℤ) (hmode : (e .S : ℤ) = e .P + e .Q + e .R - (m + n₀ + r) - 2) :
    let W := wordAt D slot colour n l
    identityK D hu (e .P) (e .Q) (e .R) m n₀ r (W .P) (W .Q) (W .R) (W .S) := by
  dsimp only
  apply identityK_of_slitChart_crossing D hu hD h24
  intro b
  dsimp only
  let W := wordAt D slot colour n l
  let A := slitChannelA D (e .P) (e .Q) (m + n₀ + r) (W .P) (W .Q) (W .R) (W .S) b
  let B := slitChannelB D (e .P) (e .Q) (e .R) m n₀ r (W .P) (W .Q) (W .R) (W .S) b
  let C := slitChannelD D (e .P) (e .Q) (e .R) m n₀ r (W .P) (W .Q) (W .R) (W .S) b
  let x : ℝ := 3 / 4
  have hx : 1 / 2 < x := by norm_num [x]
  have hx₁ : x < 1 := by norm_num [x]
  have hreal := fun {z : ℝ} (hz : 1 / 2 < z) (hz₁ : z < 1) =>
    occupation_word_real_crossing D hu hD h24 slot colour n l hl e g hg he m n₀ r hmode hz hz₁ b
  have hAD : ∃ y ∈ U_A ∩ U_D, ∀ᶠ z in 𝓝 y, A (parameter .A z) = C (parameter .D z) := by
    apply slit_AD_overlap D hD true (e .P) (e .Q) (e .R) m n₀ r (W .P) (W .Q) (W .R) (W .S) b
      (t := 4 / 3) (by norm_num)
    filter_upwards [lt_mem_nhds (show (1 : ℝ) < 4 / 3 by norm_num),
      gt_mem_nhds (show (4 / 3 : ℝ) < 2 by norm_num)] with t ht₁ ht₂
    have ht₀ : 0 < t := zero_lt_one.trans ht₁
    have ht : 1 / 2 < t⁻¹ := by
      rw [← one_div t]
      apply (lt_div_iff₀ ht₀).2
      linarith
    have ht' : t⁻¹ < 1 := (inv_lt_one₀ ht₀).2 ht₁
    simpa only [parameter, Complex.ofReal_inv, inv_inv] using (hreal ht ht').2
  obtain ⟨y, hy, hyGerm⟩ := hAD
  have hxSlit : (x : ℂ) ∈ doubleSlit := by
    refine ⟨?_, Complex.ofReal_mem_slitPlane.mpr (by norm_num [x])⟩
    change 1 - (x : ℂ) ∈ Complex.slitPlane
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub]
    exact Complex.ofReal_mem_slitPlane.mpr (sub_pos.mpr hx₁)
  have hCast : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[≠] x) (𝓝[≠] (x : ℂ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simpa only [mem_compl_iff, mem_singleton_iff, Complex.ofReal_inj] using ht
  refine ⟨(x : ℂ), y, hxSlit, hCast.frequently ?_, Or.inl ⟨hy, ?_⟩⟩
  · apply Filter.Eventually.frequently
    filter_upwards [(lt_mem_nhds hx).filter_mono nhdsWithin_le_nhds,
      (gt_mem_nhds hx₁).filter_mono nhdsWithin_le_nhds] with t ht ht₁
    exact (hreal ht ht₁).1
  · exact (hyGerm.filter_mono nhdsWithin_le_nhds).frequently

private theorem word_of_occupation (D : LatticeData) (b : Exponent D) :
    oscillatorWord D b.toMultiset.toList = MvPolynomial.monomial b 1 := by
  classical
  have hc (L : List (Index D)) (a : Index D) :
      jetOccupation L a = (L : Multiset (Index D)).count a := by
    induction L with
    | nil => simp [jetOccupation]
    | cons i L ih =>
      by_cases h : i = a
      · subst i
        simp [jetOccupation, ih, Multiset.coe_count]
      · simp [jetOccupation, ih, Finsupp.single_apply, h, Ne.symm h, Multiset.coe_count]
  have he : jetOccupation b.toMultiset.toList = b := by
    ext a
    rw [hc, Multiset.coe_toList, Finsupp.count_toMultiset]
  rw [word_monomial, he]

/-- The actual three-channel identity on arbitrary Fock occupation monomials
at the homogeneous signed-mode diagonal. Occupation multiplicities are used
only to choose finite distinct marks for the four oscillator words. -/
theorem arbitrary_occupation_identityK (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : (gramReal D).PosDef) (h24 : D.rank = 24) (b : Puncture → Exponent D)
    (e : Puncture → ℕ) (g : Puncture → ActualGround D hu) (hg : ∀ i, g i ≠ 0)
    (he : ∀ i, actualTensorL0 D hu (MvPolynomial.monomial (b i) 1 ⊗ₜ[ℂ] g i) =
      (e i : ℂ) • (MvPolynomial.monomial (b i) 1 ⊗ₜ[ℂ] g i))
    (m n r : ℤ) (hmode : (e .S : ℤ) = e .P + e .Q + e .R - (m + n + r) - 2) :
    identityK D hu (e .P) (e .Q) (e .R) m n r
      (MvPolynomial.monomial (b .P) 1) (MvPolynomial.monomial (b .Q) 1)
      (MvPolynomial.monomial (b .R) 1) (MvPolynomial.monomial (b .S) 1) := by
  classical
  let L (i : Puncture) := (b i).toMultiset.toList
  let block (i : Puncture) := (L i).map fun a => (i, a)
  let marks := block .P ++ block .Q ++ block .R ++ block .S
  let label : Fin marks.length → Puncture × Index D := marks.get
  let p (j : Fin marks.length) := (label j).1
  let c (j : Fin marks.length) := (label j).2.1
  let k (j : Fin marks.length) := (label j).2.2
  let l := List.finRange marks.length
  have hblock (i j : Puncture) :
      (((block i).filter fun a => decide (a.1 = j)).map Prod.snd) =
        if i = j then L i else [] := by
    by_cases hij : i = j <;> simp [block, List.filter_map, List.map_map, Function.comp_def, hij]
  have hmarks (i : Puncture) :
      ((marks.filter fun a => decide (a.1 = i)).map Prod.snd) = L i := by
    dsimp only [marks]
    simp only [List.filter_append, List.map_append, hblock]
    cases i <;> simp
  have hW (i : Puncture) : wordAt D p c k l i = MvPolynomial.monomial (b i) 1 := by
    unfold wordAt
    rw [← word_of_occupation D (b i)]
    apply congrArg (oscillatorWord D)
    calc
      _ = (((l.filter fun a => decide (p a = i)).map label).map Prod.snd) := by
        rw [List.map_map]
        rfl
      _ = _ := by
        have hmap : l.map label = marks := List.map_get_finRange marks
        rw [show ((l.filter fun a => decide (p a = i)).map label) =
            ((l.map label).filter fun a => decide (a.1 = i)) by
          rw [List.filter_map]
          rfl, hmap]
        exact hmarks i
  have he' (i : Puncture) :
      actualTensorL0 D hu (wordAt D p c k l i ⊗ₜ[ℂ] g i) =
        (e i : ℂ) • (wordAt D p c k l i ⊗ₜ[ℂ] g i) := by
    rw [hW i]
    exact he i
  have h := occupation_word_identityK D hu hD h24 p c k l (List.nodup_finRange _) e g hg he'
    m n r hmode
  simpa only [hW] using h

end D5.S3.VertexAlgebra.TwistedGround.OriginalFourMVariableSupport
