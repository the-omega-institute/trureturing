import D5.S3.VertexAlgebra.TwistedGround.FourPoint.HHBB.NativeHHBBTwoVariableRational
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.BBHH.NativeBBHHNormalizedGerm

/-! Homogenization and literal mode evaluations for the native BBHH channels. -/

set_option autoImplicit false
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators

namespace D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeBBHHTwoVariableRational

open ActualLeechHyperbolic (leechData)
open LatticeHalfFockGradedTrace (actualGrade)
open Orbifold.NativeOddTwistedIntertwiner (TwistedOdd TwistedEven leechUnit)
open Orbifold.NativeMixedPairField (mu_coeff_even_zero)
open Orbifold.NativeFixedPairField (nu nu_coeff_odd_zero)
open Orbifold.NativeOddUpperRightSkew (rightField_even_zero)
open NativeMixedUpperProductCusp (bJointTerm b_inner_coeff_off_grid)
open NativeFixedCrossedProductToIterate (aJointTerm)
open CollisionLaurentKernels.LaurentCollision (Bivariate Rational)
open NativeHHBBTwoVariableRational (homogenizedNumerator evalAt evalAt_homogenizedNumerator)

open private evalAt_homogenizedNumerator_div scale_modes from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.HHBB.NativeHHBBTwoVariableRational
open private b_inner_energy b_outer_pairing_off_grid from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedUpperProductCusp
open private fixed_a_off_diagonal fixed_odd_mode_zero aJointTerm_neg_outer_root from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeFixedCrossedProductToIterate
open private sqrt_square zpow_double from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedComplexSewing

local notation "ℒ" => leechData
local notation "xPoly" => (Polynomial.C (Polynomial.X : Polynomial ℂ))
local notation "zPoly" => (Polynomial.X : Bivariate ℂ)

def zeroPole (H K : ℕ) : ℕ := (5 + H + K) / 2
def swapPole (M K : ℕ) : ℕ := (5 + M + K) / 2
def collisionPole (M H : ℕ) : ℕ := (M + H + 6) / 2

def doubledDegree (M K H J : ℕ) : ℤ := (J : ℤ) - M - H - K - 6

def normalizedDegree (M K H J : ℕ) : ℤ := ((J : ℤ) - M - H - K - 4) / 2

def numeratorDegree (M K H J : ℕ) : ℕ :=
  ((zeroPole H K : ℤ) + collisionPole M H + (1 + (J : ℤ) - H) / 2).toNat

theorem degree_balance {M K H J : ℕ}
    (hM : Odd M) (hK : Even K) (hH : Odd H) (hJ : Even J) :
    doubledDegree M K H J + 2 = 2 * normalizedDegree M K H J ∧
      (numeratorDegree M K H J : ℤ) =
        normalizedDegree M K H J + swapPole M K + zeroPole H K + collisionPole M H := by
  have hm := Nat.odd_iff.mp hM
  have hk := Nat.even_iff.mp hK
  have hh := Nat.odd_iff.mp hH
  have hj := Nat.even_iff.mp hJ
  unfold numeratorDegree normalizedDegree doubledDegree swapPole zeroPole collisionPole
  push_cast
  omega

/-- Each denominator exponent involves only the source grades. -/
def denominator (M K H : ℕ) : Bivariate ℂ :=
  xPoly ^ swapPole M K * zPoly ^ zeroPole H K * (xPoly - zPoly) ^ collisionPole M H

def commonRational (p : Polynomial ℂ) (M K H J : ℕ) : Rational ℂ :=
  algebraMap (Bivariate ℂ) (Rational ℂ) (homogenizedNumerator p (numeratorDegree M K H J)) /
    algebraMap (Bivariate ℂ) (Rational ℂ) (denominator M K H)

def valueAt (p : Polynomial ℂ) (M K H J : ℕ) (X Z : ℂ) : ℂ :=
  evalAt X Z (homogenizedNumerator p (numeratorDegree M K H J)) /
    evalAt X Z (denominator M K H)

def baseValue (p : Polynomial ℂ) (M K H : ℕ) (y : ℂ) : ℂ :=
  p.eval y / (y ^ zeroPole H K * (1 - y) ^ collisionPole M H)

theorem evalAt_denominator (M K H : ℕ) (X Z : ℂ) :
    evalAt X Z (denominator M K H) =
      X ^ swapPole M K * Z ^ zeroPole H K * (X - Z) ^ collisionPole M H := by
  simp only [denominator, evalAt, map_mul, map_pow, map_sub,
    Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, Polynomial.eval₂_X,
    Polynomial.coe_evalRingHom, Polynomial.eval_X]

theorem evalAt_denominator_ne_zero (M K H : ℕ) {X Z : ℂ}
    (hX : X ≠ 0) (hZ : Z ≠ 0) (hXZ : X ≠ Z) :
    evalAt X Z (denominator M K H) ≠ 0 := by
  rw [evalAt_denominator]
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hX) (pow_ne_zero _ hZ))
    (pow_ne_zero _ (sub_ne_zero.mpr hXZ))

theorem commonRational_mul_denominator (p : Polynomial ℂ) (M K H J : ℕ) :
    commonRational p M K H J * algebraMap (Bivariate ℂ) (Rational ℂ) (denominator M K H) =
      algebraMap (Bivariate ℂ) (Rational ℂ) (homogenizedNumerator p (numeratorDegree M K H J)) := by
  have hden : denominator M K H ≠ 0 := by
    intro h
    exact evalAt_denominator_ne_zero M K H (X := 1) (Z := 2)
      (by norm_num) (by norm_num) (by norm_num) (by rw [h, map_zero])
  unfold commonRational
  apply div_mul_cancel₀
  simpa only [map_zero] using (IsFractionRing.injective (Bivariate ℂ) (Rational ℂ)).ne hden

theorem evaluate_homogeneous (p : Polynomial ℂ) {M K H J : ℕ}
    (hM : Odd M) (hK : Even K) (hH : Odd H) (hJ : Even J)
    (hp : p.natDegree ≤ numeratorDegree M K H J) {X Z : ℂ}
    (hX : X ≠ 0) (hZ : Z ≠ 0) (hXZ : X ≠ Z) :
    X ^ normalizedDegree M K H J * baseValue p M K H (Z / X) =
      valueAt p M K H J X Z := by
  unfold baseValue valueAt
  rw [evalAt_homogenizedNumerator_div p hp hX, evalAt_denominator]
  have hy : 1 - Z / X = (X - Z) / X := by rw [sub_div, div_self hX]
  have hpow : X ^ (normalizedDegree M K H J) * X ^ swapPole M K *
      X ^ zeroPole H K * X ^ collisionPole M H = X ^ numeratorDegree M K H J := by
    rw [← zpow_natCast X (swapPole M K), ← zpow_natCast X (zeroPole H K),
      ← zpow_natCast X (collisionPole M H), ← zpow_natCast X (numeratorDegree M K H J)]
    rw [← zpow_add₀ hX, ← zpow_add₀ hX, ← zpow_add₀ hX, (degree_balance hM hK hH hJ).2]
  rw [← hpow, hy, div_pow, div_pow]
  have ha := pow_ne_zero (zeroPole H K) hZ
  have hb := pow_ne_zero (collisionPole M H) (sub_ne_zero.mpr hXZ)
  field_simp [pow_ne_zero (zeroPole H K) hX, pow_ne_zero (collisionPole M H) hX,
    pow_ne_zero (swapPole M K) hX]

section Modes

variable {M K H J : ℕ} {P R : TwistedOdd} {Q S : TwistedEven}
variable (hP : P.val ∈ actualGrade ℒ leechUnit M) (hQ : Q.val ∈ actualGrade ℒ leechUnit K)
variable (hR : R.val ∈ actualGrade ℒ leechUnit H) (hS : S.val ∈ actualGrade ℒ leechUnit J)

include hP hQ hR hS

/-- The bare ordered product is supported in the total doubled degree.
Interchanging the odd sources gives the reversed product support. -/
theorem bJointTerm_off_total (hHK : Odd ((H : ℤ) + K)) (x z : ℂ)
    (i : ℤ × ℤ) (hi : i.1 + i.2 ≠ doubledDegree M K H J) :
    bJointTerm true true R Q P S x z i = 0 := by
  rcases i with ⟨j, e⟩
  by_cases hj : ∃ E : ℕ, j = 2 * (E : ℤ) - (6 + (H : ℤ) + K)
  · obtain ⟨E, rfl⟩ := hj
    have he : e ≠ (J : ℤ) - M - 2 * (E : ℤ) := by
      intro he
      apply hi
      simp only [doubledDegree, he]
      ring
    rw [bJointTerm, b_outer_pairing_off_grid true M J E P S hP hS _
      (b_inner_energy true H K E R Q hR hQ hHK) e he, zero_mul]
  · have hm := b_inner_coeff_off_grid true H K R Q hR hQ hHK j (fun E h => hj ⟨E, h⟩)
    simp [bJointTerm, hm]

/-- The bare fixed-pair iterate has the same total doubled degree. -/
theorem aJointTerm_off_total (hMH : Even ((M : ℤ) + H)) (d z : ℂ)
    (i : ℤ × ℤ) (hi : i.1 + i.2 ≠ doubledDegree M K H J) :
    aJointTerm true false P R Q S d z i = 0 := by
  rcases i with ⟨j, e⟩
  have he : e ≠ (J : ℤ) - K - (j + ((M : ℤ) + H + 6)) := by
    intro he
    apply hi
    simp only [doubledDegree, he]
    ring
  rw [aJointTerm, fixed_a_off_diagonal true false M H K J P R Q S
    hP hR hQ hS hMH j e he, zero_mul]

private theorem b_scale (hHK : Odd ((H : ℤ) + K)) {c : ℂ}
    (hc : c ≠ 0) (x z : ℂ) (i : ℤ × ℤ) :
    bJointTerm true true R Q P S (c * x) (c * z) i =
      c ^ doubledDegree M K H J * bJointTerm true true R Q P S x z i := by
  by_cases hi : i.1 + i.2 = doubledDegree M K H J
  · simp only [bJointTerm, scale_modes hc z x hi]
    ring
  · rw [bJointTerm_off_total hP hQ hR hS hHK _ _ i hi,
      bJointTerm_off_total hP hQ hR hS hHK _ _ i hi, mul_zero]

private theorem a_scale (hMH : Even ((M : ℤ) + H)) {c : ℂ}
    (hc : c ≠ 0) (d z : ℂ) (i : ℤ × ℤ) :
    aJointTerm true false P R Q S (c * d) (c * z) i =
      c ^ doubledDegree M K H J * aJointTerm true false P R Q S d z i := by
  by_cases hi : i.1 + i.2 = doubledDegree M K H J
  · simp only [aJointTerm, scale_modes hc d z hi]
    ring
  · rw [aJointTerm_off_total hP hQ hR hS hMH _ _ i hi,
      aJointTerm_off_total hP hQ hR hS hMH _ _ i hi, mul_zero]

omit hP hQ hR hS

/-- The raw B products use only odd doubled mode indices in both roots. -/
theorem bJointTerm_off_parity (x z : ℂ) (i : ℤ × ℤ) (hi : Even i.1 ∨ Even i.2) :
    bJointTerm true true R Q P S x z i = 0 := by
  rcases hi with hi | hi
  · simp [bJointTerm, mu_coeff_even_zero true i.1 R Q hi]
  · simp [bJointTerm, rightField_even_zero ℒ leechUnit true i.2 hi]

/-- The fixed-pair iterate uses only even doubled mode indices in both roots. -/
theorem aJointTerm_off_parity (d z : ℂ) (i : ℤ × ℤ) (hi : Odd i.1 ∨ Odd i.2) :
    aJointTerm true false P R Q S d z i = 0 := by
  rcases hi with hi | hi
  · simp [aJointTerm, nu_coeff_odd_zero true i.1 P R hi]
  · rw [aJointTerm, fixed_odd_mode_zero ((nu true P).coeff i.1 R) i.2 hi Q.val,
      map_zero, zero_mul]

private theorem b_neg_inner (x z : ℂ) (i : ℤ × ℤ) :
    bJointTerm true true R Q P S x (-z) i = -bJointTerm true true R Q P S x z i := by
  by_cases he : Even i.1
  · rw [bJointTerm_off_parity _ _ i (Or.inl he), bJointTerm_off_parity _ _ i (Or.inl he), neg_zero]
  · simp only [bJointTerm, (Int.not_even_iff_odd.mp he).neg_zpow, neg_mul, mul_neg]

private theorem b_neg_outer (x z : ℂ) (i : ℤ × ℤ) :
    bJointTerm true true R Q P S (-x) z i = -bJointTerm true true R Q P S x z i := by
  by_cases he : Even i.2
  · rw [bJointTerm_off_parity _ _ i (Or.inr he), bJointTerm_off_parity _ _ i (Or.inr he), neg_zero]
  · simp only [bJointTerm, (Int.not_even_iff_odd.mp he).neg_zpow, mul_neg]

private theorem a_neg_collision (d z : ℂ) (i : ℤ × ℤ) :
    aJointTerm true false P R Q S (-d) z i = aJointTerm true false P R Q S d z i := by
  by_cases he : Even i.1
  · simp only [aJointTerm, he.neg_zpow]
  · have ho := Int.not_even_iff_odd.mp he
    rw [aJointTerm_off_parity _ _ i (Or.inl ho), aJointTerm_off_parity _ _ i (Or.inl ho)]

end Modes

/-- The explicit one-variable polynomial input on the literal native channels. -/
structure OneVariableChannels (p : Polynomial ℂ) (M K H : ℕ)
    (P R : TwistedOdd) (Q S : TwistedEven) : Prop where
  ordered : ∀ y ∈ Metric.ball (0 : ℂ) 1, y ≠ 0 →
    HasSum (fun i => Complex.sqrt y * bJointTerm true true R Q P S 1 (Complex.sqrt y) i)
      (-baseValue p M K H y)
  collision : ∀ y : ℂ, (1 / 2 : ℝ) < y.re → y ≠ 1 →
    HasSum (fun i => Complex.sqrt y *
      aJointTerm true false P R Q S (Complex.sqrt (1 - y)) (Complex.sqrt y) i)
      (baseValue p M K H y)
  reversed : ∀ y : ℂ, 1 < ‖y‖ →
    HasSum (fun i => Complex.sqrt y * bJointTerm true true P Q R S (Complex.sqrt y) 1 i)
      (-baseValue p M K H y)

/-- Physical-coordinate evaluations. The product root factors absorb both odd
mode signs. The iterate factor uses the selected B sheet at the same coordinates. -/
def TwoVariableChannels (p : Polynomial ℂ) (M K H J : ℕ)
    (P R : TwistedOdd) (Q S : TwistedEven) : Prop :=
  ∀ X Z : ℂ, X ≠ 0 → Z ≠ 0 → X ≠ Z →
    let y := Z / X
    let value := valueAt p M K H J X Z
    evalAt X Z (denominator M K H) ≠ 0 ∧
    X ^ normalizedDegree M K H J * baseValue p M K H y = value ∧
    ∀ xRoot zRoot : ℂ, xRoot ^ (2 : ℕ) = X → zRoot ^ (2 : ℕ) = Z →
      (y ∈ Metric.ball (0 : ℂ) 1 →
        HasSum (fun i => (xRoot * zRoot) * bJointTerm true true R Q P S xRoot zRoot i)
          (-value)) ∧
      (∀ dRoot : ℂ, dRoot ^ (2 : ℕ) = X - Z → (1 / 2 : ℝ) < y.re →
        HasSum (fun i => (X * Complex.sqrt y) *
          aJointTerm true false P R Q S dRoot zRoot i) value) ∧
      (1 < ‖y‖ →
        HasSum (fun i => (xRoot * zRoot) * bJointTerm true true P Q R S zRoot xRoot i)
          (-value))

/-- On the selected B sheet the iterate uses the same factor as both products. -/
theorem selectedSheet_normalizer {X Z xRoot zRoot : ℂ}
    (hx : xRoot ^ (2 : ℕ) = X) (hs : zRoot = xRoot * Complex.sqrt (Z / X)) :
    X * Complex.sqrt (Z / X) = xRoot * zRoot := by
  rw [hs, ← hx, pow_two, mul_assoc]

set_option maxHeartbeats 2000000 in
/-- Transfer the three analytic one-variable sums to physical coordinates.
The bare mode support and the separate root parity identities justify every
simultaneous nonzero scale and both lifts of each physical root. -/
theorem bbhh_two_variable_of_polynomial {M K H J : ℕ} {p : Polynomial ℂ}
    {P R : TwistedOdd} {Q S : TwistedEven}
    (hP : P.val ∈ actualGrade ℒ leechUnit M) (hQ : Q.val ∈ actualGrade ℒ leechUnit K)
    (hR : R.val ∈ actualGrade ℒ leechUnit H) (hS : S.val ∈ actualGrade ℒ leechUnit J)
    (hM : Odd M) (hK : Even K) (hH : Odd H) (hJ : Even J)
    (hp : p.natDegree ≤ numeratorDegree M K H J)
    (hchannels : OneVariableChannels p M K H P R Q S) :
    TwoVariableChannels p M K H J P R Q S := by
  intro X Z hX hZ hXZ y value
  have hy₀ : y ≠ 0 := div_ne_zero hZ hX
  have hy₁ : y ≠ 1 := fun h => hXZ (((div_eq_iff hX).mp h).trans (one_mul X)).symm
  have heval : X ^ normalizedDegree M K H J * baseValue p M K H y = value :=
    evaluate_homogeneous p hM hK hH hJ hp hX hZ hXZ
  refine ⟨evalAt_denominator_ne_zero M K H hX hZ hXZ, heval, ?_⟩
  intro xRoot zRoot hx hz
  have hx₀ : xRoot ≠ 0 := fun h => hX (by simpa [h] using hx.symm)
  let zBase := xRoot * Complex.sqrt y
  let dBase := xRoot * Complex.sqrt (1 - y)
  have hzBase : zBase ^ (2 : ℕ) = Z := by
    dsimp only [zBase, y]
    rw [mul_pow, hx, sqrt_square]
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ hX]
  have hdBase : dBase ^ (2 : ℕ) = X - Z := by
    dsimp only [dBase, y]
    rw [mul_pow, hx, sqrt_square, mul_sub, mul_one]
    congr 1
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ hX]
  have hZlift := eq_or_eq_neg_of_sq_eq_sq zRoot zBase (hz.trans hzBase.symm)
  have hpow : X * xRoot ^ doubledDegree M K H J = X ^ normalizedDegree M K H J := by
    calc
      X * xRoot ^ doubledDegree M K H J = xRoot ^ (2 + doubledDegree M K H J) := by
        rw [zpow_add₀ hx₀, ← hx]
        rfl
      _ = X ^ normalizedDegree M K H J := by
        rw [add_comm (2 : ℤ), (degree_balance hM hK hH hJ).1, zpow_double, hx]
  have hMH : Even ((M : ℤ) + H) := Int.even_iff.mpr
    (by have := Nat.odd_iff.mp hM; have := Nat.odd_iff.mp hH; omega)
  have hHK : Odd ((H : ℤ) + K) := Int.odd_iff.mpr
    (by have := Nat.odd_iff.mp hH; have := Nat.even_iff.mp hK; omega)
  have hMK : Odd ((M : ℤ) + K) := Int.odd_iff.mpr
    (by have := Nat.odd_iff.mp hM; have := Nat.even_iff.mp hK; omega)
  have hswap : doubledDegree H K M J = doubledDegree M K H J := by
    unfold doubledDegree
    ring
  have hfactor : xRoot * zBase = X * Complex.sqrt y :=
    (selectedSheet_normalizer hx rfl).symm
  refine ⟨?_, ?_, ?_⟩
  · intro hball
    have hs := (hchannels.ordered y hball hy₀).mul_left (X ^ normalizedDegree M K H J)
    rw [mul_neg, heval] at hs
    refine hs.congr_fun fun i => ?_
    have hterm : bJointTerm true true R Q P S xRoot zBase i =
        xRoot ^ doubledDegree M K H J *
          bJointTerm true true R Q P S 1 (Complex.sqrt y) i := by
      simpa only [mul_one, zBase] using b_scale hP hQ hR hS hHK hx₀ 1 (Complex.sqrt y) i
    have hsheet : (xRoot * zRoot) * bJointTerm true true R Q P S xRoot zRoot i =
        (xRoot * zBase) * bJointTerm true true R Q P S xRoot zBase i := by
      rcases hZlift with h | h
      · rw [h]
      · rw [h, b_neg_inner]
        ring
    rw [hsheet, hfactor, hterm, ← hpow]
    ring
  · intro dRoot hd hright
    have hs := (hchannels.collision y hright hy₁).mul_left (X ^ normalizedDegree M K H J)
    rw [heval] at hs
    refine hs.congr_fun fun i => ?_
    have hdlift := eq_or_eq_neg_of_sq_eq_sq dRoot dBase (hd.trans hdBase.symm)
    have hdterm : aJointTerm true false P R Q S dRoot zRoot i =
        aJointTerm true false P R Q S dBase zRoot i := by
      rcases hdlift with h | h
      · rw [h]
      · rw [h, a_neg_collision]
    have hzterm : aJointTerm true false P R Q S dBase zRoot i =
        aJointTerm true false P R Q S dBase zBase i := by
      rcases hZlift with h | h
      · rw [h]
      · rw [h, aJointTerm_neg_outer_root]
    rw [hdterm, hzterm, a_scale hP hQ hR hS hMH hx₀ (Complex.sqrt (1 - y))
      (Complex.sqrt y) i, ← hpow]
    ring
  · intro hrad
    have hs := (hchannels.reversed y hrad).mul_left (X ^ normalizedDegree M K H J)
    rw [mul_neg, heval] at hs
    refine hs.congr_fun fun i => ?_
    have hterm : bJointTerm true true P Q R S zBase xRoot i =
        xRoot ^ doubledDegree M K H J *
          bJointTerm true true P Q R S (Complex.sqrt y) 1 i := by
      simpa only [mul_one, zBase, hswap] using
        b_scale hR hQ hP hS hMK hx₀ (Complex.sqrt y) 1 i
    have hsheet : (xRoot * zRoot) * bJointTerm true true P Q R S zRoot xRoot i =
        (xRoot * zBase) * bJointTerm true true P Q R S zBase xRoot i := by
      rcases hZlift with h | h
      · rw [h]
      · rw [h, b_neg_outer]
        ring
    rw [hsheet, hfactor, hterm, ← hpow]
    ring

open NativeBBHHNormalizedGerm (bbhh_actual_normalized_common_rational)
open NativeMixedUpperProductCusp (bProductCoeff)
open OriginalGaussianSewnAnalytic (coefficient)
open private energySum from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedIterateSlot12Analytic
open private grade_mod_two bModeLinear_apply from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedBProductInversion
open private aModeLinear_apply from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeFixedCrossedProductToIterate

/-- The same finite reversed Taylor numerator as the one-variable theorem. -/
def nativeNumerator (M K H J : ℕ) (P R : TwistedOdd) (Q S : TwistedEven) : Polynomial ℂ :=
  let d := numeratorDegree M K H J
  let G (z : ℂ) := (z - 1) ^ collisionPole M H *
    (-energySum (bProductCoeff true true H M K J P Q R S) z)
  ∑ n ∈ Finset.range (d + 1), Polynomial.C (coefficient n G) * Polynomial.X ^ (d - n)

private theorem b_zero {P R : TwistedOdd} {Q S : TwistedEven}
    (h : P = 0 ∨ Q = 0 ∨ R = 0 ∨ S = 0) (x z : ℂ) (i : ℤ × ℤ) :
    bJointTerm true true R Q P S x z i = 0 := by
  rcases h with h | h | h | h <;> simp [← bModeLinear_apply, h]

private theorem b_zero_reversed {P R : TwistedOdd} {Q S : TwistedEven}
    (h : P = 0 ∨ Q = 0 ∨ R = 0 ∨ S = 0) (x z : ℂ) (i : ℤ × ℤ) :
    bJointTerm true true P Q R S x z i = 0 := by
  rcases h with h | h | h | h <;> simp [← bModeLinear_apply, h]

private theorem a_zero {P R : TwistedOdd} {Q S : TwistedEven}
    (h : P = 0 ∨ Q = 0 ∨ R = 0 ∨ S = 0) (d z : ℂ) (i : ℤ × ℤ) :
    aJointTerm true false P R Q S d z i = 0 := by
  rcases h with h | h | h | h <;> simp [← aModeLinear_apply, h]

private theorem state_grade_parities {M K H J : ℕ}
    {P R : TwistedOdd} {Q S : TwistedEven}
    (hP : P.val ∈ actualGrade ℒ leechUnit M) (hQ : Q.val ∈ actualGrade ℒ leechUnit K)
    (hR : R.val ∈ actualGrade ℒ leechUnit H) (hS : S.val ∈ actualGrade ℒ leechUnit J)
    (hn : ¬ (P = 0 ∨ Q = 0 ∨ R = 0 ∨ S = 0)) :
    Odd M ∧ Even K ∧ Odd H ∧ Even J := by
  push Not at hn
  exact ⟨Nat.odd_iff.mpr (grade_mod_two hP hn.1),
    Nat.even_iff.mpr (grade_mod_two hQ hn.2.1), Nat.odd_iff.mpr (grade_mod_two hR hn.2.2.1),
    Nat.even_iff.mpr (grade_mod_two hS hn.2.2.2)⟩

/-- All three bare mode families vanish off the same doubled-degree diagonal,
including for zero states assigned to any homogeneous grade. -/
theorem bbhh_actual_bare_mode_support (M K H J : ℕ)
    (P R : TwistedOdd) (Q S : TwistedEven)
    (hP : P.val ∈ actualGrade ℒ leechUnit M) (hQ : Q.val ∈ actualGrade ℒ leechUnit K)
    (hR : R.val ∈ actualGrade ℒ leechUnit H) (hS : S.val ∈ actualGrade ℒ leechUnit J)
    (x z d : ℂ) (i : ℤ × ℤ) (hi : i.1 + i.2 ≠ doubledDegree M K H J) :
    bJointTerm true true R Q P S x z i = 0 ∧
    aJointTerm true false P R Q S d z i = 0 ∧
    bJointTerm true true P Q R S z x i = 0 := by
  by_cases h : P = 0 ∨ Q = 0 ∨ R = 0 ∨ S = 0
  · exact ⟨b_zero h x z i, a_zero h d z i, b_zero_reversed h z x i⟩
  obtain ⟨hm, hk, hh, _⟩ := state_grade_parities hP hQ hR hS h
  have hM := Nat.odd_iff.mp hm
  have hK := Nat.even_iff.mp hk
  have hH := Nat.odd_iff.mp hh
  have hswap : doubledDegree H K M J = doubledDegree M K H J := by
    unfold doubledDegree
    ring
  exact ⟨bJointTerm_off_total hP hQ hR hS (Int.odd_iff.mpr (by omega)) x z i hi,
    aJointTerm_off_total hP hQ hR hS (Int.even_iff.mpr (by omega)) d z i hi,
    bJointTerm_off_total hR hQ hP hS (Int.odd_iff.mpr (by omega)) z x i (hswap.symm ▸ hi)⟩

private theorem nativeNumerator_zero (M K H J : ℕ) {P R : TwistedOdd} {Q S : TwistedEven}
    (h : P = 0 ∨ Q = 0 ∨ R = 0 ∨ S = 0) :
    nativeNumerator M K H J P R Q S = 0 := by
  have hcoeff (E : ℕ) : bProductCoeff true true H M K J P Q R S E = 0 := by
    simpa only [bJointTerm, bProductCoeff, one_zpow, mul_one] using
      b_zero_reversed h 1 1 (2 * (E : ℤ) - (6 + (M : ℤ) + K), (J : ℤ) - H - 2 * (E : ℤ))
  simp [nativeNumerator, energySum, hcoeff, coefficient]

set_option maxHeartbeats 1000000 in
/-- The actual BBHH numerator gives one physical rational function on all three
literal mode channels, with detector-independent bounds at X=0, Z=0 and X=Z. -/
theorem bbhh_actual_two_variable_common_rational (M K H J : ℕ)
    (P R : TwistedOdd) (Q S : TwistedEven)
    (hP : P.val ∈ actualGrade ℒ leechUnit M) (hQ : Q.val ∈ actualGrade ℒ leechUnit K)
    (hR : R.val ∈ actualGrade ℒ leechUnit H) (hS : S.val ∈ actualGrade ℒ leechUnit J) :
    let p := nativeNumerator M K H J P R Q S
    p.natDegree ≤ numeratorDegree M K H J ∧
    commonRational p M K H J * algebraMap (Bivariate ℂ) (Rational ℂ) (denominator M K H) =
      algebraMap (Bivariate ℂ) (Rational ℂ) (homogenizedNumerator p (numeratorDegree M K H J)) ∧
    TwoVariableChannels p M K H J P R Q S := by
  intro p
  obtain ⟨hp, _, hB, hA, hD⟩ :=
    bbhh_actual_normalized_common_rational M K H J P R Q S hP hQ hR hS
  refine ⟨hp, commonRational_mul_denominator p M K H J, ?_⟩
  by_cases h : P = 0 ∨ Q = 0 ∨ R = 0 ∨ S = 0
  · have hp₀ : p = 0 := nativeNumerator_zero M K H J h
    have hval (X Z : ℂ) : valueAt p M K H J X Z = 0 := by
      simp [valueAt, evalAt_homogenizedNumerator, hp₀]
    intro X Z hX hZ hXZ
    refine ⟨evalAt_denominator_ne_zero M K H hX hZ hXZ, ?_, ?_⟩
    · rw [hval]
      simp [baseValue, hp₀]
    intro xRoot zRoot _ _
    refine ⟨fun _ => ?_, fun dRoot _ _ => ?_, fun _ => ?_⟩
    · simpa only [hval, b_zero h, mul_zero, neg_zero] using
        (hasSum_zero : HasSum (fun _ : ℤ × ℤ => (0 : ℂ)) 0)
    · simpa only [hval, a_zero h, mul_zero] using
        (hasSum_zero : HasSum (fun _ : ℤ × ℤ => (0 : ℂ)) 0)
    · simpa only [hval, b_zero_reversed h, mul_zero, neg_zero] using
        (hasSum_zero : HasSum (fun _ : ℤ × ℤ => (0 : ℂ)) 0)
  obtain ⟨hM, hK, hH, hJ⟩ := state_grade_parities hP hQ hR hS h
  exact bbhh_two_variable_of_polynomial hP hQ hR hS hM hK hH hJ hp ⟨hB, hA, hD⟩

end D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeBBHHTwoVariableRational
