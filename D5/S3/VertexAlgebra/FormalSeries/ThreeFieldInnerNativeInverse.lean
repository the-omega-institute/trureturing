/- GID: D5/S3/VertexAlgebra/FormalSeries/ThreeFieldInnerNativeInverse
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/FormalSeries/ThreeFieldInnerNativeInverse
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native unit inversion of the exact inner multiplier on signed coefficients. -/
import D5.S3.VertexAlgebra.FormalSeries.ThreeFieldInnerPolynomial
import D5.S3.VertexAlgebra.FormalSeries.ThreeFieldFinalLaurentAction
import Batteries.Tactic.OpenPrivate

/-! All native substitutions concern power series, never unrestricted raw
distributions. The raw coefficient action is proved by finite translations.
The existing native chart and signed monomial identities are reused. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.VertexAlgebra.ThreeFieldInnerNativeInverse
open UniformGradedLocalCorrelator UngradedLocalWordSeries SupportedThreeFieldCollision
open SupportedFinalCovariance SupportedFinalRInjectivity ThreeFieldInnerPolynomial
open ThreeFieldFinalCone
open scoped BigOperators
noncomputable section

open private W shiftedChart chartVariables variable_transport add_transport
  mul_transport pow_transport native_chart_readout from
  D5.S3.VertexAlgebra.FormalSeries.ThreeFieldFinalLaurentAction
open private coeff_mul_box from
  D5.S3.VertexAlgebra.FormalSeries.ThreeFieldFinalInverseCoefficients

variable {R : Type*} [CommRing R] [Algebra ℂ R]

/-- Native coefficient reorder, with no raw-variable substitution. -/
def rotateSeries (P : MvPowerSeries (Fin 3) R) : MvPowerSeries (Fin 3) R :=
  fun d => MvPowerSeries.coeff (index3 (d 2) (d 0) (d 1)) P

omit [Algebra ℂ R] in
private theorem signed_rotate (P : MvPowerSeries (Fin 3) R) (e : Exponent 3) :
    signedExtend (rotateSeries P) e = signedExtend P ![e 2, e 0, e 1] := by
  have hn : (∀ i, 0 ≤ e i) ↔ ∀ i : Fin 3, 0 ≤ (![e 2, e 0, e 1] : Exponent 3) i := by
    constructor
    · intro h i
      fin_cases i
      · exact h 2
      · exact h 0
      · exact h 1
    · intro h i
      fin_cases i
      · exact h 1
      · exact h 2
      · exact h 0
  by_cases h : ∀ i, 0 ≤ e i
  · rw [signedExtend, ite_eq_left h, signedExtend, ite_eq_left (hn.mp h)]
    change MvPowerSeries.coeff
      (index3 ((signedIndex e) 2) ((signedIndex e) 0) ((signedIndex e) 1)) P = _
    apply congrArg (fun d => MvPowerSeries.coeff d P)
    ext i
    fin_cases i <;> simp [index3, signedIndex]
  · simp only [signedExtend, ite_eq_right h, ite_eq_right (fun hh => h (hn.mpr hh))]

/-- The actual native unit after the b/z and z/x coefficient chart. -/
def innerUnitSeries (R : Type*) [CommRing R] (k H : ℕ) : MvPowerSeries (Fin 3) R :=
  (1 - MvPowerSeries.X 1 - MvPowerSeries.X 0 * MvPowerSeries.X 1) ^ k *
    (1 - MvPowerSeries.X 1) ^ k * (1 + MvPowerSeries.X 0) ^ H

def innerUnit (R : Type*) [CommRing R] (k H : ℕ) :
    (MvPowerSeries (Fin 3) R)ˣ where
  val := innerUnitSeries R k H
  inv := MvPowerSeries.invOfUnit (innerUnitSeries R k H) 1
  val_inv := MvPowerSeries.mul_invOfUnit _ 1 (by simp [innerUnitSeries])
  inv_val := MvPowerSeries.invOfUnit_mul _ 1 (by simp [innerUnitSeries])

def innerShift (k : ℕ) (a : Fin 3 → ℕ) : Exponent 3 :=
  ![(k : ℤ), k + a 1 + a 2, a 0 + 3 * k + a 1 + a 2]

/-- A signed native coefficient, including all outside-cone zero branches. -/
def rawInnerCoefficient (P : MvPowerSeries (Fin 3) R)
    (k : ℕ) (a : Fin 3 → ℕ) (e : Exponent 3) : R :=
  shiftedChart (innerShift k a)
    ((↑((innerUnit R k (a 1))⁻¹) : MvPowerSeries (Fin 3) R) *
      nativeChart (rotateSeries P)) ![e 1, e 2, e 0]

private theorem sub_transport (b : Exponent 3) (p q : LaurentPolynomial 3)
    (P Q : MvPowerSeries (Fin 3) R)
    (hp : ∀ F, polynomialAction p (shiftedChart b F) = shiftedChart b (P * F))
    (hq : ∀ F, polynomialAction q (shiftedChart b F) = shiftedChart b (Q * F))
    (F : MvPowerSeries (Fin 3) R) :
    polynomialAction (p - q) (shiftedChart b F) = shiftedChart b ((P - Q) * F) := by
  rw [map_sub, LinearMap.sub_apply, hp, hq]
  funext e
  change signedExtension (P * F) (W e + b) - signedExtension (Q * F) (W e + b) =
    signedExtension ((P - Q) * F) (W e + b)
  rw [sub_mul, map_sub]
  rfl

private theorem factorization {T : Type*} [CommRing T]
    (S T' U : T) (k A H B : ℕ) :
    U ^ A * (U - S * T' * U - T' * U) ^ k * (U - T' * U) ^ k *
      (S * T' * U) ^ k * (S * T' * U + T' * U) ^ H * (T' * U) ^ B =
    S ^ k * T' ^ (k + H + B) * U ^ (A + 3 * k + H + B) *
      ((1 - T' - S * T') ^ k * (1 - T') ^ k * (1 + S) ^ H) := by
  rw [show U - S * T' * U - T' * U = (1 - T' - S * T') * U by ring,
    show U - T' * U = (1 - T') * U by ring,
    show S * T' * U + T' * U = (1 + S) * T' * U by ring,
    show 3 * k = k + k + k by omega]
  simp only [mul_pow, pow_add]
  ring

private theorem rotated_action_chart (F : MvPowerSeries (Fin 3) R)
    (k : ℕ) (a : Fin 3 → ℕ) (e : Exponent 3) :
    polynomialAction (rotatedPolynomial k a) (shiftedChart (innerShift k a) F) e =
      signedExtend (innerUnitSeries R k (a 1) * F) (W e) := by
  let b := innerShift k a
  have hx := variable_transport (R := R) b 0
  have hy := variable_transport (R := R) b 1
  have hz := variable_transport (R := R) b 2
  have hd := sub_transport b _ _ _ _ hz hy
  have ht := sub_transport b _ _ _ _ (sub_transport b _ _ _ _ hz hx) hy
  have hp := add_transport b _ _ _ _ hx hy
  have transport := mul_transport b _ _ _ _
    (mul_transport b _ _ _ _
      (mul_transport b _ _ _ _
        (mul_transport b _ _ _ _
          (mul_transport b _ _ _ _
            (pow_transport b _ _ hz (a 0)) (pow_transport b _ _ ht k))
          (pow_transport b _ _ hd k)) (pow_transport b _ _ hx k))
        (pow_transport b _ _ hp (a 1))) (pow_transport b _ _ hy (a 2)) F
  have evaluated := congrFun transport e
  change polynomialAction (rotatedPolynomial k a) (shiftedChart b F) e = _ at evaluated
  rw [evaluated]
  change signedExtend _ (W e + innerShift k a) = _
  simp only [chartVariables, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [factorization]
  change signedExtend
    ((MvPowerSeries.X 0 ^ k * MvPowerSeries.X 1 ^ (k + a 1 + a 2) *
      MvPowerSeries.X 2 ^ (a 0 + 3 * k + a 1 + a 2) *
      innerUnitSeries R k (a 1)) * F) (W e + innerShift k a) = _
  rw [mul_assoc, mul_assoc, mul_assoc, signed_X_pow_mul, signed_X_pow_mul,
    signed_X_pow_mul]
  congr 1
  funext i
  fin_cases i <;> dsimp [innerShift, W] <;> simp

omit [Algebra ℂ R] in
private theorem rotate_raw (P : MvPowerSeries (Fin 3) R) (k : ℕ) (a : Fin 3 → ℕ) :
    rotate (rawInnerCoefficient P k a) = shiftedChart (innerShift k a)
      ((↑((innerUnit R k (a 1))⁻¹) : MvPowerSeries (Fin 3) R) *
        nativeChart (rotateSeries P)) := by
  funext e
  change shiftedChart _ _ ![e 0, e 1, e 2] = _
  congr 1
  funext i
  fin_cases i <;> rfl

theorem raw_inner_action (P : MvPowerSeries (Fin 3) R)
    (k : ℕ) (a : Fin 3 → ℕ) (e : Exponent 3) :
    polynomialAction (innerPolynomial k a) (rawInnerCoefficient P k a) e =
      signedExtend P e := by
  have h := congrFun (inner_action_rotate k a (rawInnerCoefficient P k a))
    ![e 1, e 2, e 0]
  rw [rotate_raw, rotated_action_chart] at h
  have cancel : innerUnitSeries R k (a 1) *
      ((↑((innerUnit R k (a 1))⁻¹) : MvPowerSeries (Fin 3) R) *
        nativeChart (rotateSeries P)) = nativeChart (rotateSeries P) := by
    have hc : innerUnitSeries R k (a 1) *
        (↑((innerUnit R k (a 1))⁻¹) : MvPowerSeries (Fin 3) R) = 1 :=
      (innerUnit R k (a 1)).val_inv
    rw [← mul_assoc, hc, one_mul]
  rw [cancel, native_chart_readout, signed_rotate] at h
  have ee : (![e 0, e 1, e 2] : Exponent 3) = e := by
    funext i
    fin_cases i <;> rfl
  simpa only [rotate, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, ee]
    using h.symm

theorem raw_inner_support (P : MvPowerSeries (Fin 3) R)
    (k : ℕ) (a : Fin 3 → ℕ) : NestedSupport (rotate (rawInnerCoefficient P k a)) := by
  rw [rotate_raw]
  constructor
  · refine ⟨k, ?_⟩
    intro b z x hb
    apply ite_eq_right
    intro hn
    have h := hn 0
    dsimp [W, innerShift] at h
    omega
  · intro b
    refine ⟨(b + k + a 1 + a 2).toNat, ?_⟩
    intro z x hz
    apply ite_eq_right
    intro hn
    have h := hn 1
    dsimp [W, innerShift] at h
    omega

end
end D5.S3.VertexAlgebra.ThreeFieldInnerNativeInverse
