/- GID: D5/S3/VertexAlgebra/FormalSeries/ThreeFieldBalancedNativeInverse
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/FormalSeries/ThreeFieldBalancedNativeInverse
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native unit inversion of the literal balanced multiplier on signed coefficients. -/
import D5.S3.VertexAlgebra.FormalSeries.ThreeFieldBalancedPolynomial
import D5.S3.VertexAlgebra.FormalSeries.ThreeFieldInnerNativeInverse
import D5.S3.VertexAlgebra.FormalSeries.ThreeFieldFinalLaurentAction
import Batteries.Tactic.OpenPrivate

/-! All native substitutions concern power series, never unrestricted raw
distributions. The raw coefficient action is proved by finite translations.
The existing native chart and signed monomial identities are reused. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.VertexAlgebra.ThreeFieldBalancedNativeInverse
open UniformGradedLocalCorrelator UngradedLocalWordSeries SupportedThreeFieldCollision
open SupportedFinalCovariance SupportedFinalRInjectivity ThreeFieldBalancedPolynomial
open ThreeFieldFinalCone
open scoped BigOperators
noncomputable section

open private W shiftedChart chartVariables variable_transport add_transport
  mul_transport pow_transport native_chart_readout from
  D5.S3.VertexAlgebra.FormalSeries.ThreeFieldFinalLaurentAction
open private coeff_mul_box from
  D5.S3.VertexAlgebra.FormalSeries.ThreeFieldFinalInverseCoefficients

open private sub_transport from
  D5.S3.VertexAlgebra.FormalSeries.ThreeFieldInnerNativeInverse

variable {R : Type*} [CommRing R] [Algebra ℂ R]

/-- Native coefficient reorder, with no raw-variable substitution. -/
def balancedSwapSeries (P : MvPowerSeries (Fin 3) R) : MvPowerSeries (Fin 3) R :=
  fun d => MvPowerSeries.coeff (index3 (d 0) (d 2) (d 1)) P

omit [Algebra ℂ R] in
private theorem signed_swap (P : MvPowerSeries (Fin 3) R) (e : Exponent 3) :
    signedExtend (balancedSwapSeries P) e = signedExtend P ![e 0, e 2, e 1] := by
  have hn : (∀ i, 0 ≤ e i) ↔ ∀ i : Fin 3, 0 ≤ (![e 0, e 2, e 1] : Exponent 3) i := by
    constructor
    · intro h i
      fin_cases i
      · exact h 0
      · exact h 2
      · exact h 1
    · intro h i
      fin_cases i
      · exact h 0
      · exact h 2
      · exact h 1
  by_cases h : ∀ i, 0 ≤ e i
  · rw [signedExtend, ite_eq_left h, signedExtend, ite_eq_left (hn.mp h)]
    change MvPowerSeries.coeff
      (index3 ((signedIndex e) 0) ((signedIndex e) 2) ((signedIndex e) 1)) P = _
    apply congrArg (fun d => MvPowerSeries.coeff d P)
    ext i
    fin_cases i <;> simp [index3, signedIndex]
  · simp only [signedExtend, ite_eq_right h, ite_eq_right (fun hh => h (hn.mpr hh))]

/-- The constant-one factor of the literal balanced clearing. -/
def balancedUnitSeries (R : Type*) [CommRing R] (k A : ℕ) : MvPowerSeries (Fin 3) R :=
  (1 + MvPowerSeries.X 0 * MvPowerSeries.X 1) ^ A *
    (1 + MvPowerSeries.X 0 * MvPowerSeries.X 1 - MvPowerSeries.X 1) ^ k *
    (1 - MvPowerSeries.X 1) ^ k

def balancedUnit (R : Type*) [CommRing R] (k A : ℕ) :
    (MvPowerSeries (Fin 3) R)ˣ where
  val := balancedUnitSeries R k A
  inv := MvPowerSeries.invOfUnit (balancedUnitSeries R k A) 1
  val_inv := MvPowerSeries.mul_invOfUnit _ 1 (by simp [balancedUnitSeries])
  inv_val := MvPowerSeries.invOfUnit_mul _ 1 (by simp [balancedUnitSeries])

def balancedShift (k : ℕ) (a : Fin 3 → ℕ) : Exponent 3 :=
  ![(k : ℤ), k + a 2, a 0 + a 1 + a 2 + 3 * k]

def rawBalancedCoefficient (P : MvPowerSeries (Fin 3) R)
    (k : ℕ) (a : Fin 3 → ℕ) (e : Exponent 3) : R :=
  shiftedChart (balancedShift k a)
    ((↑((balancedUnit R k (a 0))⁻¹) : MvPowerSeries (Fin 3) R) *
      nativeChart (balancedSwapSeries P)) ![e 0, e 2, e 1]

private theorem factorization {T : Type*} [CommRing T]
    (S T' U : T) (k A B C : ℕ) :
    (U + S * T' * U) ^ A * U ^ B * (T' * U) ^ C * (S * T' * U) ^ k *
      (S * T' * U + U - T' * U) ^ k * (U - T' * U) ^ k =
    S ^ k * T' ^ (k + C) * U ^ (A + B + C + 3 * k) *
      ((1 + S * T') ^ A * (1 + S * T' - T') ^ k * (1 - T') ^ k) := by
  rw [show U + S * T' * U = (1 + S * T') * U by ring,
    show S * T' * U + U - T' * U = (1 + S * T' - T') * U by ring,
    show U - T' * U = (1 - T') * U by ring,
    show 3 * k = k + k + k by omega]
  simp only [mul_pow, pow_add]
  ring

private theorem rotated_action_chart (F : MvPowerSeries (Fin 3) R)
    (k : ℕ) (a : Fin 3 → ℕ) (e : Exponent 3) :
    polynomialAction (balancedRotatedPolynomial k a) (shiftedChart (balancedShift k a) F) e =
      signedExtend (balancedUnitSeries R k (a 0) * F) (W e) := by
  let b := balancedShift k a
  have hx := variable_transport (R := R) b 0
  have hy := variable_transport (R := R) b 1
  have hz := variable_transport (R := R) b 2
  have hd := sub_transport b _ _ _ _ hz hy
  have ht := sub_transport b _ _ _ _ (add_transport b _ _ _ _ hx hz) hy
  have hp := add_transport b _ _ _ _ hz hx
  have transport := mul_transport b _ _ _ _
    (mul_transport b _ _ _ _
      (mul_transport b _ _ _ _
        (mul_transport b _ _ _ _
          (mul_transport b _ _ _ _
            (pow_transport b _ _ hp (a 0)) (pow_transport b _ _ hz (a 1)))
          (pow_transport b _ _ hy (a 2))) (pow_transport b _ _ hx k))
        (pow_transport b _ _ ht k)) (pow_transport b _ _ hd k) F
  have evaluated := congrFun transport e
  change polynomialAction (balancedRotatedPolynomial k a) (shiftedChart b F) e = _ at evaluated
  rw [evaluated]
  change signedExtend _ (W e + balancedShift k a) = _
  simp only [chartVariables, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [factorization]
  change signedExtend
    ((MvPowerSeries.X 0 ^ k * MvPowerSeries.X 1 ^ (k + a 2) *
      MvPowerSeries.X 2 ^ (a 0 + a 1 + a 2 + 3 * k) *
      balancedUnitSeries R k (a 0)) * F) (W e + balancedShift k a) = _
  rw [mul_assoc, mul_assoc, mul_assoc, signed_X_pow_mul, signed_X_pow_mul,
    signed_X_pow_mul]
  congr 1
  funext i
  fin_cases i <;> dsimp [balancedShift, W] <;> simp

omit [Algebra ℂ R] in
private theorem swap_raw (P : MvPowerSeries (Fin 3) R) (k : ℕ) (a : Fin 3 → ℕ) :
    balancedRotate (rawBalancedCoefficient P k a) = shiftedChart (balancedShift k a)
      ((↑((balancedUnit R k (a 0))⁻¹) : MvPowerSeries (Fin 3) R) *
        nativeChart (balancedSwapSeries P)) := by
  funext e
  change shiftedChart _ _ ![e 0, e 1, e 2] = _
  congr 1
  funext i
  fin_cases i <;> rfl

theorem raw_balanced_action (P : MvPowerSeries (Fin 3) R)
    (k : ℕ) (a : Fin 3 → ℕ) (e : Exponent 3) :
    polynomialAction (balancedPolynomial k a) (rawBalancedCoefficient P k a) e =
      signedExtend P e := by
  have h := congrFun (balanced_action_rotate k a (rawBalancedCoefficient P k a))
    ![e 0, e 2, e 1]
  rw [swap_raw, rotated_action_chart] at h
  have cancel : balancedUnitSeries R k (a 0) *
      ((↑((balancedUnit R k (a 0))⁻¹) : MvPowerSeries (Fin 3) R) *
        nativeChart (balancedSwapSeries P)) = nativeChart (balancedSwapSeries P) := by
    have hc : balancedUnitSeries R k (a 0) *
        (↑((balancedUnit R k (a 0))⁻¹) : MvPowerSeries (Fin 3) R) = 1 :=
      (balancedUnit R k (a 0)).val_inv
    rw [← mul_assoc, hc, one_mul]
  rw [cancel, native_chart_readout, signed_swap] at h
  have ee : (![e 0, e 1, e 2] : Exponent 3) = e := by
    funext i
    fin_cases i <;> rfl
  simpa only [balancedRotate, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, ee]
    using h.symm

theorem raw_balanced_support (P : MvPowerSeries (Fin 3) R)
    (k : ℕ) (a : Fin 3 → ℕ) : NestedSupport (balancedRotate (rawBalancedCoefficient P k a)) := by
  rw [swap_raw]
  constructor
  · refine ⟨k, ?_⟩
    intro b z x hb
    apply ite_eq_right
    intro hn
    have h := hn 0
    dsimp [W, balancedShift] at h
    omega
  · intro b
    refine ⟨(b + k + a 2).toNat, ?_⟩
    intro z x hz
    apply ite_eq_right
    intro hn
    have h := hn 1
    dsimp [W, balancedShift] at h
    omega

end
end D5.S3.VertexAlgebra.ThreeFieldBalancedNativeInverse
