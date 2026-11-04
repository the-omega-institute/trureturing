/- GID: D5/S3/VertexAlgebra/FormalSeries/ThreeFieldFinalLaurentAction
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/FormalSeries/ThreeFieldFinalLaurentAction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual finite raw action on the existing final Laurent coefficients. -/
import D5.S3.VertexAlgebra.FormalSeries.ThreeFieldFinalInverseCoefficients
import D5.S3.VertexAlgebra.FormalSeries.SupportedFinalCovariance

/-! proof_shape: content
admission_basis: escape-witness
escape_witness: variable_transport proves the raw-to-native signed translations;
native_chart_readout proves both negative and unsorted coefficient branches.
The private chart below only reads coefficients of native series.
Every raw action is the existing finite polynomialAction. Its three generating
translations are checked on all signed indices, and sums/products/powers
propagate those finite identities to exactly the six factors of R. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.VertexAlgebra.ThreeFieldFinalLaurentAction
open UniformGradedLocalCorrelator UngradedLocalWordSeries SupportedThreeFieldCollision
open ThreeFieldFinalLaurentFiber ThreeFieldFinalCone ThreeFieldFinalInverseCoefficients
open SupportedFinalCovariance
open scoped BigOperators
noncomputable section
variable {R : Type*} [CommRing R] [Algebra ℂ R]

private def W (e : Exponent 3) : Exponent 3 := ![e 0, e 0 + e 1, e 0 + e 1 + e 2]

private def bshift (k : ℕ) (a : Fin 3 → ℕ) : Exponent 3 :=
  ![(k : ℤ), 3 * k, 3 * k + a 0 + a 1 + a 2]

private def shiftedChart (b : Exponent 3) (F : MvPowerSeries (Fin 3) R) :
    Distribution 3 R := fun e => signedExtend F (W e + b)

private def chartVariables (R : Type*) [CommRing R] :
    Fin 3 → MvPowerSeries (Fin 3) R :=
  ![MvPowerSeries.X 0 * MvPowerSeries.X 1 * MvPowerSeries.X 2,
    MvPowerSeries.X 1 * MvPowerSeries.X 2, MvPowerSeries.X 2]

private theorem signed_variable_mul (F : MvPowerSeries (Fin 3) R)
    (i : Fin 3) (e : Exponent 3) :
    signedExtend (MvPowerSeries.X i * F) e = signedExtend F (e - Pi.single i 1) := by
  simpa only [pow_one, one_nsmul] using signed_X_pow_mul F i 1 e

/-- This is the finite monomial map (1,0,0)->(1,1,1),
(0,1,0)->(0,1,1), (0,0,1)->(0,0,1), checked BEFORE taking native indices. -/
private theorem variable_transport (b : Exponent 3) (i : Fin 3)
    (F : MvPowerSeries (Fin 3) R) :
    polynomialAction (variablePolynomial i) (shiftedChart b F) =
      shiftedChart b (chartVariables R i * F) := by
  funext e
  rw [variablePolynomial, polynomialAction, AddMonoidAlgebra.lift_single]
  change (1 : ℂ) • signedExtend F (W (e - Pi.single i 1) + b) =
    signedExtend (chartVariables R i * F) (W e + b)
  rw [one_smul]
  fin_cases i
  · dsimp [chartVariables]
    rw [mul_assoc, mul_assoc, signed_variable_mul, signed_variable_mul,
      signed_variable_mul]
    apply congrArg (signedExtend F)
    funext c
    fin_cases c <;> dsimp [W] <;> simp [Pi.single_apply] <;> ring
  · dsimp [chartVariables]
    rw [mul_assoc, signed_variable_mul, signed_variable_mul]
    apply congrArg (signedExtend F)
    funext c
    fin_cases c <;> dsimp [W] <;> simp [Pi.single_apply] <;> ring
  · dsimp [chartVariables]
    rw [signed_variable_mul]
    apply congrArg (signedExtend F)
    funext c
    fin_cases c <;> dsimp [W] <;> simp [Pi.single_apply] <;> ring

private theorem add_transport (b : Exponent 3) (p q : LaurentPolynomial 3)
    (P Q : MvPowerSeries (Fin 3) R)
    (hp : ∀ F, polynomialAction p (shiftedChart b F) = shiftedChart b (P * F))
    (hq : ∀ F, polynomialAction q (shiftedChart b F) = shiftedChart b (Q * F))
    (F : MvPowerSeries (Fin 3) R) :
    polynomialAction (p + q) (shiftedChart b F) = shiftedChart b ((P + Q) * F) := by
  rw [map_add, LinearMap.add_apply, hp, hq]
  funext e
  change signedExtension (P * F) (W e + b) + signedExtension (Q * F) (W e + b) =
    signedExtension ((P + Q) * F) (W e + b)
  rw [add_mul, map_add]
  rfl

private theorem mul_transport (b : Exponent 3) (p q : LaurentPolynomial 3)
    (P Q : MvPowerSeries (Fin 3) R)
    (hp : ∀ F, polynomialAction p (shiftedChart b F) = shiftedChart b (P * F))
    (hq : ∀ F, polynomialAction q (shiftedChart b F) = shiftedChart b (Q * F))
    (F : MvPowerSeries (Fin 3) R) :
    polynomialAction (p * q) (shiftedChart b F) = shiftedChart b ((P * Q) * F) := by
  rw [map_mul, Module.End.mul_apply, hq, hp, mul_assoc]

private theorem pow_transport (b : Exponent 3) (p : LaurentPolynomial 3)
    (P : MvPowerSeries (Fin 3) R)
    (hp : ∀ F, polynomialAction p (shiftedChart b F) = shiftedChart b (P * F))
    (n : ℕ) (F : MvPowerSeries (Fin 3) R) :
    polynomialAction (p ^ n) (shiftedChart b F) = shiftedChart b (P ^ n * F) := by
  induction n generalizing F with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', pow_succ']
    exact mul_transport b p (p ^ n) P (P ^ n) hp ih F

/-- Finite transport of the concrete R. This is an action identity on raw
coefficients, not a formal substitution on an unrestricted distribution. -/
private theorem six_factor_transport (b : Exponent 3) (k : ℕ) (a : Fin 3 → ℕ)
    (F : MvPowerSeries (Fin 3) R) :
    polynomialAction
      (variablePolynomial 0 ^ k * variablePolynomial 1 ^ k *
        (variablePolynomial 0 + variablePolynomial 1) ^ k *
        (variablePolynomial 0 + variablePolynomial 1 + variablePolynomial 2) ^ a 0 *
        (variablePolynomial 1 + variablePolynomial 2) ^ a 1 * variablePolynomial 2 ^ a 2)
      (shiftedChart b F) =
    shiftedChart b
      (((chartVariables R 0) ^ k * (chartVariables R 1) ^ k *
        (chartVariables R 0 + chartVariables R 1) ^ k *
        (chartVariables R 0 + chartVariables R 1 + chartVariables R 2) ^ a 0 *
        (chartVariables R 1 + chartVariables R 2) ^ a 1 *
        (chartVariables R 2) ^ a 2) * F) := by
  have hx := variable_transport (R := R) b 0
  have hy := variable_transport (R := R) b 1
  have hz := variable_transport (R := R) b 2
  have hxy := add_transport b (variablePolynomial 0) (variablePolynomial 1)
    (chartVariables R 0) (chartVariables R 1) hx hy
  have hxyz := add_transport b (variablePolynomial 0 + variablePolynomial 1)
    (variablePolynomial 2) (chartVariables R 0 + chartVariables R 1)
    (chartVariables R 2) hxy hz
  have hyz := add_transport b (variablePolynomial 1) (variablePolynomial 2)
    (chartVariables R 1) (chartVariables R 2) hy hz
  have p0 := pow_transport b (variablePolynomial 0) (chartVariables R 0) hx k
  have p1 := pow_transport b (variablePolynomial 1) (chartVariables R 1) hy k
  have p2 := pow_transport b (variablePolynomial 0 + variablePolynomial 1)
    (chartVariables R 0 + chartVariables R 1) hxy k
  have p3 := pow_transport b (variablePolynomial 0 + variablePolynomial 1 + variablePolynomial 2)
    (chartVariables R 0 + chartVariables R 1 + chartVariables R 2) hxyz (a 0)
  have p4 := pow_transport b (variablePolynomial 1 + variablePolynomial 2)
    (chartVariables R 1 + chartVariables R 2) hyz (a 1)
  have p5 := pow_transport b (variablePolynomial 2) (chartVariables R 2) hz (a 2)
  exact mul_transport b _ _ _ _
    (mul_transport b _ _ _ _
      (mul_transport b _ _ _ _
        (mul_transport b _ _ _ _
          (mul_transport b _ _ _ _ p0 p1) p2) p3) p4) p5 F

private theorem cone_iff (k : ℕ) (a : Fin 3 → ℕ) (e : Exponent 3) :
    FinalCone k a e ↔ ∀ i, 0 ≤ (W e + bshift k a) i := by
  constructor
  · intro h i
    fin_cases i <;> dsimp [W, bshift] <;> dsimp only [FinalCone] at h <;> omega
  · intro h
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    simp only [Pi.add_apply, W, bshift, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at h0 h1 h2
    dsimp only [FinalCone]
    omega

/-- Equality with the OLD expression is proved before the raw action is used.
The outside-cone branch stays in signed arithmetic. -/
private theorem old_as_chart (P : MvPowerSeries (Fin 3) R) (k : ℕ) (a : Fin 3 → ℕ) :
    laurentCoefficient P k a = shiftedChart (bshift k a)
      ((↑((chartUnit R k a)⁻¹) : MvPowerSeries (Fin 3) R) * nativeChart P) := by
  funext e
  by_cases he : FinalCone k a e
  · let n := coneEquiv k a ⟨e, he⟩
    have decode_eq : decode k a n = e :=
      congrArg Subtype.val ((coneEquiv k a).symm_apply_apply ⟨e, he⟩)
    have nonneg := (cone_iff k a e).mp he
    have idx : signedIndex (W e + bshift k a) = index3 (n 0) (n 1) (n 2) := by
      ext i
      fin_cases i <;> simp [signedIndex, W, bshift, n, coneEquiv, index3] <;>
        congr 1 <;> omega
    rw [← decode_eq, ← inverse_coefficients P k a n, decode_eq]
    change _ = signedExtend _ (W e + bshift k a)
    rw [signedExtend, if_pos nonneg]
    change _ = MvPowerSeries.coeff (signedIndex (W e + bshift k a)) _
    rw [idx]
    rfl
  · rw [old_zero_outside P k a e he]
    change 0 = signedExtend _ (W e + bshift k a)
    rw [signedExtend, if_neg (fun h => he ((cone_iff k a e).mpr h))]

/-- Removing t^bshift leaves output W(e), NOT chi(e). This equation holds
also when W(e) has a negative coordinate, by the signed monomial suppliers. -/
private theorem final_action_chart (F : MvPowerSeries (Fin 3) R)
    (k : ℕ) (a : Fin 3 → ℕ) (e : Exponent 3) :
    polynomialAction
      (variablePolynomial 0 ^ k * variablePolynomial 1 ^ k *
        (variablePolynomial 0 + variablePolynomial 1) ^ k *
        (variablePolynomial 0 + variablePolynomial 1 + variablePolynomial 2) ^ a 0 *
        (variablePolynomial 1 + variablePolynomial 2) ^ a 1 * variablePolynomial 2 ^ a 2)
      (shiftedChart (bshift k a) F) e =
      signedExtend (chartUnitSeries R k a * F) (W e) := by
  rw [six_factor_transport]
  change signedExtend _ (W e + bshift k a) = _
  dsimp [chartVariables]
  rw [native_chart_factorization]
  change signedExtend
    ((MvPowerSeries.X 0 ^ k * MvPowerSeries.X 1 ^ (3 * k) *
      MvPowerSeries.X 2 ^ (3 * k + a 0 + a 1 + a 2) * chartUnitSeries R k a) * F)
    (W e + bshift k a) = _
  rw [mul_assoc, mul_assoc, mul_assoc, signed_X_pow_mul, signed_X_pow_mul,
    signed_X_pow_mul]
  apply congrArg (signedExtend (chartUnitSeries R k a * F))
  funext i
  fin_cases i <;> dsimp [bshift, W] <;> simp [Pi.single_apply, nsmul_eq_mul] <;> ring

/-- A negative raw coordinate with nonnegative W gives an unsorted Q index;
a negative coordinate of W gives the signed-zero branch. -/
private theorem native_chart_readout (P : MvPowerSeries (Fin 3) R) (e : Exponent 3) :
    signedExtend (nativeChart P) (W e) = signedExtend P e := by
  classical
  by_cases hw : ∀ i, 0 ≤ W e i
  · let n : Fin 3 → ℕ := fun i => (W e i).toNat
    have n0 : (n 0 : ℤ) = e 0 := Int.toNat_of_nonneg (hw 0)
    have n1 : (n 1 : ℤ) = e 0 + e 1 := Int.toNat_of_nonneg (hw 1)
    have n2 : (n 2 : ℤ) = e 0 + e 1 + e 2 := Int.toNat_of_nonneg (hw 2)
    have sorted : n 0 ≤ n 1 ∧ n 1 ≤ n 2 ↔ ∀ i, 0 ≤ e i := by
      constructor
      · intro h i
        fin_cases i <;> dsimp <;> omega
      · intro h
        have h0 := h 0
        have h1 := h 1
        have h2 := h 2
        constructor <;> omega
    have idx : signedIndex (W e) = index3 (n 0) (n 1) (n 2) := by
      ext i
      fin_cases i <;> simp [signedIndex, index3, n]
    have native_coeff (r s t : ℕ) :
        MvPowerSeries.coeff (index3 r s t) (nativeChart P) =
          if r ≤ s ∧ s ≤ t then
            MvPowerSeries.coeff (index3 r (s - r) (t - s)) P else 0 := by
      simp [MvPowerSeries.coeff_apply, nativeChart, index3]
    rw [signedExtend, if_pos hw]
    change MvPowerSeries.coeff (signedIndex (W e)) (nativeChart P) = _
    rw [idx, native_coeff]
    by_cases he : ∀ i, 0 ≤ e i
    · rw [if_pos (sorted.mpr he), signedExtend, if_pos he]
      change MvPowerSeries.coeff _ P = MvPowerSeries.coeff (signedIndex e) P
      apply congrArg P
      ext i
      have h0 := he 0
      have h1 := he 1
      have h2 := he 2
      fin_cases i <;> simp [index3, signedIndex] <;> omega
    · rw [if_neg (fun h => he (sorted.mp h)), signedExtend, if_neg he]
  · have he : ¬ ∀ i, 0 ≤ e i := by
      intro he
      apply hw
      intro i
      have h0 := he 0
      have h1 := he 1
      have h2 := he 2
      fin_cases i <;> dsimp [W] <;> omega
    simp only [signedExtend, if_neg hw, if_neg he]

/-- Full actual R-action of the EXISTING old Laurent expression, for infinite
P and EVERY signed target. No R-action or raw/K equality is a premise. -/
theorem raw_R_action_transport (P : MvPowerSeries (Fin 3) R)
    (k : ℕ) (a : Fin 3 → ℕ) (e : Exponent 3) :
    polynomialAction
      (variablePolynomial 0 ^ k * variablePolynomial 1 ^ k *
        (variablePolynomial 0 + variablePolynomial 1) ^ k *
        (variablePolynomial 0 + variablePolynomial 1 + variablePolynomial 2) ^ a 0 *
        (variablePolynomial 1 + variablePolynomial 2) ^ a 1 * variablePolynomial 2 ^ a 2)
      (laurentCoefficient P k a) e = signedExtend P e := by
  rw [old_as_chart P k a, final_action_chart, native_unit_equation, native_chart_readout]

end
end D5.S3.VertexAlgebra.ThreeFieldFinalLaurentAction
