/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSCommonSpectralDeterminant
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSCommonSpectralDeterminant
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: The closed-form common spectral determinant is nonzero at every required suffix length. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.CommonSpectralDeterminantCertificate
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformSpectralDivisorArithmetic

/-! The integral bivariate numerator for the actual common spectral-divisor minor. -/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace PeriodicMPSCommonSpectralDeterminant

open Polynomial
open PeriodicMPSCommonSpectralJets (L coefficient)
open SpectralDeterminantReflection
open CommonSpectralDeterminantCertificate (input numerator scale det_input)

/-- The integral numerator. The outer variable is `q` and the inner variable is `m`. -/
noncomputable def N : Polynomial (Polynomial ℤ) := asPolynomial numerator

private noncomputable abbrev ratCoeffs := Polynomial.mapRingHom (Int.castRingHom ℚ)

/-- The symbolic determinant identity before changing the coefficients to rationals. -/
theorem integral_matrix_det_eq_scale_mul_N :
    (input.map asPolynomial).det = (scale : IP) * N :=
  det_input

private theorem eval_N_int (m q : ℤ) : N.evalEval m q = value m q numerator := by
  rw [← specialize_asPolynomial (RingHom.id ℤ) m q numerator]
  simp only [N, specialize, coe_eval₂RingHom]
  change _ = eval₂ (evalRingHom m) q _
  rw [eval₂_evalRingHom]

private theorem eval_N_rat (m q : ℚ) :
    (N.map ratCoeffs).evalEval m q = value m q numerator := by
  rw [← specialize_asPolynomial (Int.castRingHom ℚ) m q numerator]
  exact (eval₂_eval₂RingHom_apply (Int.castRingHom ℚ) m q N).symm

private theorem input_eval (m q : ℚ) (i j : Fin 9) :
    specialize (Int.castRingHom ℚ) m q (asPolynomial (input i j)) = 768 * L m q i j := by
  rw [specialize_asPolynomial]
  simp only [input, bi, List.map_cons, List.map_nil, value, Dense.eval_cons, Dense.eval_nil,
    L, coefficient, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, mul_zero, add_zero]
  ring

/-- At every pair of rational inputs, the integral polynomial evaluates to `2^34 det L`. -/
theorem N_eval_eq_two_pow_mul_det_L (m q : ℚ) :
    (N.map ratCoeffs).evalEval m q = (2 : ℚ)^34 * (L m q).det := by
  let f := specialize (Int.castRingHom ℚ) m q
  have hM : f.mapMatrix (input.map asPolynomial) = (768 : ℚ) • L m q := by
    apply Matrix.ext
    intro i j
    exact input_eval m q i j
  have h := congrArg f integral_matrix_det_eq_scale_mul_N
  rw [f.map_det, hM, Matrix.det_smul, Fintype.card_fin, map_mul, map_intCast] at h
  have hN : f N = (N.map ratCoeffs).evalEval m q := by
    rw [eval_N_rat]
    exact specialize_asPolynomial (Int.castRingHom ℚ) m q numerator
  rw [hN] at h
  have hs : (768 : ℚ)^9 = (scale : ℚ) * 2^34 := by norm_num [scale]
  rw [hs, mul_assoc] at h
  exact (mul_left_cancel₀ (by norm_num [scale] : (scale : ℚ) ≠ 0) h).symm

private abbrev RP := Polynomial (Polynomial ℚ)

private noncomputable def ratMap : IP →+* RP := mapRingHom ratCoeffs

/-- The two-variable matrix polynomial whose evaluation is the literal matrix `L`. -/
noncomputable def polynomialL : Matrix (Fin 9) (Fin 9) RP :=
  fun i j => CC (1 / 768 : ℚ) * ratMap (asPolynomial (input i j))

theorem polynomialL_eval (m q : ℚ) :
    (evalEvalRingHom m q).mapMatrix polynomialL = L m q := by
  apply Matrix.ext
  intro i j
  let e := evalEvalRingHom m q
  change e (CC (1 / 768 : ℚ) * ratMap (asPolynomial (input i j))) = L m q i j
  rw [map_mul]
  have h0 : e (ratMap (asPolynomial (input i j))) = 768 * L m q i j := by
    change ((asPolynomial (input i j)).map ratCoeffs).evalEval m q = _
    rw [← eval₂_eval₂RingHom_apply, ← coe_eval₂RingHom]
    exact input_eval m q i j
  rw [show e (CC (1 / 768 : ℚ)) = 1 / 768 from evalEval_CC m q _, h0]
  ring

private theorem bivar_ext {p r : RP} (h : ∀ m q : ℚ, p.evalEval m q = r.evalEval m q) :
    p = r := by
  apply Polynomial.ext
  intro k
  apply Polynomial.funext
  intro m
  have hm : p.map (evalRingHom m) = r.map (evalRingHom m) := by
    apply Polynomial.funext
    intro q
    simpa only [map_evalRingHom_eval] using h m q
  have hc := congrArg (fun t : Polynomial ℚ => t.coeff k) hm
  simpa only [coeff_map, coe_evalRingHom] using hc

/-- The exact identity in the bivariate polynomial ring over the rationals. -/
theorem N_map_eq_two_pow_mul_det_polynomialL :
    N.map ratCoeffs = CC ((2 : ℚ)^34) * polynomialL.det := by
  apply bivar_ext
  intro m q
  let e := evalEvalRingHom m q
  change _ = e (CC ((2 : ℚ)^34) * polynomialL.det)
  rw [map_mul, e.map_det, polynomialL_eval]
  rw [show e (CC ((2 : ℚ)^34)) = (2 : ℚ)^34 from evalEval_CC m q _]
  exact N_eval_eq_two_pow_mul_det_L m q

/-- The exact constant coefficient in `q`, including the octic factor. -/
theorem N_coeff_zero : N.coeff 0 = SpectralDivisorArithmetic.constantTerm := by
  apply Polynomial.funext
  intro m
  rw [coeff_zero_eq_eval_zero]
  have he : N.evalEval m 0 = (N.eval 0).eval m := by
    simp only [evalEval, map_zero]
  rw [← he]
  rw [eval_N_int, SpectralDivisorArithmetic.eval_constantTerm, SpectralDivisorArithmetic.eval_octic]
  simp only [numerator, bi, List.map_cons, List.map_nil, value, Dense.eval_cons, Dense.eval_nil,
    zero_mul, mul_zero, add_zero, Int.cast_id]
  ring

theorem N_eval_at_length_ne_zero {m : ℕ} (hm : 8 ≤ m) :
    N.evalEval (m : ℤ) ((-3 : ℤ)^m) ≠ 0 :=
  SpectralDivisorArithmetic.evalEval_ne_zero N N_coeff_zero hm

private theorem det_L_at_length_ne_zero_of_N (m : ℕ)
    (hn : N.evalEval (m : ℤ) ((-3 : ℤ)^m) ≠ 0) :
    (L (m : ℚ) ((-3 : ℚ)^m)).det ≠ 0 := by
  intro hz
  have h := Polynomial.map_mapRingHom_evalEval (f := Int.castRingHom ℚ) N (m : ℤ) ((-3 : ℤ)^m)
  change (N.map ratCoeffs).evalEval (↑(m : ℤ)) (↑((-3 : ℤ)^m)) =
    ((N.evalEval (m : ℤ) ((-3 : ℤ)^m) : ℤ) : ℚ) at h
  push_cast at h
  rw [N_eval_eq_two_pow_mul_det_L, hz, mul_zero] at h
  apply hn
  exact_mod_cast h.symm

theorem det_L_at_length_ne_zero {m : ℕ} (hm : 8 ≤ m) :
    (L (m : ℚ) ((-3 : ℚ)^m)).det ≠ 0 :=
  det_L_at_length_ne_zero_of_N m (N_eval_at_length_ne_zero hm)

/-- Values of the integral numerator at suffix lengths 5, 6 and 7. -/
def firstNumerators (k : Fin 3) : ℤ :=
  ![2962272587322628513100811416371200, 282048273365687754000268639682596700160,
    -2514871601754008510606610582271386294681600] k

theorem N_eval_first (k : Fin 3) :
    N.evalEval ((k.val + 5 : ℕ) : ℤ) ((-3 : ℤ)^(k.val + 5)) = firstNumerators k := by
  rw [eval_N_int]
  fin_cases k <;> decide +kernel

theorem N_first_nonzero (k : Fin 3) :
    N.evalEval ((k.val + 5 : ℕ) : ℤ) ((-3 : ℤ)^(k.val + 5)) ≠ 0 := by
  rw [N_eval_first]
  fin_cases k <;> decide +kernel

theorem det_L_at_length_ge_five_ne_zero {m : ℕ} (hm : 5 ≤ m) :
    (L (m : ℚ) ((-3 : ℚ)^m)).det ≠ 0 := by
  by_cases h8 : 8 ≤ m
  · exact det_L_at_length_ne_zero h8
  · let k : Fin 3 := ⟨m - 5, by omega⟩
    have hk : k.val + 5 = m := by dsimp [k]; omega
    exact det_L_at_length_ne_zero_of_N m (hk ▸ N_first_nonzero k)

end PeriodicMPSCommonSpectralDeterminant
