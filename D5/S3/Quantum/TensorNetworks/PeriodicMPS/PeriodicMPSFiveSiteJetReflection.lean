/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSFiveSiteJetReflection
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSFiveSiteJetReflection
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSFiveSiteJetCoordinates]
   utility: none
   digest: The finite jet checks recover coefficients of the five-site observation polynomial. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSFiveSiteJetCoordinates
import Mathlib.Algebra.Polynomial.Eval.Defs

/-! The sum of three square-zero variables has fourth power zero. Its square
and cube record the corresponding Taylor coefficients. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteJetReflection

open PeriodicMPSFiveSiteCoordinates PeriodicMPSFiveSiteTraceChart
  PeriodicMPSFiveSiteJetCoordinates Polynomial
open scoped QuadraticAlgebra

open private amplitude entry D₁ D₂ D₃ constant parameter jet
  from D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSFiveSiteJetCoordinates

private def mapGaussian {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    Gaussian R →+* Gaussian S where
  toFun z := ⟨f z.re, f z.im⟩
  map_one' := by apply QuadraticAlgebra.ext <;> simp
  map_zero' := by apply QuadraticAlgebra.ext <;> simp
  map_add' x y := by apply QuadraticAlgebra.ext <;> simp
  map_mul' x y := by apply QuadraticAlgebra.ext <;> simp

private lemma mapGaussian_mk {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (a b : R) : mapGaussian f ⟨a, b⟩ = ⟨f a, f b⟩ := rfl

private lemma mapGaussian_star {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (a : Gaussian R) : mapGaussian f (star a) = star (mapGaussian f a) := by
  apply QuadraticAlgebra.ext <;> simp [mapGaussian]

private lemma map_amplitude {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (u : Fin 9 → R) :
    mapGaussian f ∘ amplitude u = amplitude (f ∘ u) := by
  funext i
  fin_cases i <;>
    simp [amplitude, chart, shear, aligned, mapGaussian_mk, map_ofNat]

private lemma map_entry {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (u : Fin 9 → R) (i j : Fin 4) :
    mapGaussian f (entry u i j) = entry (f ∘ u) i j := by
  have hm (a : Fin 4) (b : Fin 8) :
      mapGaussian f (flatten (amplitude u) a b) = flatten (amplitude (f ∘ u)) a b := by
    have h (p : Fin 8 → Gaussian R) :
        mapGaussian f (flatten p a b) = flatten (mapGaussian f ∘ p) a b := by
      fin_cases a <;> fin_cases b <;> rfl
    rw [h, map_amplitude]
  simp only [entry, map_mul, map_sum, mapGaussian_mk, RingHom.map_zero, Function.comp_apply,
    mapGaussian_star, hm]

/-- The raw observation formula commutes with specialization of the scalar ring. -/
theorem map_raw {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (u : Fin 9 → R) (i : Fin 10) :
    f (raw u i) = raw (f ∘ u) i := by
  fin_cases i <;> first
  | exact congrArg QuadraticAlgebra.re (map_entry f u _ _)
  | exact congrArg QuadraticAlgebra.im (map_entry f u _ _)

noncomputable section

private local instance : CommRing D₁ := TrivSqZeroExt.commRing
private local instance : CommRing D₂ := TrivSqZeroExt.commRing
private local instance : CommRing D₃ := TrivSqZeroExt.commRing

private def inlHom (R : Type) [CommRing R] : R →+* DualNumber R :=
  (TrivSqZeroExt.inlAlgHom R R R).toRingHom

private def constantHom : ℚ →+* D₃ :=
  (inlHom D₂).comp ((inlHom D₁).comp (inlHom ℚ))

private theorem constantHom_apply (c : ℚ) : constantHom c = constant c := rfl

private noncomputable def evaluateJet : ℚ[X] →+* D₃ :=
  eval₂RingHom constantHom parameter

private lemma parameter_four : parameter ^ (4 : ℕ) = 0 := by
  apply TrivSqZeroExt.ext <;>
    apply TrivSqZeroExt.ext <;>
      apply TrivSqZeroExt.ext <;>
        decide +kernel

private lemma parameter_pow_eq_zero (n : ℕ) (hn : 4 ≤ n) :
    parameter ^ n = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [pow_add, parameter_four, zero_mul]

private lemma parameter_coefficients (n : ℕ) :
    (parameter ^ n).fst.snd.snd = (if n = 2 then 2 else 0) ∧
      (parameter ^ n).snd.snd.snd = (if n = 3 then 6 else 0) := by
  by_cases hn : 4 ≤ n
  · simp [parameter_pow_eq_zero n hn, show n ≠ 2 by omega, show n ≠ 3 by omega]
  · interval_cases n <;> decide +kernel

private lemma constant_mul_coefficients (c : ℚ) (z : D₃) :
    (constant c * z).fst.snd.snd = c * z.fst.snd.snd ∧
      (constant c * z).snd.snd.snd = c * z.snd.snd.snd := by
  let a₁ : D₁ := TrivSqZeroExt.inl c
  let a₂ : D₂ := TrivSqZeroExt.inl a₁
  change (TrivSqZeroExt.inl a₂ * z).fst.snd.snd = _ ∧
    (TrivSqZeroExt.inl a₂ * z).snd.snd.snd = _
  rw [TrivSqZeroExt.inl_mul_eq_smul]
  simp only [TrivSqZeroExt.fst_smul, TrivSqZeroExt.snd_smul, smul_eq_mul]
  unfold a₂
  rw [TrivSqZeroExt.inl_mul_eq_smul, TrivSqZeroExt.inl_mul_eq_smul]
  simp only [TrivSqZeroExt.snd_smul, smul_eq_mul]
  unfold a₁
  rw [TrivSqZeroExt.inl_mul_eq_smul, TrivSqZeroExt.inl_mul_eq_smul]
  simp only [TrivSqZeroExt.snd_smul, smul_eq_mul, and_self]

private lemma finite_coefficients (c : ℚ) (n : ℕ) :
    ((evaluateJet (monomial n c)).fst.snd.snd = 2 * (monomial n c).coeff 2) ∧
      ((evaluateJet (monomial n c)).snd.snd.snd = 6 * (monomial n c).coeff 3) := by
  change ((monomial n c).eval₂ constantHom parameter).fst.snd.snd = _ ∧
    ((monomial n c).eval₂ constantHom parameter).snd.snd.snd = _
  rw [eval₂_monomial, constantHom_apply, (constant_mul_coefficients c (parameter ^ n)).1,
    (constant_mul_coefficients c (parameter ^ n)).2, (parameter_coefficients n).1,
    (parameter_coefficients n).2, coeff_monomial, coeff_monomial]
  split_ifs <;> constructor <;> ring

private lemma eval_coefficients (p : ℚ[X]) :
    (evaluateJet p).fst.snd.snd = 2 * p.coeff 2 ∧
      (evaluateJet p).snd.snd.snd = 6 * p.coeff 3 := by
  induction p using Polynomial.induction_on' with
  | monomial n c => exact finite_coefficients c n
  | add p q hp hq =>
    simp [map_add, coeff_add, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, hp.1, hp.2, hq.1, hq.2,
      mul_add]

/-- The raw result along a quadratic path, as a univariate rational polynomial. -/
def pathPolynomial (u v w : Fin 9 → ℚ) (i : Fin 10) : ℚ[X] :=
  raw (fun k => C (u k) + C (v k) * X + C (w k) * X ^ 2) i

private lemma evaluation_pathPolynomial (u v w : Fin 9 → ℚ) (i : Fin 10) :
    evaluateJet (pathPolynomial u v w i) = jet u v w i := by
  unfold pathPolynomial jet
  rw [map_raw]
  congr 1
  funext k
  simp [evaluateJet, constantHom_apply]

theorem quadraticCoefficient_eq_coeff (u v w : Fin 9 → ℚ) (i : Fin 10) :
    quadraticCoefficient u v w i = (pathPolynomial u v w i).coeff 2 := by
  have h := (eval_coefficients (pathPolynomial u v w i)).1
  rw [evaluation_pathPolynomial] at h
  rw [quadraticCoefficient, h]
  ring

theorem cubicCoefficient_eq_coeff (u v w : Fin 9 → ℚ) (i : Fin 10) :
    cubicCoefficient u v w i = (pathPolynomial u v w i).coeff 3 := by
  have h := (eval_coefficients (pathPolynomial u v w i)).2
  rw [evaluation_pathPolynomial] at h
  rw [cubicCoefficient, h]
  ring

private lemma eval_dual_coeff_one (p : ℚ[X]) :
    (p.eval₂ (inlHom ℚ) DualNumber.eps).snd = p.coeff 1 := by
  induction p using Polynomial.induction_on' with
  | monomial n c =>
    rw [eval₂_monomial, coeff_monomial]
    rcases n with _ | n
    · simp [inlHom]
    rcases n with _ | n
    · rw [zero_add, pow_one, if_pos rfl]
      change ((TrivSqZeroExt.inl c : D₁) * DualNumber.eps).snd = c
      rw [TrivSqZeroExt.inl_mul_eq_smul]
      rw [TrivSqZeroExt.snd_smul, DualNumber.snd_eps]
      exact mul_one c
    · have he : (DualNumber.eps : D₁) ^ (2 : ℕ) = 0 := by
        apply TrivSqZeroExt.ext <;> decide +kernel
      rw [show n + 1 + 1 = 2 + n by omega, pow_add, he, zero_mul, mul_zero]
      simp [show 2 + n ≠ 1 by omega]
  | add p q hp hq =>
    rw [eval₂_add, TrivSqZeroExt.snd_add, coeff_add, hp, hq]

theorem linearCoefficient_basis (u : Fin 9 → ℚ) (i : Fin 10) (j : Fin 9) :
    (pathPolynomial u (fun k => if k = j then 1 else 0) 0 i).coeff 1 = rawJacobian u i j := by
  rw [← eval_dual_coeff_one]
  let F : ℚ[X] →+* D₁ := eval₂RingHom (inlHom ℚ) DualNumber.eps
  change (F (pathPolynomial u (fun k => if k = j then 1 else 0) 0 i)).snd = _
  unfold pathPolynomial rawJacobian
  rw [map_raw F]
  congr 2
  funext k
  have hC (r : ℚ) : F (C r) = TrivSqZeroExt.inl r := by
    change (C r).eval₂ (inlHom ℚ) DualNumber.eps = _
    rw [eval₂_C]
    rfl
  have hX : F X = (DualNumber.eps : D₁) := by
    change (X : ℚ[X]).eval₂ (inlHom ℚ) DualNumber.eps = _
    rw [eval₂_X]
  change F (C (u k) + C (if k = j then 1 else 0) * X + C 0 * X ^ 2) = _
  rw [map_add, map_add, map_mul, map_mul, hC, hC, hC, hX]
  have hadd (a b : ℚ) : (TrivSqZeroExt.inl a + TrivSqZeroExt.inr b : D₁) = ⟨a, b⟩ := by
    apply TrivSqZeroExt.ext <;> simp
  by_cases h : k = j <;>
    simp only [h, ite_true, ite_false, TrivSqZeroExt.inl_zero, TrivSqZeroExt.inl_one,
      zero_mul, add_zero, one_mul, DualNumber.eps, hadd]
  · exact add_zero _
  · rfl

/-- Evaluation of the verified rational path polynomial agrees with the raw
real observation along the same path. -/
theorem eval_pathPolynomial_real (u v w : Fin 9 → ℚ) (i : Fin 10) (t : ℝ) :
    (pathPolynomial u v w i).eval₂ (Rat.castHom ℝ) t =
      raw (fun k => (u k : ℝ) + (v k : ℝ) * t + (w k : ℝ) * t ^ 2) i := by
  let F : ℚ[X] →+* ℝ := eval₂RingHom (Rat.castHom ℝ) t
  change F (pathPolynomial u v w i) = _
  rw [pathPolynomial, map_raw F]
  congr 1
  funext k
  simp [F]

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteJetReflection
