/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteJetReflection
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteJetReflection
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteJetCoordinates]
   utility: none
   digest: Dual-number evaluation certifies coefficients of the six-site observation polynomial. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteJetCoordinates
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSFiveSiteJetReflection

/-! Scalar specialization identifies the six-site dual-number certificates with
coefficients of the polynomial obtained from the same chart. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSSixSiteJetReflection

open PeriodicMPSSixSiteCoordinates PeriodicMPSSixSiteMarginal
  PeriodicMPSSixSiteJetCoordinates Polynomial

open private amplitude entry readout D₁ D₂ D₃ pathInput jet
  from D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteJetCoordinates
open private mapGaussian mapGaussian_mk mapGaussian_star inlHom evaluateJet
  constantHom_apply eval_coefficients eval_dual_coeff_one
  from D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSFiveSiteJetReflection

private theorem map_coordinates {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (T U V d e k : R) :
    f ∘ coordinates T U V d e k = coordinates (f T) (f U) (f V) (f d) (f e) (f k) := by
  funext i
  fin_cases i <;> simp [coordinates, map_ofNat]

private lemma map_amplitude {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (u : Fin 9 → R) :
    mapGaussian f ∘ amplitude u = amplitude (f ∘ u) := by
  simp only [amplitude, map_coordinates, map_mul, map_pow, map_one,
    mapGaussian_mk, Function.comp_apply]

private lemma map_entry {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (u : Fin 9 → R) (i j : Fin 4) :
    mapGaussian f (entry (u 8) (amplitude u) i j) =
      entry ((f ∘ u) 8) (amplitude (f ∘ u)) i j := by
  have hm (a : Fin 4) (b : Fin 16) :
      mapGaussian f (flatten (amplitude u) a b) = flatten (amplitude (f ∘ u)) a b :=
    congrFun (map_amplitude f u) (necklaceTable a b)
  simp only [entry, map_mul, map_sum, mapGaussian_mk, RingHom.map_zero,
    Function.comp_apply, mapGaussian_star, hm]

/-- The six-site raw readout commutes with specialization of the scalar ring. -/
theorem map_raw {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (u : Fin 9 → R) (i : Fin 10) :
    f (raw u i) = raw (f ∘ u) i := by
  fin_cases i <;> first
  | exact congrArg QuadraticAlgebra.re (map_entry f u _ _)
  | exact congrArg QuadraticAlgebra.im (map_entry f u _ _)

noncomputable section

/-- The raw observation along the quadratic source path, over the rationals. -/
def pathPolynomial (u v w : Fin 9 → ℚ) (i : Fin 10) : ℚ[X] :=
  raw (fun k => C (u k) + C (v k) * X + C (w k) * X ^ 2) i

/-- The real evaluation of the rational polynomial is the raw chart along the real path. -/
theorem eval_pathPolynomial_real (u v w : Fin 9 → ℚ) (i : Fin 10) (t : ℝ) :
    (pathPolynomial u v w i).eval₂ (Rat.castHom ℝ) t =
      raw (fun k => (u k : ℝ) + (v k : ℝ) * t + (w k : ℝ) * t ^ 2) i := by
  let F : ℚ[X] →+* ℝ := eval₂RingHom (Rat.castHom ℝ) t
  change F (pathPolynomial u v w i) = _
  rw [pathPolynomial, map_raw F]
  congr 1
  funext k
  simp [F]

private local instance : CommRing D₁ := TrivSqZeroExt.commRing
private local instance : CommRing D₂ := TrivSqZeroExt.commRing
private local instance : CommRing D₃ := TrivSqZeroExt.commRing

private lemma evaluation_pathPolynomial (u v w : Fin 9 → ℚ) (i : Fin 10) :
    evaluateJet (pathPolynomial u v w i) = jet u v w i := by
  unfold pathPolynomial jet
  rw [map_raw]
  congr 1
  funext k
  simp [evaluateJet, constantHom_apply, pathInput] <;> rfl

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

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSSixSiteJetReflection
