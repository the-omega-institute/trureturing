/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSFiveSiteAnalyticDerivative
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSFiveSiteAnalyticDerivative
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [mathlib/module/Mathlib.Analysis.Analytic.Polynomial]
   utility: none
   digest: The rational five-site Jacobian gives the real Fréchet derivative in the trace chart. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSFiveSiteJetReflection
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! The raw trace-chart observation is polynomial, with the verified rational
Jacobian determining its differential at rational points. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteAnalyticDerivative

open PeriodicMPSFiveSiteJetCoordinates PeriodicMPSFiveSiteJetReflection

/-- Each real raw observation entry is analytic in the nine trace-chart inputs. -/
theorem analytic_raw (u : Fin 9 → ℝ) (i : Fin 10) :
    AnalyticAt ℝ (fun q : Fin 9 → ℝ => raw q i) u := by
  let p := raw (R := MvPolynomial (Fin 9) ℝ) MvPolynomial.X i
  have h (q : Fin 9 → ℝ) : MvPolynomial.aeval q p = raw q i := by
    let F : MvPolynomial (Fin 9) ℝ →+* ℝ := (MvPolynomial.aeval q).toRingHom
    have hmap := map_raw F MvPolynomial.X i
    simpa [F, p, Function.comp_def] using hmap
  simp_rw [← h]
  exact AnalyticAt.aeval_mvPolynomial
    (fun j => (ContinuousLinearMap.proj j : (Fin 9 → ℝ) →L[ℝ] ℝ).analyticAt u) p

/-- The checked Jacobian entry equals the derivative on its coordinate basis vector. -/
theorem fderiv_raw_basis (u : Fin 9 → ℚ) (i : Fin 10) (j : Fin 9) :
    fderiv ℝ (fun q : Fin 9 → ℝ => raw q i) (fun k => (u k : ℝ))
      (fun k => if k = j then 1 else 0) =
    (rawJacobian u i j : ℝ) := by
  let base : Fin 9 → ℝ := fun k => (u k : ℝ)
  let v : Fin 9 → ℚ := fun k => if k = j then 1 else 0
  let e : Fin 9 → ℝ := fun k => if k = j then 1 else 0
  let path : ℝ → Fin 9 → ℝ := fun t => base + t • e
  let p := (pathPolynomial u v 0 i).map (Rat.castHom ℝ)
  have he (k : Fin 9) : (v k : ℝ) = e k := by
    by_cases h : k = j <;> simp [v, e, h]
  have heval (t : ℝ) : (p.eval t) = raw (path t) i := by
    dsimp only [p]
    rw [Polynomial.eval_map, eval_pathPolynomial_real]
    congr 1
    funext k
    simp [path, base, he, mul_comm]
  have hpath : HasDerivAt path e 0 := by
    simpa [path] using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add base
  have hdiff := (analytic_raw base i).hasStrictFDerivAt.hasFDerivAt
  have hc := hdiff.comp_hasDerivAt_of_eq (0 : ℝ) hpath
    (show base = path 0 by simp [path])
  have hd : HasDerivAt (fun t => p.eval t)
      (fderiv ℝ (fun q : Fin 9 → ℝ => raw q i) base e) 0 := by
    exact hc.congr_of_eventuallyEq (Filter.Eventually.of_forall heval)
  rw [← hd.deriv, (p.hasDerivAt (0 : ℝ)).deriv, ← Polynomial.coeff_zero_eq_eval_zero,
    Polynomial.coeff_derivative]
  simp [p, Polynomial.coeff_map, v, linearCoefficient_basis]

/-- The real differential acts by the checked rational matrix. -/
theorem fderiv_raw_apply (u : Fin 9 → ℚ) (i : Fin 10) (v : Fin 9 → ℝ) :
    fderiv ℝ (fun q : Fin 9 → ℝ => raw q i) (fun k => (u k : ℝ)) v =
      ∑ j, (rawJacobian u i j : ℝ) * v j := by
  have hv : ∑ j : Fin 9, v j • (fun k : Fin 9 => if k = j then (1 : ℝ) else 0) = v := by
    funext k
    simp [Finset.sum_apply, Pi.smul_apply, mul_ite]
  conv_lhs => rw [← hv]
  simp only [map_sum, map_smul, fderiv_raw_basis, smul_eq_mul]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- The first coefficient along a quadratic rational path is the
differential on its first-order direction. -/
theorem linearCoefficient_real (u v w : Fin 9 → ℚ) (i : Fin 10) :
    ((pathPolynomial u v w i).coeff 1 : ℝ) =
      ∑ j, (rawJacobian u i j : ℝ) * (v j : ℝ) := by
  let b : Fin 9 → ℝ := fun k => (u k : ℝ)
  let d : Fin 9 → ℝ := fun k => (v k : ℝ)
  let c : Fin 9 → ℝ := fun k => (w k : ℝ)
  let path : ℝ → Fin 9 → ℝ := fun t => b + t • d + t ^ 2 • c
  let p := (pathPolynomial u v w i).map (Rat.castHom ℝ)
  have heval (t : ℝ) : (p.eval t) = raw (path t) i := by
    dsimp only [p]
    rw [Polynomial.eval_map, eval_pathPolynomial_real]
    congr 1
    funext k
    simp [path, b, d, c, mul_comm]
  have hpath : HasDerivAt path d 0 := by
    simpa [path, Pi.add_def] using (((hasDerivAt_id (0 : ℝ)).smul_const d).const_add b).add
      (((hasDerivAt_id (0 : ℝ)).pow 2).smul_const c)
  have hc := (analytic_raw b i).hasStrictFDerivAt.hasFDerivAt.comp_hasDerivAt_of_eq
    (0 : ℝ) hpath (show b = path 0 by simp [path])
  have hd : HasDerivAt (fun t => p.eval t)
      (fderiv ℝ (fun q : Fin 9 → ℝ => raw q i) b d) 0 :=
    hc.congr_of_eventuallyEq (Filter.Eventually.of_forall heval)
  have hp := hd.deriv
  rw [(p.hasDerivAt (0 : ℝ)).deriv, ← Polynomial.coeff_zero_eq_eval_zero,
    Polynomial.coeff_derivative, fderiv_raw_apply] at hp
  simpa [p, Polynomial.coeff_map, d] using hp

end D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteAnalyticDerivative
