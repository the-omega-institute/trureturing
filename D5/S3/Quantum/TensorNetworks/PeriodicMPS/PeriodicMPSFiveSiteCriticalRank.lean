/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSFiveSiteCriticalRank
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSFiveSiteCriticalRank
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSFiveSiteCriticalChart]
   utility: none
   digest: Rank loss of the normalized observation forces both critical minors to vanish. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSFiveSiteCriticalChart
import D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteOrdinaryTrace
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Linear
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! The complexified Jacobian has separate weighted Euler vectors for the two
trace tuples. A normalized physical kernel supplies an independent kernel
direction after correcting its radial part. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteCriticalRank

open Matrix hiding gram
open MvPolynomial PeriodicMPSFiveSiteCoordinates
  PeriodicMPSFiveSiteLineMinors PeriodicMPSFiveSiteWeightedMinors
  PeriodicMPSFiveSiteOrdinaryTrace PeriodicMPSFiveSiteNormalization
  PeriodicMPSFiveSiteSpecialFiber
open scoped ComplexConjugate Matrix.Norms.Elementwise Topology

open private observedRows amplitudes map_coordinates map_flatten
  from D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteLineMinors
open private rightWeights observation_right_weight
  from D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSFiveSiteCriticalChart

noncomputable section

/-- The ordinary trace tuple and its conjugate after setting both first traces to one. -/
def conjugatedTuple (q : Parameters) : Fin 10 → ℂ :=
  ![1, q 0, q 1, q 3, q 0 - q 2, 1, conj (q 0), conj (q 1), conj (q 3),
    conj (q 0) - conj (q 2)]

private def conjugatedDirection (v : Parameters) : Fin 10 → ℂ :=
  ![0, v 0, v 1, v 3, v 0 - v 2, 0, conj (v 0), conj (v 1), conj (v 3),
    conj (v 0) - conj (v 2)]

private theorem conjugatedDirection_ne_zero (v : Parameters) (hv : v ≠ 0) :
    conjugatedDirection v ≠ 0 := by
  intro h
  have h₀ : v 0 = 0 := congrFun h (1 : Fin 10)
  have h₁ : v 1 = 0 := congrFun h (2 : Fin 10)
  have h₃ : v 3 = 0 := congrFun h (3 : Fin 10)
  have h₂ : v 2 = 0 := by
    have e : v 0 - v 2 = 0 := congrFun h (4 : Fin 10)
    simpa [h₀] using e
  apply hv
  funext i
  fin_cases i
  · exact h₀
  · exact h₁
  · exact h₂
  · exact h₃

private theorem conjugatedTuple_line (q v : Parameters) (r : ℝ) :
    conjugatedTuple (q + r • v) = conjugatedTuple q + r • conjugatedDirection v := by
  funext i
  fin_cases i <;> simp [conjugatedTuple, conjugatedDirection, Complex.real_smul] <;> ring

/-- The normalized physical observation in the ordinary trace chart. -/
def normalizedObservation (q : Parameters) : Matrix (Fin 4) (Fin 4) ℂ :=
  normalizedGram (amplitude q)

private theorem analyticAt_gramEntry (q : Parameters) (i j : Fin 4) :
    AnalyticAt ℝ (fun z : Parameters => gram (amplitude z) i j) q := by
  have ha (k : Fin 8) : AnalyticAt ℝ (fun z : Parameters => amplitude z k) q := by
    let p : MvPolynomial (Fin 4) ℂ := coordinates 1 (X 0) (X 1) (X 3) (X 0 - X 2) k
    have he (z : Parameters) : MvPolynomial.aeval z p = amplitude z k := by
      rw [amplitude_eq]
      have h := congrFun (map_coordinates (MvPolynomial.aeval z).toRingHom
        (1 : MvPolynomial (Fin 4) ℂ) (X 0) (X 1) (X 3) (X 0 - X 2)) k
      simpa [p, Function.comp_def] using h
    simp_rw [← he]
    exact AnalyticAt.aeval_mvPolynomial
      (fun a => (ContinuousLinearMap.proj a : Parameters →L[ℝ] ℂ).analyticAt q) p
  have hf (r : Fin 4) (s : Fin 8) :
      AnalyticAt ℝ (fun z : Parameters => flatten (amplitude z) r s) q := by
    have h (p : Fin 8 → ℂ) : flatten p r s = p (flatten id r s) := by
      fin_cases r <;> fin_cases s <;> rfl
    simp only [h]
    exact ha _
  simp only [gram, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def]
  apply Finset.analyticAt_fun_sum
  intro k _
  let coord := fun z : Parameters => flatten (amplitude z) j k
  exact (hf i k).mul
    (AnalyticAt.fun_comp_of_eq (f := coord)
      ((Complex.conjCLE : ℂ →L[ℝ] ℂ).analyticAt (coord q)) (hf j k) rfl)

private def chartMass (q : Parameters) : ℝ := mass (amplitude q)

private theorem analyticAt_chartMass (q : Parameters) : AnalyticAt ℝ chartMass q := by
  let total := fun z : Parameters => (gram (amplitude z)).trace
  have ht : AnalyticAt ℝ total q := by
    unfold total Matrix.trace Matrix.diag
    exact Finset.analyticAt_fun_sum _ fun i _ => analyticAt_gramEntry q i i
  exact AnalyticAt.fun_comp_of_eq (f := total) (Complex.reCLM.analyticAt (total q)) ht rfl

/-- The ordinary normalized observation is real analytic at every nonzero amplitude. -/
theorem analyticAt_normalizedObservation (q : Parameters) (hq : q ∈ domain) :
    AnalyticAt ℝ normalizedObservation q := by
  apply analyticAt_pi_iff.mpr
  intro i
  apply analyticAt_pi_iff.mpr
  intro j
  exact ((analyticAt_chartMass q).inv (mass_positive _ hq).ne').smul (analyticAt_gramEntry q i j)

private theorem observation_conjugatedTuple (q : Parameters) (i : Fin 10) :
    observation (conjugatedTuple q) i =
      gram (amplitude q) (observedRows i).1 (observedRows i).2 := by
  have hl : amplitudes (conjugatedTuple q) true = amplitude q := by
    rw [amplitude_eq]
    rfl
  have hr : amplitudes (conjugatedTuple q) false = conj ∘ amplitude q := by
    rw [amplitude_eq]
    symm
    simpa [amplitudes, conjugatedTuple] using
      map_coordinates (starRingEnd ℂ) (1 : ℂ) (q 0) (q 1) (q 3) (q 0 - q 2)
  simp only [observation, hl, hr, gram, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.star_def]
  apply Finset.sum_congr rfl
  intro k _
  rw [← map_flatten (starRingEnd ℂ)]
  rfl

private def evalAt (a : Fin 10 → ℂ) : P →+* ℂ :=
  MvPolynomial.eval₂Hom (Int.castRingHom ℂ) a

private theorem evalAt_observation (a : Fin 10 → ℂ) (i : Fin 10) :
    evalAt a (observation (R := P) X i) = observation a i := by
  simpa [evalAt, Function.comp_def] using map_observation (evalAt a) X i

private theorem evalAt_pderiv (a : Fin 10 → ℂ) (i j : Fin 10) :
    evalAt a (pderiv j (observation (R := P) X i)) = jacobian a i j :=
  evaluated_derivative a i j

private def slope (a v : Fin 10 → ℂ) (p : P) : ℂ :=
  ∑ j, evalAt a (pderiv j p) * v j

private theorem evalAt_derivative (a v : Fin 10 → ℂ) (p : P) :
    HasDerivAt (fun r : ℝ => evalAt (a + r • v) p) (slope a v p) 0 := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    simpa [slope, evalAt] using (hasDerivAt_const (0 : ℝ) (c : ℂ))
  | add p p' hp hp' =>
    simpa [slope, add_mul, Finset.sum_add_distrib] using hp.fun_add hp'
  | mul_X p i hp =>
    have hi : HasDerivAt (fun r : ℝ => (a + r • v) i) (v i) 0 := by
      simpa [Complex.real_smul] using
        (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ)).mul_const (v i)).const_add (a i)
    have hsum : ∑ j, evalAt a (pderiv j (X i : P)) * v j = v i := by
      classical
      simp [pderiv_X, Pi.single_apply]
    have hstep : slope a v (p * X i) = slope a v p * a i + evalAt a p * v i := by
      unfold slope
      simp_rw [pderiv_mul, map_add, map_mul, show evalAt a (X i : P) = a i from
        MvPolynomial.eval₂Hom_X' _ _ _, add_mul, Finset.sum_add_distrib]
      rw [← hsum, Finset.sum_mul, Finset.mul_sum]
      congr 1
      · exact Finset.sum_congr rfl fun j _ => by ring
      · exact Finset.sum_congr rfl fun j _ => by ring
    rw [hstep]
    simpa [evalAt] using hp.fun_mul hi

private theorem observation_derivative (a v : Fin 10 → ℂ) (i : Fin 10) :
    HasDerivAt (fun r : ℝ => observation (a + r • v) i) ((jacobian a *ᵥ v) i) 0 := by
  have h := evalAt_derivative a v (observation (R := P) X i)
  simpa only [evalAt_observation, slope, evalAt_pderiv, Matrix.mulVec, dotProduct] using h

private def weightedDirection (w : Fin 10 → ℕ) (a : Fin 10 → ℂ) : Fin 10 → ℂ :=
  fun j => (w j : ℂ) * a j

private theorem euler (a : Fin 10 → ℂ) (w : Fin 10 → ℕ) (n : ℕ)
    (hw : ∀ i, (observation (R := P) X i).IsWeightedHomogeneous w n) :
    jacobian a *ᵥ weightedDirection w a = (n : ℂ) • observation a := by
  funext i
  have h := congrArg (evalAt a) (hw i).sum_weight_X_mul_pderiv
  simp only [map_sum, map_nsmul, map_mul, evalAt_pderiv, evalAt_observation,
    show ∀ j, evalAt a (X j : P) = a j from fun j => MvPolynomial.eval₂Hom_X' _ _ _] at h
  simp only [nsmul_eq_mul] at h
  change (∑ j, jacobian a i j * ((w j : ℂ) * a j)) = (n : ℂ) * observation a i
  rw [← h]
  exact Finset.sum_congr rfl fun j _ => by ring

private theorem deletedMinor_eq_zero (J : Matrix (Fin 10) (Fin 10) ℂ) (k : Fin 10)
    {v : Fin 10 → ℂ} (hv : v ≠ 0) (hvk : v k = 0) (hJ : J *ᵥ v = 0) :
    (J.submatrix k.succAbove k.succAbove).det = 0 := by
  let v' := v ∘ k.succAbove
  have hv' : v' ≠ 0 := by
    intro h
    apply hv
    funext j
    by_cases hj : j = k
    · simpa [hj] using hvk
    · obtain ⟨t, rfl⟩ := Fin.exists_succAbove_eq hj
      exact congrFun h t
  have hm : J.submatrix k.succAbove k.succAbove *ᵥ v' = 0 := by
    funext i
    have h : ∑ j, J (k.succAbove i) j * v j = 0 := congrFun hJ (k.succAbove i)
    rw [Fin.sum_univ_succAbove _ k, hvk, mul_zero, zero_add] at h
    exact h
  by_contra hd
  have hinj := Matrix.mulVec_injective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hd))
  exact hv' (hinj (hm.trans (Matrix.mulVec_zero _).symm))

private theorem minors_of_two_kernel_directions (J : Matrix (Fin 10) (Fin 10) ℂ)
    {h p : Fin 10 → ℂ} (hh : h ≠ 0) (hh₀ : h 0 = 0) (hp₀ : p 0 = 1)
    (hJh : J *ᵥ h = 0) (hJp : J *ᵥ p = 0) (k : Fin 10) :
    (J.submatrix k.succAbove k.succAbove).det = 0 := by
  by_cases hk : p k = 0
  · exact deletedMinor_eq_zero J k (fun e => by
      have he : p 0 = 0 := congrFun e (0 : Fin 10)
      exact one_ne_zero (hp₀.symm.trans he)) hk hJp
  let v := h - (h k / p k) • p
  have hvk : v k = 0 := by simp [v, div_mul_cancel₀ _ hk]
  have hJv : J *ᵥ v = 0 := by simp [v, Matrix.mulVec_sub, Matrix.mulVec_smul, hJh, hJp]
  have hv : v ≠ 0 := by
    intro he
    have hcoef : h k / p k = 0 := by
      simpa [v, hh₀, hp₀] using (congrFun he (0 : Fin 10))
    exact hh (by simpa [v, hcoef] using he)
  exact deletedMinor_eq_zero J k hv hvk hJv

private theorem chartJacobian_minor_of_radial (q : Parameters) (a : Fin 10 → ℂ)
    (ha : a = conjugatedTuple q) (v : Parameters) (hv : v ≠ 0) (gain : ℂ)
    (h : jacobian a *ᵥ conjugatedDirection v = gain • observation a) (k : Fin 10) :
    (jacobian a |>.submatrix k.succAbove k.succAbove).det = 0 := by
  let R := weightedDirection rightWeights a
  let T := weightedDirection weights a
  have hR₀ : R 0 = 0 := by simp [R, weightedDirection, rightWeights]
  have hR₅ : R 5 = 1 := by simp [R, weightedDirection, rightWeights, weights, ha, conjugatedTuple]
  have hT₀ : T 0 = 1 := by simp [T, weightedDirection, weights, ha, conjugatedTuple]
  have hR : jacobian a *ᵥ R = (5 : ℂ) • observation a := by
    simpa [R] using euler a rightWeights 5 observation_right_weight
  have hT : jacobian a *ᵥ T = (10 : ℂ) • observation a := by
    simpa [T] using euler a weights 10 observation_weight
  let p := T - (2 : ℂ) • R
  let b := conjugatedDirection v - (gain / 5) • R
  have hp₀ : p 0 = 1 := by simp [p, hT₀, hR₀]
  have hb₀ : b 0 = 0 := by
    change 0 - (gain / 5) * R 0 = 0
    simp [hR₀]
  have hpJ : jacobian a *ᵥ p = 0 := by
    dsimp only [p]
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hT, hR, smul_smul, show (2 : ℂ) * 5 = 10 by norm_num,
      sub_self]
  have hbJ : jacobian a *ᵥ b = 0 := by
    dsimp only [b]
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, h, hR, smul_smul,
      div_mul_cancel₀ _ (by norm_num), sub_self]
  have hb : b ≠ 0 := by
    intro he
    have hg : gain / 5 = 0 := by
      have hc := congrFun he (5 : Fin 10)
      change 0 - (gain / 5) * R 5 = 0 at hc
      simpa only [hR₅, mul_one, zero_sub, neg_eq_zero] using hc
    exact conjugatedDirection_ne_zero v hv (by simpa [b, hg] using he)
  exact minors_of_two_kernel_directions (jacobian a) hb hb₀ hp₀ hbJ hpJ k

/-- A nonzero kernel vector of the normalized differential forces each indicated
weighted symbolic minor to vanish at the conjugated ordinary trace tuple. -/
theorem evaluated_minor_eq_zero_of_kernel (q : Parameters) (hq : q ∈ domain)
    (v : Parameters) (hv : v ≠ 0) (hker : fderiv ℝ normalizedObservation q v = 0) (k : Fin 10) :
    MvPolynomial.eval₂ (Int.castRingHom ℂ) (conjugatedTuple q) (symbolicMinor k) = 0 := by
  let a := conjugatedTuple q
  let u := conjugatedDirection v
  let path := fun r : ℝ => q + r • v
  have hpath : HasDerivAt path v 0 := by
    simpa [path] using ((hasDerivAt_id' (0 : ℝ)).smul_const v).const_add q
  have hzero : q = path 0 := by simp [path]
  let s' := fderiv ℝ chartMass q v
  have hmass : HasDerivAt (chartMass ∘ path) s' 0 :=
    (analyticAt_chartMass q).differentiableAt.hasFDerivAt.comp_hasDerivAt_of_eq 0 hpath hzero
  have hnorm : HasDerivAt (normalizedObservation ∘ path) 0 0 := by
    rw [← hker]
    have hd := (analyticAt_normalizedObservation q hq).differentiableAt.hasFDerivAt
    exact hd.comp_hasDerivAt_of_eq 0 hpath hzero
  have hm : chartMass q ≠ 0 := (mass_positive _ hq).ne'
  have hevent : ∀ᶠ r in 𝓝 (0 : ℝ), chartMass (path r) ≠ 0 :=
    (hmass.continuousAt.eventually_ne (by rwa [Function.comp_apply, ← hzero]))
  have hradial : jacobian a *ᵥ u = (↑(s' / chartMass q) : ℂ) • observation a := by
    funext i
    let e : Matrix (Fin 4) (Fin 4) ℂ →L[ℝ] ℂ :=
      (ContinuousLinearMap.proj (observedRows i).2 : (Fin 4 → ℂ) →L[ℝ] ℂ).comp
        (ContinuousLinearMap.proj (observedRows i).1 :
          (Fin 4 → Fin 4 → ℂ) →L[ℝ] (Fin 4 → ℂ))
    have hn : HasDerivAt (fun r => e (normalizedObservation (path r))) 0 0 := by
      have hd : HasDerivAt (fun r : ℝ => e (normalizedObservation (path r))) (e 0) 0 :=
        e.hasFDerivAt.comp_hasDerivAt 0 hnorm
      exact (congrArg (fun d : ℂ =>
        HasDerivAt (fun r : ℝ => e (normalizedObservation (path r))) d 0) e.map_zero).mp hd
    have hproduct := hmass.smul hn
    have hvalue : HasDerivAt (fun r : ℝ => observation (a + r • u) i)
        (s' • e (normalizedObservation q)) 0 := by
      simp only [Function.comp_apply, ← hzero, smul_zero, zero_add] at hproduct
      refine hproduct.congr_of_eventuallyEq ?_
      filter_upwards [hevent] with r hr
      rw [show a + r • u = conjugatedTuple (path r) from (conjugatedTuple_line q v r).symm,
        observation_conjugatedTuple]
      change gram (amplitude (path r)) (observedRows i).1 (observedRows i).2 =
        chartMass (path r) • ((chartMass (path r))⁻¹ •
          gram (amplitude (path r)) (observedRows i).1 (observedRows i).2)
      rw [smul_smul, mul_inv_cancel₀ hr, one_smul]
    rw [(observation_derivative a u i).unique hvalue]
    change s' • ((chartMass q)⁻¹ • gram (amplitude q) (observedRows i).1 (observedRows i).2) =
      (↑(s' / chartMass q) : ℂ) * observation a i
    rw [smul_smul, ← div_eq_mul_inv, observation_conjugatedTuple]
    rfl
  have hJ := chartJacobian_minor_of_radial q a rfl v hv _ hradial k
  change evalAt a (symbolicMinor k) = 0
  rw [symbolicMinor, RingHom.map_det]
  have he : (evalAt a).mapMatrix (Matrix.of fun i j : Fin 9 =>
      pderiv (k.succAbove j) (observation (R := P) X (k.succAbove i))) =
      (jacobian a).submatrix k.succAbove k.succAbove := by
    ext i j
    exact evalAt_pderiv a _ _
  rwa [he]

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteCriticalRank
