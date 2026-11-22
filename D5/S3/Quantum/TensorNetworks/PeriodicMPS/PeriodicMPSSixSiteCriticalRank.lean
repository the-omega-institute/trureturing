/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteCriticalRank
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteCriticalRank
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteWeightedMinors]
   utility: none
   digest: Rank loss of the normalized six-site Gram forces the critical minors to vanish. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSFiveSiteCriticalRank
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSitePhysicalObservation
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteWeightedMinors

/-! The two trace scalings supply Euler directions for the complexified observation.
Subtracting the mass derivative from a normalized kernel direction yields a second
independent vector in the complexified kernel. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSSixSiteCriticalRank

open Matrix hiding gram
open MvPolynomial PeriodicMPSSixSiteCoordinates PeriodicMPSSixSiteMarginal
  PeriodicMPSSixSiteLineMinors PeriodicMPSSixSiteWeightedMinors
open PeriodicMPSWeightedDehomogenization (eval₂Hom_homogeneous)
open PeriodicMPSSixSiteCompactSource (graphPoint normalizedGram gram_mass_pos)
open PeriodicMPSFiveSitePhysicalObservation (entries)
open scoped ComplexConjugate Matrix.Norms.Elementwise Topology

open private observedRows amplitudes map_coordinates
  from D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteLineMinors
open private entries_smul from D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSFiveSitePhysicalObservation
open private coordinates_weight
  from D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteWeightedMinors
open private evalAt evalAt_derivative slope minors_of_two_kernel_directions
  from D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSFiveSiteCriticalRank

noncomputable section

abbrev Parameters := Fin 4 → ℂ

/-- The weight-two invariant chart with the first squared trace normalized to one. -/
def invariantTuple (q : Parameters) : Fin 6 → ℂ :=
  ![1, q 0, q 0 ^ 2, q 1, q 2, q 3]

/-- The amplitudes in the first-trace chart. -/
def chartAmplitude (q : Parameters) : Fin 14 → ℂ :=
  PeriodicMPSSixSiteCompactSource.amplitude (invariantTuple q)

/-- The locus on which the physical Gram has a nonzero trace. -/
def domain : Set Parameters := {q | chartAmplitude q ≠ 0}

/-- The two trace tuples evaluated at a physical point of the first-trace chart. -/
def conjugatedTuple (q : Parameters) : Fin 10 → ℂ :=
  ![1, q 0, q 1, q 2, q 3, 1, conj (q 0), conj (q 1), conj (q 2), conj (q 3)]

private def conjugatedDirection (v : Parameters) : Fin 10 → ℂ :=
  ![0, v 0, v 1, v 2, v 3, 0, conj (v 0), conj (v 1), conj (v 2), conj (v 3)]

private theorem conjugatedDirection_ne_zero (v : Parameters) (hv : v ≠ 0) :
    conjugatedDirection v ≠ 0 := by
  intro h
  apply hv
  funext j
  fin_cases j
  · exact congrFun h (1 : Fin 10)
  · exact congrFun h (2 : Fin 10)
  · exact congrFun h (3 : Fin 10)
  · exact congrFun h (4 : Fin 10)

private theorem conjugatedTuple_line (q v : Parameters) (r : ℝ) :
    conjugatedTuple (q + r • v) = conjugatedTuple q + r • conjugatedDirection v := by
  funext i
  fin_cases i <;> simp [conjugatedTuple, conjugatedDirection, Complex.real_smul] <;> ring

private def chartMass (q : Parameters) : ℝ := (gram (chartAmplitude q)).trace.re

/-- The normalized physical observation in the first-trace chart. -/
def normalizedObservation (q : Parameters) : Matrix (Fin 4) (Fin 4) ℂ :=
  normalizedGram (chartAmplitude q)

theorem normalizedObservation_eq_observation (q : Parameters) (hq : q ∈ domain) :
    normalizedObservation q =
      PeriodicMPSSixSiteCompactSource.observation (graphPoint (invariantTuple q)) :=
  (PeriodicMPSSixSiteCompactSource.observation_of_projector
    (x := graphPoint (invariantTuple q)) (p := chartAmplitude q) hq rfl).symm

private theorem analyticAt_chartAmplitude (q : Parameters) (k : Fin 14) :
    AnalyticAt ℝ (fun z : Parameters => chartAmplitude z k) q := by
  let p : MvPolynomial (Fin 4) ℂ := coordinates 1 (X 0) (X 0 ^ 2) (X 1) (X 2) (X 3) k
  have he (z : Parameters) : MvPolynomial.aeval z p = chartAmplitude z k := by
    change MvPolynomial.aeval z p = coordinates 1 (z 0) (z 0 ^ 2) (z 1) (z 2) (z 3) k
    have h := congrFun (map_coordinates (MvPolynomial.aeval z).toRingHom
      (1 : MvPolynomial (Fin 4) ℂ) (X 0) (X 0 ^ 2) (X 1) (X 2) (X 3)) k
    simpa [p, Function.comp_def, map_pow] using h
  simp_rw [← he]
  exact AnalyticAt.aeval_mvPolynomial
    (fun j => (ContinuousLinearMap.proj j : Parameters →L[ℝ] ℂ).analyticAt q) p

theorem isOpen_domain : IsOpen domain := by
  have h : Continuous chartAmplitude :=
    continuous_pi fun k => continuous_iff_continuousAt.mpr
      fun q => (analyticAt_chartAmplitude q k).continuousAt
  exact isOpen_ne_fun h continuous_const

private theorem analyticAt_gramEntry (q : Parameters) (i j : Fin 4) :
    AnalyticAt ℝ (fun z : Parameters => gram (chartAmplitude z) i j) q := by
  simp only [gram, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def]
  apply Finset.analyticAt_fun_sum
  intro k _
  let coord := fun z : Parameters => chartAmplitude z (necklaceTable j k)
  exact (analyticAt_chartAmplitude q (necklaceTable i k)).mul
    (AnalyticAt.fun_comp_of_eq (f := coord)
      ((Complex.conjCLE : ℂ →L[ℝ] ℂ).analyticAt (coord q))
      (analyticAt_chartAmplitude q (necklaceTable j k)) rfl)

private theorem analyticAt_chartMass (q : Parameters) : AnalyticAt ℝ chartMass q := by
  let total := fun z : Parameters => (gram (chartAmplitude z)).trace
  have ht : AnalyticAt ℝ total q := by
    unfold total Matrix.trace Matrix.diag
    exact Finset.analyticAt_fun_sum _ fun i _ => analyticAt_gramEntry q i i
  exact AnalyticAt.fun_comp_of_eq (f := total) (Complex.reCLM.analyticAt (total q)) ht rfl

/-- The normalized six-site Gram is real analytic on the open amplitude domain. -/
theorem analyticAt_normalizedObservation (q : Parameters) (hq : q ∈ domain) :
    AnalyticAt ℝ normalizedObservation q := by
  apply analyticAt_pi_iff.mpr
  intro i
  apply analyticAt_pi_iff.mpr
  intro j
  exact ((analyticAt_chartMass q).inv (gram_mass_pos _ hq).ne').smul
    (analyticAt_gramEntry q i j)

set_option maxHeartbeats 1500000 in
-- Identify the finite Gram coordinates on the physical conjugate slice.
private theorem observation_conjugatedTuple (q : Parameters) (i : Fin 10) :
    observation (conjugatedTuple q) i =
      gram (chartAmplitude q) (observedRows i).1 (observedRows i).2 := by
  have hl : amplitudes (conjugatedTuple q) true = chartAmplitude q := by
    change coordinates ((1 : ℂ) ^ 2) (1 * q 0) (q 0 ^ 2) (q 1) (q 2) (q 3) =
      coordinates 1 (q 0) (q 0 ^ 2) (q 1) (q 2) (q 3)
    simp only [one_pow, one_mul]
  have hr : amplitudes (conjugatedTuple q) false = conj ∘ chartAmplitude q := by
    change coordinates ((1 : ℂ) ^ 2) (1 * conj (q 0)) (conj (q 0) ^ 2)
      (conj (q 1)) (conj (q 2)) (conj (q 3)) =
      conj ∘ coordinates 1 (q 0) (q 0 ^ 2) (q 1) (q 2) (q 3)
    rw [one_pow, one_mul]
    let f : ℂ →+* ℂ := starRingEnd ℂ
    have h := map_coordinates f (1 : ℂ) (q 0) (q 0 ^ 2) (q 1) (q 2) (q 3)
    rw [map_one, map_pow] at h
    exact h.symm
  simp only [observation, hl, hr, gram, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.star_def, flatten, Function.comp_apply]

/-- The normalized physical entries in the order of
`PeriodicMPSSixSitePhysicalObservation.raw_eq_entries`. -/
theorem entries_normalizedObservation (q : Parameters) :
    entries (normalizedObservation q) =
      let z := observation (conjugatedTuple q)
      ((gram (chartAmplitude q)).trace.re)⁻¹ •
        ![(z 0).re, (z 1).re, (z 1).im, (z 2).re, (z 2).im, (z 4).re,
          (z 5).re, (z 6).re, (z 6).im, (z 9).re] := by
  rw [normalizedObservation, normalizedGram, entries_smul]
  simp only [observation_conjugatedTuple] <;> rfl

private theorem evalAt_observation (a : Fin 10 → ℂ) (i : Fin 10) :
    evalAt a (observation (R := P) X i) = observation a i := by
  simpa [evalAt, Function.comp_def] using map_observation (evalAt a) X i

private theorem evalAt_pderiv (a : Fin 10 → ℂ) (i j : Fin 10) :
    evalAt a (pderiv j (observation (R := P) X i)) = jacobian a i j :=
  evaluated_derivative a i j

private theorem observation_derivative (a v : Fin 10 → ℂ) (i : Fin 10) :
    HasDerivAt (fun r : ℝ => observation (a + r • v) i) ((jacobian a *ᵥ v) i) 0 := by
  have h := evalAt_derivative a v (observation (R := P) X i)
  change HasDerivAt (fun r : ℝ => evalAt (a + r • v) (observation (R := P) X i))
    (∑ j, evalAt a (pderiv j (observation (R := P) X i)) * v j) 0 at h
  simpa only [evalAt_observation, evalAt_pderiv, Matrix.mulVec, dotProduct] using h

private def rightWeights (j : Fin 10) : ℕ := if j.val < 5 then 0 else weights j

private theorem left_amplitude_right_weight (i : Fin 14) :
    (amplitudes (R := P) X true i).IsWeightedHomogeneous rightWeights 0 := by
  let f : Fin 10 → P := fun j => if j.val < 5 then X j else 0
  have hw (j : Fin 10) : (f j).IsWeightedHomogeneous rightWeights 0 := by
    by_cases hj : j.val < 5
    · simpa [f, rightWeights, hj] using isWeightedHomogeneous_X ℤ rightWeights j
    · simpa [f, hj] using isWeightedHomogeneous_zero ℤ rightWeights 0
  have hs : (amplitudes (R := P) X true i).IsWeightedHomogeneous (fun _ => 0) 0 := by
    intro m _
    simp [Finsupp.weight_apply, Finsupp.sum]
  let F : P →+* P := eval₂Hom C f
  have h : (F (amplitudes (R := P) X true i)).IsWeightedHomogeneous rightWeights 0 :=
    eval₂Hom_homogeneous (fun _ => 0) rightWeights f hw hs
  have e := congrFun (map_coordinates F ((X 0 : P) ^ 2) (X 0 * X 1)
    (X 1 ^ 2) (X 2) (X 3) (X 4)) i
  simp only [Function.comp_apply, map_pow, map_mul, F, eval₂Hom_X'] at e
  change F (amplitudes (R := P) X true i) = _ at e
  rw [e] at h
  simpa [f, amplitudes] using h

private theorem right_amplitude_right_weight (i : Fin 14) :
    (amplitudes (R := P) X false i).IsWeightedHomogeneous rightWeights 6 := by
  let f : Fin 10 → P := fun j => if j.val < 5 then 0 else X j
  have hw (j : Fin 10) : (f j).IsWeightedHomogeneous rightWeights (weights j) := by
    by_cases hj : j.val < 5
    · simpa [f, hj] using isWeightedHomogeneous_zero ℤ rightWeights (weights j)
    · simpa [f, rightWeights, hj] using isWeightedHomogeneous_X ℤ rightWeights j
  have hs := coordinates_weight ((X 5 : P) ^ 2) (X 5 * X 6) (X 6 ^ 2) (X 7) (X 8) (X 9)
    ((isWeightedHomogeneous_X ℤ weights 5).pow 2)
    ((isWeightedHomogeneous_X ℤ weights 5).mul (isWeightedHomogeneous_X ℤ weights 6))
    ((isWeightedHomogeneous_X ℤ weights 6).pow 2)
    (isWeightedHomogeneous_X ℤ weights 7) (isWeightedHomogeneous_X ℤ weights 8)
    (isWeightedHomogeneous_X ℤ weights 9) i
  let F : P →+* P := eval₂Hom C f
  have h : (F (amplitudes (R := P) X false i)).IsWeightedHomogeneous rightWeights 6 :=
    eval₂Hom_homogeneous weights rightWeights f hw hs
  have e := congrFun (map_coordinates F ((X 5 : P) ^ 2) (X 5 * X 6)
    (X 6 ^ 2) (X 7) (X 8) (X 9)) i
  simp only [Function.comp_apply, map_pow, map_mul, F, eval₂Hom_X'] at e
  change F (amplitudes (R := P) X false i) = _ at e
  rw [e] at h
  simpa [f, amplitudes] using h

private theorem observation_right_weight (i : Fin 10) :
    (observation (R := P) X i).IsWeightedHomogeneous rightWeights 6 := by
  classical
  unfold observation
  apply IsWeightedHomogeneous.sum
  intro k _
  exact (left_amplitude_right_weight (necklaceTable (observedRows i).1 k)).mul
    (right_amplitude_right_weight (necklaceTable (observedRows i).2 k))

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

private theorem chartJacobian_minor_of_radial (q v : Parameters) (hv : v ≠ 0) (gain : ℂ)
    (h : jacobian (conjugatedTuple q) *ᵥ conjugatedDirection v =
      gain • observation (conjugatedTuple q)) (k : Fin 10) :
    ((jacobian (conjugatedTuple q)).submatrix k.succAbove k.succAbove).det = 0 := by
  let a := conjugatedTuple q
  let R := weightedDirection rightWeights a
  let T := weightedDirection weights a
  have hR₀ : R 0 = 0 := by simp [R, weightedDirection, rightWeights]
  have hR₅ : R 5 = 1 := by simp [R, weightedDirection, rightWeights, weights, a, conjugatedTuple]
  have hT₀ : T 0 = 1 := by simp [T, weightedDirection, weights, a, conjugatedTuple]
  have hR : jacobian a *ᵥ R = (6 : ℂ) • observation a := by
    simpa [R] using euler a rightWeights 6 observation_right_weight
  have hT : jacobian a *ᵥ T = (12 : ℂ) • observation a := by
    simpa [T] using euler a weights 12 observation_weight
  let p := T - (2 : ℂ) • R
  let b := conjugatedDirection v - (gain / 6) • R
  have hp₀ : p 0 = 1 := by simp [p, hT₀, hR₀]
  have hb₀ : b 0 = 0 := by
    change 0 - (gain / 6) * R 0 = 0
    simp [hR₀]
  have hpJ : jacobian a *ᵥ p = 0 := by
    dsimp only [p]
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hT, hR, smul_smul,
      show (2 : ℂ) * 6 = 12 by norm_num, sub_self]
  have hbJ : jacobian a *ᵥ b = 0 := by
    change jacobian a *ᵥ conjugatedDirection v = gain • observation a at h
    dsimp only [b]
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, h, hR, smul_smul,
      div_mul_cancel₀ _ (by norm_num), sub_self]
  have hb : b ≠ 0 := by
    intro he
    have hg : gain / 6 = 0 := by
      have hc := congrFun he (5 : Fin 10)
      change 0 - (gain / 6) * R 5 = 0 at hc
      simpa only [hR₅, mul_one, zero_sub, neg_eq_zero] using hc
    exact conjugatedDirection_ne_zero v hv (by simpa [b, hg] using he)
  exact minors_of_two_kernel_directions (jacobian a) hb hb₀ hp₀ hbJ hpJ k

/-- A nonzero real kernel direction forces every principal cofactor of the
complexified Jacobian to vanish, including the selected minors at zero and one. -/
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
  have hm : chartMass q ≠ 0 := (gram_mass_pos _ hq).ne'
  have hevent : ∀ᶠ r in 𝓝 (0 : ℝ), chartMass (path r) ≠ 0 :=
    hmass.continuousAt.eventually_ne (by rwa [Function.comp_apply, ← hzero])
  have hradial : jacobian a *ᵥ u = (↑(s' / chartMass q) : ℂ) • observation a := by
    funext i
    let e : Matrix (Fin 4) (Fin 4) ℂ →L[ℝ] ℂ :=
      (ContinuousLinearMap.proj (observedRows i).2 : (Fin 4 → ℂ) →L[ℝ] ℂ).comp
        (ContinuousLinearMap.proj (observedRows i).1 :
          (Fin 4 → Fin 4 → ℂ) →L[ℝ] (Fin 4 → ℂ))
    have hn : HasDerivAt (fun r => e (normalizedObservation (path r))) 0 0 := by
      have hd : HasDerivAt (fun r : ℝ => e (normalizedObservation (path r))) (e 0) 0 :=
        e.hasFDerivAt.comp_hasDerivAt 0 hnorm
      simpa only [map_zero] using hd
    have hproduct := hmass.smul hn
    have hvalue : HasDerivAt (fun r : ℝ => observation (a + r • u) i)
        (s' • e (normalizedObservation q)) 0 := by
      simp only [Function.comp_apply, ← hzero, smul_zero, zero_add] at hproduct
      refine hproduct.congr_of_eventuallyEq ?_
      filter_upwards [hevent] with r hr
      rw [show a + r • u = conjugatedTuple (path r) from (conjugatedTuple_line q v r).symm,
        observation_conjugatedTuple]
      change gram (chartAmplitude (path r)) (observedRows i).1 (observedRows i).2 =
        chartMass (path r) • ((chartMass (path r))⁻¹ •
          gram (chartAmplitude (path r)) (observedRows i).1 (observedRows i).2)
      rw [smul_smul, mul_inv_cancel₀ hr, one_smul]
    rw [(observation_derivative a u i).unique hvalue]
    change s' • ((chartMass q)⁻¹ • gram (chartAmplitude q) (observedRows i).1 (observedRows i).2) =
      (↑(s' / chartMass q) : ℂ) * observation a i
    rw [smul_smul, ← div_eq_mul_inv, observation_conjugatedTuple]
    rfl
  have hJ := chartJacobian_minor_of_radial q v hv _ hradial k
  change evalAt a (symbolicMinor k) = 0
  rw [symbolicMinor, RingHom.map_det]
  have he : (evalAt a).mapMatrix (Matrix.of fun i j : Fin 9 =>
      pderiv (k.succAbove j) (observation (R := P) X (k.succAbove i))) =
      (jacobian a).submatrix k.succAbove k.succAbove := by
    ext i j
    exact evalAt_pderiv a _ _
  rwa [he]

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSSixSiteCriticalRank
