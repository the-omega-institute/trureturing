/- GID: D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSIntrinsicQ2Fiber
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/OpenBoundaryMPSIntrinsicQ2Fiber
   mirror-E: none(waiver:static-actual-image-fibers)
   anchors: []
   utility: none
   digest: Intrinsic actual-image raw prefix Q2 fibers through quotient retraction. -/

import D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSQ2PolynomialFiber

/-! Actual-image quotient validity, retraction and neighborhood transport.
The canonical core and phase rigidity reuse Haobo Ma and Wenlin Zhang's
CC BY 4.0 Conjecture 8 supplier through OpenBoundaryMPSTwoSiteMinimality.
The local C1 supplier credits BochaoKong's Apache-2.0 LeanPool argument,
commit 2b1ec889365345f19a45fa94b6457a4d92c96295.
All observations retain raw scale and use the displayed prefix windows. -/

noncomputable section
open Set Matrix MvPolynomial
open scoped BigOperators Matrix Topology

namespace D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSIntrinsicQ2Fiber

open OpenBoundaryMPSTwoSiteMinimality
open OpenBoundaryMPSDensityRecovery
open OpenBoundaryMPSDensityGenericity
  (realCoeff imagCoeff coefficient_eval polynomial_nonzero_dense)
open PeriodicMPSParentIntersection (Bond Word wordMatrix)
open OpenBoundaryMPSQuotient hiding coreCoordinates
open OpenBoundaryMPSMarginalBirationality
open OpenBoundaryMPSQ2PolynomialFiber

def quotientRawPrefix (m : ℕ) (x : Coordinates) : Matrix (Word 3) (Word 3) ℂ :=
  OpenBoundaryMPSDensityRecovery.rawPrefix 3 m
    (OpenBoundaryMPSTwoSiteMinimality.state (3 + m) (positiveRepresentative x))

private def parameterCoordinatesParameter
    (θ : OpenBoundaryMPSTwoSiteMinimality.Parameter) :
    OpenBoundaryMPSMarginalBirationality.parameterIndex → ℂ :=
  Sum.elim
    (fun t => OpenBoundaryMPSTwoSiteMinimality.core θ t.1 t.2.1 t.2.2)
    (Sum.elim
      (fun i => OpenBoundaryMPSTwoSiteMinimality.left θ i)
      (fun i => OpenBoundaryMPSTwoSiteMinimality.right θ i))

private def parameterCoordinates (x : Coordinates) :
    OpenBoundaryMPSMarginalBirationality.parameterIndex → ℂ :=
  parameterCoordinatesParameter (positiveRepresentative x)

private lemma parameterCoordinates_eval (m : ℕ) (x : Coordinates) :
    (fun w => eval (parameterCoordinates x)
      (OpenBoundaryMPSMarginalBirationality.parameterPolys (3 + m) w)) =
      OpenBoundaryMPSTwoSiteMinimality.state (3 + m) (positiveRepresentative x) := by
  have h := OpenBoundaryMPSMarginalBirationality.parameter_eval (3 + m)
    (parameterCoordinates x)
  change (fun w => eval (parameterCoordinates x)
      (OpenBoundaryMPSMarginalBirationality.parameterPolys (3 + m) w)) =
    OpenBoundaryMPSMarginalBirationality.mpsState (3 + m)
      (OpenBoundaryMPSTwoSiteMinimality.core (positiveRepresentative x) 0)
      (OpenBoundaryMPSTwoSiteMinimality.core (positiveRepresentative x) 1)
      (OpenBoundaryMPSTwoSiteMinimality.left (positiveRepresentative x))
      (OpenBoundaryMPSTwoSiteMinimality.right (positiveRepresentative x))
  convert h using 1 <;>
    ext <;> rfl

private lemma parameterCoordinatesParameter_continuous :
    Continuous (parameterCoordinatesParameter :
      OpenBoundaryMPSTwoSiteMinimality.Parameter →
        OpenBoundaryMPSMarginalBirationality.parameterIndex → ℂ) := by
  apply continuous_pi
  intro i
  cases i with
  | inl t =>
      rcases t with ⟨s, ⟨j, k⟩⟩
      fin_cases s <;> fin_cases j <;> fin_cases k <;>
        simp [parameterCoordinatesParameter, OpenBoundaryMPSTwoSiteMinimality.core]
        <;> fun_prop
  | inr i =>
      cases i with
      | inl j =>
          fin_cases j <;>
            simp [parameterCoordinatesParameter, OpenBoundaryMPSTwoSiteMinimality.left]
            <;> fun_prop
      | inr j =>
          fin_cases j
          · exact Complex.continuous_ofReal.comp
              (continuous_fst.comp
                (continuous_snd : Continuous
                  (fun θ : OpenBoundaryMPSTwoSiteMinimality.Parameter => θ.2)))
          · exact continuous_snd.comp
              (continuous_snd : Continuous
                (fun θ : OpenBoundaryMPSTwoSiteMinimality.Parameter => θ.2))

private lemma parameterCoordinates_continuous :
    Continuous (parameterCoordinates : Coordinates →
      OpenBoundaryMPSMarginalBirationality.parameterIndex → ℂ) := by
  change Continuous (parameterCoordinatesParameter ∘ positiveRepresentative)
  exact parameterCoordinatesParameter_continuous.comp representative_continuous

private lemma quotientRawPrefix_continuous (m : ℕ) :
    Continuous (quotientRawPrefix m) := by
  have hc : Continuous (fun x : Coordinates =>
      OpenBoundaryMPSTwoSiteMinimality.state (3 + m) (positiveRepresentative x)) :=
    by
      have hpar : Continuous (fun x : Coordinates =>
          fun w => eval (parameterCoordinates x)
            (OpenBoundaryMPSMarginalBirationality.parameterPolys (3 + m) w)) := by
        apply continuous_pi
        intro w
        exact (MvPolynomial.continuous_eval _).comp parameterCoordinates_continuous
      exact hpar.congr (fun x => parameterCoordinates_eval m x)
  apply continuous_matrix
  intro u v
  unfold quotientRawPrefix OpenBoundaryMPSDensityRecovery.rawPrefix
  simp only [Matrix.mul_apply, OpenBoundaryMPSDensityRecovery.amplitudeColumns,
    Matrix.conjTranspose_apply]
  apply continuous_finset_sum Finset.univ
  intro b hb
  exact ((continuous_apply (Fin.append u b)).comp hc).mul
    (Continuous.star ((continuous_apply (Fin.append v b)).comp hc))

lemma positiveRepresentative_witness (m : ℕ) :
    positiveRepresentative (coordinatesOf (witnessParameter m)) = witnessParameter m := by
  apply representative_coordinatesOf
  dsimp [witnessParameter]
  positivity

def quotientValidityDomain (m : ℕ) : Set Coordinates :=
  {x | 0 < sigma x ∧
    eval (OpenBoundaryMPSDensityGenericity.realCoordinates
      (fun ij => quotientRawPrefix m x ij.1 ij.2))
      (OpenBoundaryMPSQuotient.quotientLocusPolynomial m) ≠ 0 ∧
    eval x (leadingPolynomial m) ≠ 0}

lemma quotientValidityDomain_open (m : ℕ) :
    IsOpen (quotientValidityDomain m) := by
  unfold quotientValidityDomain
  have hcoords : Continuous (fun x : Coordinates =>
      OpenBoundaryMPSDensityGenericity.realCoordinates
        (fun ij : ObsIndex => quotientRawPrefix m x ij.1 ij.2)) := by
    have hraw : Continuous (fun x : Coordinates =>
        (fun ij : ObsIndex => quotientRawPrefix m x ij.1 ij.2)) := by
      apply continuous_pi
      intro ij
      exact (continuous_apply ij.2).comp
        ((continuous_apply ij.1).comp (quotientRawPrefix_continuous m))
    apply continuous_pi
    intro i
    cases i with
    | inl ij => exact Complex.continuous_re.comp ((continuous_apply ij).comp hraw)
    | inr ij => exact Complex.continuous_im.comp ((continuous_apply ij).comp hraw)
  apply (isOpen_lt continuous_const (continuous_apply 10)).inter
  apply IsOpen.inter
  · exact isOpen_ne.preimage ((MvPolynomial.continuous_eval _).comp
      hcoords)
  · exact isOpen_ne.preimage (MvPolynomial.continuous_eval _)

set_option maxHeartbeats 800000 in
lemma quotientValidityDomain_nonempty (m : ℕ) :
    (quotientValidityDomain m).Nonempty := by
  let x₀ := coordinatesOf (witnessParameter m)
  have hrep : positiveRepresentative x₀ = witnessParameter m := by
    exact positiveRepresentative_witness m
  have hwit := OpenBoundaryMPSQuotient.quotient_locus_witness m
  dsimp only at hwit
  rcases hwit with ⟨hψ, hQ, hg, h00⟩
  have hw := OpenBoundaryMPSTwoSiteMinimality.witness_gauge m
  have hρ : eval (OpenBoundaryMPSDensityGenericity.realCoordinates
      (fun ij => quotientRawPrefix m x₀ ij.1 ij.2))
      (OpenBoundaryMPSQuotient.quotientLocusPolynomial m) ≠ 0 := by
    simpa [quotientRawPrefix, hrep, hw] using hQ
  have hσ : 0 < sigma x₀ := by
    dsimp [x₀, sigma, coordinatesOf]
    dsimp [witnessParameter]
    norm_num
  obtain ⟨θ, hθpos, hθchart, hθcore, hθlead⟩ :=
    OpenBoundaryMPSTwoSiteMinimality.canonicalChart_nonempty m
  have hθrep : positiveRepresentative (coordinatesOf θ) = θ :=
    representative_coordinatesOf θ hθpos
  have hLθ : eval (coordinatesOf θ) (leadingPolynomial m) ≠ 0 := by
    rw [leadingPolynomial_eval m (coordinatesOf θ) (by
      dsimp [sigma, coordinatesOf]
      positivity)]
    rw [hθrep]
    exact fun hz => hθlead ((Complex.normSq_eq_zero.mp hz))
  have hLdense := polynomial_nonzero_dense (leadingPolynomial m)
    (coordinatesOf θ) hLθ
  let R : Set Coordinates := {x | 0 < sigma x ∧
    eval (OpenBoundaryMPSDensityGenericity.realCoordinates
      (fun ij => quotientRawPrefix m x ij.1 ij.2))
      (OpenBoundaryMPSQuotient.quotientLocusPolynomial m) ≠ 0}
  have hRopen : IsOpen R := by
    unfold R
    have hcoords : Continuous (fun x : Coordinates =>
        OpenBoundaryMPSDensityGenericity.realCoordinates
          (fun ij : ObsIndex => quotientRawPrefix m x ij.1 ij.2)) := by
      have hraw : Continuous (fun x : Coordinates =>
          (fun ij : ObsIndex => quotientRawPrefix m x ij.1 ij.2)) := by
        apply continuous_pi
        intro ij
        exact (continuous_apply ij.2).comp
          ((continuous_apply ij.1).comp (quotientRawPrefix_continuous m))
      apply continuous_pi
      intro i
      cases i with
      | inl ij => exact Complex.continuous_re.comp ((continuous_apply ij).comp hraw)
      | inr ij => exact Complex.continuous_im.comp ((continuous_apply ij).comp hraw)
    apply (isOpen_lt continuous_const (continuous_apply 10)).inter
    exact isOpen_ne.preimage ((MvPolynomial.continuous_eval _).comp hcoords)
  have hRne : R.Nonempty := ⟨x₀, hσ, hρ⟩
  obtain ⟨x, hxR, hxL⟩ := hLdense.inter_open_nonempty R hRopen hRne
  exact ⟨x, hxR.1, hxR.2, hxL⟩

lemma rawPrefix_scale_local (k m : ℕ) (z : ℂ)
    (ψ : Word (k + m) → ℂ) :
    OpenBoundaryMPSDensityRecovery.rawPrefix k m (z • ψ) =
      (Complex.normSq z : ℂ) • OpenBoundaryMPSDensityRecovery.rawPrefix k m ψ := by
  unfold OpenBoundaryMPSDensityRecovery.rawPrefix
  have hC : OpenBoundaryMPSDensityRecovery.amplitudeColumns k m (z • ψ) =
      z • OpenBoundaryMPSDensityRecovery.amplitudeColumns k m ψ := rfl
  rw [hC, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul]
  change (z * (starRingEnd ℂ) z) • _ = _
  rw [Complex.mul_conj]

private lemma positiveBoundary_state_eq (m : ℕ)
    (p : OpenBoundaryMPSQuotient.Quotient) :
    OpenBoundaryMPSTwoSiteMinimality.state (3 + m)
        (p.1, Real.sqrt p.2.1, (Real.sqrt p.2.1 : ℂ) * p.2.2) =
      OpenBoundaryMPSMarginalBirationality.mpsState (3 + m)
        (OpenBoundaryMPSTwoSiteMinimality.core p 0)
        (OpenBoundaryMPSTwoSiteMinimality.core p 1)
        (OpenBoundaryMPSTwoSiteMinimality.left p)
        (OpenBoundaryMPSQuotient.positiveBoundary p) := by
  funext w
  rfl

set_option maxHeartbeats 800000 in
private lemma quotientIndexEquiv_symm_zero : quotientIndexEquiv.symm 0 = Sum.inl 0 := by decide

set_option maxHeartbeats 800000 in
private lemma quotientIndexEquiv_symm_one : quotientIndexEquiv.symm 1 = Sum.inl 1 := by decide

set_option maxHeartbeats 800000 in
private lemma quotientIndexEquiv_symm_two : quotientIndexEquiv.symm 2 = Sum.inl 2 := by decide

set_option maxHeartbeats 800000 in
private lemma quotientIndexEquiv_symm_three : quotientIndexEquiv.symm 3 = Sum.inl 3 := by decide

set_option maxHeartbeats 800000 in
private lemma quotientIndexEquiv_symm_four : quotientIndexEquiv.symm 4 = Sum.inl 4 := by decide

set_option maxHeartbeats 800000 in
private lemma quotientIndexEquiv_symm_five : quotientIndexEquiv.symm 5 = Sum.inr (Sum.inl 0) := by decide

set_option maxHeartbeats 800000 in
private lemma quotientIndexEquiv_symm_six : quotientIndexEquiv.symm 6 = Sum.inr (Sum.inl 1) := by decide

set_option maxHeartbeats 800000 in
private lemma quotientIndexEquiv_symm_seven : quotientIndexEquiv.symm 7 = Sum.inr (Sum.inl 2) := by decide

set_option maxHeartbeats 800000 in
private lemma quotientIndexEquiv_symm_eight : quotientIndexEquiv.symm 8 = Sum.inr (Sum.inl 3) := by decide

set_option maxHeartbeats 800000 in
private lemma quotientIndexEquiv_symm_nine : quotientIndexEquiv.symm 9 = Sum.inr (Sum.inl 4) := by decide

set_option maxHeartbeats 800000 in
private lemma quotientIndexEquiv_symm_ten : quotientIndexEquiv.symm 10 = Sum.inr (Sum.inr 0) := by decide

set_option maxHeartbeats 800000 in
private lemma quotientIndexEquiv_symm_eleven : quotientIndexEquiv.symm 11 = Sum.inr (Sum.inr 1) := by decide

set_option maxHeartbeats 800000 in
private lemma quotientIndexEquiv_symm_twelve : quotientIndexEquiv.symm 12 = Sum.inr (Sum.inr 2) := by decide

set_option maxHeartbeats 800000 in
lemma quotientCoordinates_positiveRepresentative (p : OpenBoundaryMPSQuotient.Quotient)
    (hp : 0 < p.2.1) :
    positiveRepresentative (quotientCoordinates13 p) =
      (p.1, Real.sqrt p.2.1, (Real.sqrt p.2.1 : ℂ) * p.2.2) := by
  apply Prod.ext
  · funext i
    fin_cases i <;>
      simp [positiveRepresentative, coreCoordinates, quotientCoordinates13,
        OpenBoundaryMPSQuotient.quotientRealCoordinates,
        sigma, eta, quotientRealCoordinates,
        quotientIndexEquiv_symm_zero, quotientIndexEquiv_symm_one,
        quotientIndexEquiv_symm_two, quotientIndexEquiv_symm_three,
        quotientIndexEquiv_symm_four, quotientIndexEquiv_symm_five,
        quotientIndexEquiv_symm_six, quotientIndexEquiv_symm_seven,
        quotientIndexEquiv_symm_eight, quotientIndexEquiv_symm_nine,
        quotientIndexEquiv_symm_ten, quotientIndexEquiv_symm_eleven,
        quotientIndexEquiv_symm_twelve]
  · apply Prod.ext
    · simp [positiveRepresentative, quotientCoordinates13,
        OpenBoundaryMPSQuotient.quotientRealCoordinates, sigma, eta,
        quotientRealCoordinates, quotientIndexEquiv_symm_ten,
        quotientIndexEquiv_symm_eleven, quotientIndexEquiv_symm_twelve]
    · apply Complex.ext <;>
        simp [positiveRepresentative, quotientCoordinates13,
          OpenBoundaryMPSQuotient.quotientRealCoordinates, sigma, eta,
          quotientRealCoordinates, quotientIndexEquiv_symm_ten,
          quotientIndexEquiv_symm_eleven, quotientIndexEquiv_symm_twelve]

private def quotientParameterOfCoordinates (x : Coordinates) :
    OpenBoundaryMPSQuotient.Quotient := (coreCoordinates x, sigma x, eta x)

private lemma quotientParameter_coordinates (x : Coordinates) :
    quotientCoordinates13 (quotientParameterOfCoordinates x) = x := by
  funext i
  fin_cases i <;>
    simp [quotientParameterOfCoordinates, quotientCoordinates13,
      quotientIndexEquiv_symm_zero, quotientIndexEquiv_symm_one,
      quotientIndexEquiv_symm_two, quotientIndexEquiv_symm_three,
      quotientIndexEquiv_symm_four, quotientIndexEquiv_symm_five,
      quotientIndexEquiv_symm_six, quotientIndexEquiv_symm_seven,
      quotientIndexEquiv_symm_eight, quotientIndexEquiv_symm_nine,
      quotientIndexEquiv_symm_ten, quotientIndexEquiv_symm_eleven,
      quotientIndexEquiv_symm_twelve, OpenBoundaryMPSQuotient.quotientRealCoordinates,
      quotientRealCoordinates, coreCoordinates, sigma, eta]

private lemma quotientParameter_positiveBoundary (x : Coordinates) :
    positiveRepresentative x =
      ((quotientParameterOfCoordinates x).1,
        Real.sqrt (quotientParameterOfCoordinates x).2.1,
        (Real.sqrt (quotientParameterOfCoordinates x).2.1 : ℂ) *
          (quotientParameterOfCoordinates x).2.2) := by
  rfl

private lemma positiveObservation_local (m : ℕ) (x : Coordinates) (hx : 0 ≤ sigma x) :
    quotientRawPrefix m x =
      OpenBoundaryMPSQuotient.quotientObservation 3 m
        (quotientParameterOfCoordinates x) := by
  let p := quotientParameterOfCoordinates x
  have hs0 : OpenBoundaryMPSTwoSiteMinimality.state (3 + m)
      (positiveRepresentative x) =
      OpenBoundaryMPSMarginalBirationality.mpsState (3 + m)
        (OpenBoundaryMPSTwoSiteMinimality.core p 0)
        (OpenBoundaryMPSTwoSiteMinimality.core p 1)
        (OpenBoundaryMPSTwoSiteMinimality.left p)
        (OpenBoundaryMPSQuotient.positiveBoundary p) := by
    rw [quotientParameter_positiveBoundary x]
    exact positiveBoundary_state_eq m p
  have hs1 : OpenBoundaryMPSMarginalBirationality.mpsState (3 + m)
      (OpenBoundaryMPSTwoSiteMinimality.core p 0)
      (OpenBoundaryMPSTwoSiteMinimality.core p 1)
      (OpenBoundaryMPSTwoSiteMinimality.left p)
      (OpenBoundaryMPSQuotient.positiveBoundary p) =
      (Real.sqrt (sigma x) : ℂ) •
        OpenBoundaryMPSMarginalBirationality.mpsState (3 + m)
          (OpenBoundaryMPSTwoSiteMinimality.core p 0)
          (OpenBoundaryMPSTwoSiteMinimality.core p 1)
          (OpenBoundaryMPSTwoSiteMinimality.left p)
          (OpenBoundaryMPSTwoSiteMinimality.right
            (p.1, 1, p.2.2)) := by
    have hr : OpenBoundaryMPSQuotient.positiveBoundary p =
        (Real.sqrt p.2.1 : ℂ) •
          OpenBoundaryMPSTwoSiteMinimality.right (p.1, 1, p.2.2) := by
      ext i
      fin_cases i <;>
        simp [OpenBoundaryMPSQuotient.positiveBoundary,
          OpenBoundaryMPSTwoSiteMinimality.right]
    rw [hr]
    funext w
    simp only [OpenBoundaryMPSMarginalBirationality.mpsState,
      OpenBoundaryMPSDensityRecovery.state_formula, Matrix.mulVec_smul,
      dotProduct_smul, Pi.smul_apply, smul_eq_mul]
    rfl
  have hs := hs0.trans hs1
  rw [show quotientRawPrefix m x =
      OpenBoundaryMPSDensityRecovery.rawPrefix 3 m
        (OpenBoundaryMPSTwoSiteMinimality.state (3 + m)
          (positiveRepresentative x)) by rfl]
  rw [hs, rawPrefix_scale_local]
  have hz : Complex.normSq (Real.sqrt (sigma x) : ℂ) = (sigma x : ℂ) := by
    rw [Complex.normSq_ofReal]
    congr 1
    rw [← sq, Real.sq_sqrt hx]
  rw [hz]
  rfl

lemma quotientCoordinates_retraction_local (m : ℕ) (x : Coordinates)
    (hx : 0 < sigma x)
    (hρ : eval (OpenBoundaryMPSDensityGenericity.realCoordinates
      (fun ij => quotientRawPrefix m x ij.1 ij.2))
      (OpenBoundaryMPSQuotient.quotientLocusPolynomial m) ≠ 0) :
    quotientCoordinates13
        (OpenBoundaryMPSQuotient.quotientCoordinates m (quotientRawPrefix m x)) = x := by
  let p := quotientParameterOfCoordinates x
  have hparts := (OpenBoundaryMPSQuotient.quotientLocus_eval m
    (quotientRawPrefix m x)).mp hρ
  have hobs := positiveObservation_local m x hx.le
  rw [hobs] at hparts
  have hp := OpenBoundaryMPSQuotient.quotient_retraction m p hx hparts.1
  rw [← hobs] at hp
  rw [hp, quotientParameter_coordinates]

def quotientNumeratorFamily (m : ℕ) (j : Fin 13) :
    MvPolynomial (ObsIndex ⊕ ObsIndex) ℝ :=
  OpenBoundaryMPSQuotient.quotientRealNumerator m (quotientIndexEquiv.symm j)

def quotientDenominatorFamily (m : ℕ) (j : Fin 13) :
    MvPolynomial (ObsIndex ⊕ ObsIndex) ℝ :=
  OpenBoundaryMPSQuotient.quotientRealDenominator m (quotientIndexEquiv.symm j)

private lemma quotient_ratio_vector_local (m : ℕ) (x : Coordinates)
    (hσ : 0 < sigma x)
    (hρ : eval (OpenBoundaryMPSDensityGenericity.realCoordinates
      (fun ij => quotientRawPrefix m x ij.1 ij.2))
      (OpenBoundaryMPSQuotient.quotientLocusPolynomial m) ≠ 0) :
    (fun j =>
      eval (OpenBoundaryMPSDensityGenericity.realCoordinates
        (fun ij => quotientRawPrefix m x ij.1 ij.2)) (quotientNumeratorFamily m j) /
      eval (OpenBoundaryMPSDensityGenericity.realCoordinates
        (fun ij => quotientRawPrefix m x ij.1 ij.2)) (quotientDenominatorFamily m j)) = x := by
  funext j
  have hr := quotientCoordinate_ratio m (quotientRawPrefix m x) (by simpa using hρ) j
  rw [quotientCoordinates_retraction_local m x hσ hρ] at hr
  exact hr

private lemma state_continuous (m : ℕ) :
    Continuous (fun x : Coordinates =>
      OpenBoundaryMPSTwoSiteMinimality.state (3 + m) (positiveRepresentative x)) := by
  have hpar : Continuous (fun x : Coordinates =>
      fun w => eval (parameterCoordinates x)
        (OpenBoundaryMPSMarginalBirationality.parameterPolys (3 + m) w)) := by
    apply continuous_pi
    intro w
    exact (MvPolynomial.continuous_eval _).comp parameterCoordinates_continuous
  exact hpar.congr (fun x => parameterCoordinates_eval m x)

private lemma openBoundaryMPS_smul {n : ℕ} {ψ : Word n → ℂ}
    (hψ : ψ ∈ OpenBoundaryMPSMarginalBirationality.openBoundaryMPS n) (z : ℂ) :
    z • ψ ∈ OpenBoundaryMPSMarginalBirationality.openBoundaryMPS n := by
  rcases hψ with ⟨a₀, a₁, l, r, hr⟩
  refine ⟨a₀, a₁, l, z • r, ?_⟩
  rw [hr]
  funext w
  simp only [OpenBoundaryMPSMarginalBirationality.mpsState,
    Matrix.mulVec_smul, dotProduct_smul, Pi.smul_apply, smul_eq_mul]

private def q2WordCast (m : ℕ) (w : Word (2 + (1 + m))) : Word (3 + m) :=
  fun i => w (Fin.cast (by omega) i)

private def actualQ2RawPrefix (m : ℕ)
    (ψ : Word (3 + m) → ℂ) : Matrix (Word 2) (Word 2) ℂ :=
  OpenBoundaryMPSDensityRecovery.rawPrefix 2 (1 + m)
    (fun w => ψ (q2WordCast m w))

def intrinsicActualQ2Fiber (m : ℕ) : Prop :=
  ∃ G : MvPolynomial (ObsIndex ⊕ ObsIndex) ℝ, G ≠ 0 ∧
    let L := actualPrincipalLocus m G
    L.Nonempty ∧ IsOpen L ∧ Dense L ∧
      ∀ ψ ∈ L, ∀ V : Set (OpenBoundaryMPSMarginalBirationality.openBoundaryMPS (3 + m)),
        V ∈ 𝓝 ψ →
        ∃ φ ∈ V,
          actualQ2RawPrefix m (φ : Word (3 + m) → ℂ) =
            actualQ2RawPrefix m (ψ : Word (3 + m) → ℂ) ∧
          ¬ ∃ ζ : ℂ, ‖ζ‖ = 1 ∧
            (φ : Word (3 + m) → ℂ) = ζ • (ψ : Word (3 + m) → ℂ)

set_option maxHeartbeats 1000000 in
theorem intrinsic_actual_q2_fiber (m : ℕ) : intrinsicActualQ2Fiber m := by
  obtain ⟨J, hJ, hJw, hJfiber⟩ :=
    D5.S3.Geometry.PolynomialLocalFiber.exists_rank_fiber_polynomial
      (recordPolynomial (1 + m))
  let P : RealPoly := J * leadingPolynomial m
  obtain ⟨H, B, hclear⟩ :=
    clear_polynomial P (quotientNumeratorFamily m) (quotientDenominatorFamily m)
  obtain ⟨x₀, hx₀⟩ := hJw
  have hJdense := polynomial_nonzero_dense J x₀ (by rw [hx₀]; norm_num)
  obtain ⟨x, hxDom, hxJ⟩ := hJdense.inter_open_nonempty _
    (quotientValidityDomain_open m) (quotientValidityDomain_nonempty m)
  change eval x J ≠ 0 at hxJ
  let Qx := quotientRawPrefix m x
  let ax : ObsIndex ⊕ ObsIndex → ℝ :=
    OpenBoundaryMPSDensityGenericity.realCoordinates
      (fun ij : ObsIndex => Qx ij.1 ij.2)
  have hρx : eval ax (OpenBoundaryMPSQuotient.quotientLocusPolynomial m) ≠ 0 := by
    exact hxDom.2.1
  have hdenx : ∀ j, eval ax (quotientDenominatorFamily m j) ≠ 0 := by
    intro j
    exact quotient_denominators_nonzero m Qx hρx j
  have hratx : (fun j => eval ax (quotientNumeratorFamily m j) /
      eval ax (quotientDenominatorFamily m j)) = x := by
    exact quotient_ratio_vector_local m x hxDom.1 hρx
  have hcx := hclear ax hdenx
  rw [hratx] at hcx
  have hPx : eval x P ≠ 0 := by
    simpa [P] using mul_ne_zero hxJ hxDom.2.2
  have hHx : eval ax H ≠ 0 := by
    intro h
    have : eval x P = 0 := by simpa [h] using hcx.2
    exact hPx this
  let G : MvPolynomial (ObsIndex ⊕ ObsIndex) ℝ :=
    OpenBoundaryMPSQuotient.quotientLocusPolynomial m * H
  have hGx : eval ax G ≠ 0 := by
    simpa [G] using mul_ne_zero hρx hHx
  have hG : G ≠ 0 := by
    intro h
    rw [h] at hGx
    simpa using hGx
  let ψ₀ : Word (3 + m) → ℂ :=
    OpenBoundaryMPSTwoSiteMinimality.state (3 + m) (positiveRepresentative x)
  have hψ₀ : ψ₀ ∈ OpenBoundaryMPSMarginalBirationality.openBoundaryMPS (3 + m) := by
    refine ⟨OpenBoundaryMPSTwoSiteMinimality.core (positiveRepresentative x) 0,
      OpenBoundaryMPSTwoSiteMinimality.core (positiveRepresentative x) 1,
      OpenBoundaryMPSTwoSiteMinimality.left (positiveRepresentative x),
      OpenBoundaryMPSTwoSiteMinimality.right (positiveRepresentative x), ?_⟩
    rfl
  let ψ : OpenBoundaryMPSMarginalBirationality.openBoundaryMPS (3 + m) := ⟨ψ₀, hψ₀⟩
  have hψG : eval (OpenBoundaryMPSDensityGenericity.realCoordinates
      (fun ij => OpenBoundaryMPSDensityRecovery.rawPrefix 3 m
        (ψ : Word (3 + m) → ℂ) ij.1 ij.2)) G ≠ 0 := by
    simpa [ψ, ψ₀, Qx, ax, quotientRawPrefix, actualPrincipalLocus] using hGx
  obtain ⟨Lne, Lopen, Ldense⟩ :=
    actual_principal_genericity m G ⟨ψ, hψG⟩
  refine ⟨G, hG, Lne, Lopen, Ldense, ?_⟩
  intro ψ' hψ' V hV
  obtain ⟨O, hOV, hO, hψ'O⟩ := mem_nhds_iff.mp hV
  let Qψ := OpenBoundaryMPSDensityRecovery.rawPrefix 3 m
    (ψ' : Word (3 + m) → ℂ)
  have hGψ := hψ'
  change eval (OpenBoundaryMPSDensityGenericity.realCoordinates
      (fun ij => Qψ ij.1 ij.2)) G ≠ 0 at hGψ
  have hρψ : eval (OpenBoundaryMPSDensityGenericity.realCoordinates
      (fun ij => Qψ ij.1 ij.2))
      (OpenBoundaryMPSQuotient.quotientLocusPolynomial m) ≠ 0 := by
    have hmul : eval (OpenBoundaryMPSDensityGenericity.realCoordinates
        (fun ij => Qψ ij.1 ij.2))
        (OpenBoundaryMPSQuotient.quotientLocusPolynomial m * H) ≠ 0 := by
      simpa [G] using hGψ
    simp only [map_mul] at hmul
    exact (mul_ne_zero_iff.mp hmul).1
  have hpartsψ := (OpenBoundaryMPSQuotient.quotientLocus_eval m Qψ).mp hρψ
  obtain ⟨_, _, _, _, _, h00ψ⟩ :=
    OpenBoundaryMPSQuotient.rational_quotient_inverse m Qψ hρψ
  have hrep := OpenBoundaryMPSQuotient.actual_quotient_representative m
      (ψ' : Word (3 + m) → ℂ) ψ'.property hpartsψ.1 h00ψ
  dsimp only at hrep
  let p := OpenBoundaryMPSQuotient.quotientCoordinates m Qψ
  have hrep' : 0 < p.2.1 ∧ ∃ z : ℂ, ‖z‖ = 1 ∧
      (ψ' : Word (3 + m) → ℂ) = z •
        OpenBoundaryMPSMarginalBirationality.mpsState (3 + m)
          (OpenBoundaryMPSTwoSiteMinimality.core p 0)
          (OpenBoundaryMPSTwoSiteMinimality.core p 1)
          (OpenBoundaryMPSTwoSiteMinimality.left p)
          (OpenBoundaryMPSQuotient.positiveBoundary p) := by
    simpa [p] using hrep
  obtain ⟨hpσ, z, hz, hphase⟩ := hrep'
  let x' := quotientCoordinates13 p
  have hx'σ : 0 < sigma x' := by
    simpa [x', sigma, quotientCoordinates13, quotientRealCoordinates,
      quotientIndexEquiv_symm_ten] using hpσ
  have hx'Q : Qψ = quotientRawPrefix m x' := by
    have hrep := quotientCoordinates_positiveRepresentative p hpσ
    have hstate : OpenBoundaryMPSTwoSiteMinimality.state (3 + m)
        (positiveRepresentative x') =
        OpenBoundaryMPSMarginalBirationality.mpsState (3 + m)
          (OpenBoundaryMPSTwoSiteMinimality.core p 0)
          (OpenBoundaryMPSTwoSiteMinimality.core p 1)
          (OpenBoundaryMPSTwoSiteMinimality.left p)
          (OpenBoundaryMPSQuotient.positiveBoundary p) := by
      rw [hrep]
      exact positiveBoundary_state_eq m p
    have hzsq : Complex.normSq z = 1 := by
      rw [← Complex.sq_norm, hz]
      norm_num
    change OpenBoundaryMPSDensityRecovery.rawPrefix 3 m
        (ψ' : Word (3 + m) → ℂ) =
      OpenBoundaryMPSDensityRecovery.rawPrefix 3 m
        (OpenBoundaryMPSTwoSiteMinimality.state (3 + m)
          (positiveRepresentative x'))
    rw [hphase, rawPrefix_scale_local, hzsq, hstate]
    simp
  have hρx' : eval (OpenBoundaryMPSDensityGenericity.realCoordinates
      (fun ij => quotientRawPrefix m x' ij.1 ij.2))
      (OpenBoundaryMPSQuotient.quotientLocusPolynomial m) ≠ 0 := by
    rw [← hx'Q]
    exact hρψ
  have hdenx' : ∀ j, eval (OpenBoundaryMPSDensityGenericity.realCoordinates
      (fun ij => quotientRawPrefix m x' ij.1 ij.2))
      (quotientDenominatorFamily m j) ≠ 0 := by
    intro j
    exact quotient_denominators_nonzero m (quotientRawPrefix m x') hρx' j
  have hratx' := quotient_ratio_vector_local m x' hx'σ hρx'
  have hcx' := hclear
    (OpenBoundaryMPSDensityGenericity.realCoordinates
      (fun ij => quotientRawPrefix m x' ij.1 ij.2)) hdenx'
  rw [hratx'] at hcx'
  have hHrawx' : eval (OpenBoundaryMPSDensityGenericity.realCoordinates
      (fun ij => quotientRawPrefix m x' ij.1 ij.2)) H ≠ 0 := by
    have hmul : eval (OpenBoundaryMPSDensityGenericity.realCoordinates
        (fun ij => Qψ ij.1 ij.2))
        (OpenBoundaryMPSQuotient.quotientLocusPolynomial m * H) ≠ 0 := by
      simpa [G] using hGψ
    simp only [map_mul] at hmul
    have hHψ : eval (OpenBoundaryMPSDensityGenericity.realCoordinates
        (fun ij => Qψ ij.1 ij.2)) H ≠ 0 :=
      (mul_ne_zero_iff.mp hmul).2
    rw [← hx'Q]
    exact hHψ
  have hPx' : eval x' P ≠ 0 := by
    intro h
    have hdiv : eval (OpenBoundaryMPSDensityGenericity.realCoordinates
        (fun ij => quotientRawPrefix m x' ij.1 ij.2)) H /
        eval (OpenBoundaryMPSDensityGenericity.realCoordinates
          (fun ij => quotientRawPrefix m x' ij.1 ij.2)) B = 0 := by
      simpa [h] using hcx'.2.symm
    rcases (div_eq_zero_iff.mp hdiv) with hH | hB
    · exact False.elim (hHrawx' hH)
    · exact False.elim (hcx'.1 hB)
  have hx'J : eval x' J ≠ 0 := by
    exact (mul_ne_zero_iff.mp (by simpa [P] using hPx')).1
  have hx'lead : eval x' (leadingPolynomial m) ≠ 0 := by
    exact (mul_ne_zero_iff.mp (by simpa [P] using hPx')).2
  let S : Coordinates → (Word (3 + m) → ℂ) := fun y =>
    z • OpenBoundaryMPSTwoSiteMinimality.state (3 + m) (positiveRepresentative y)
  have hScont : Continuous S := by
    dsimp [S]
    exact (continuous_const : Continuous (fun _ : Coordinates => z)).smul
      (state_continuous m)
  let Ssub : Coordinates →
      OpenBoundaryMPSMarginalBirationality.openBoundaryMPS (3 + m) := fun y =>
    ⟨S y, openBoundaryMPS_smul (by
      exact ⟨OpenBoundaryMPSTwoSiteMinimality.core (positiveRepresentative y) 0,
        OpenBoundaryMPSTwoSiteMinimality.core (positiveRepresentative y) 1,
        OpenBoundaryMPSTwoSiteMinimality.left (positiveRepresentative y),
        OpenBoundaryMPSTwoSiteMinimality.right (positiveRepresentative y), rfl⟩) z⟩
  have hSsubcont : Continuous Ssub := hScont.subtype_mk _
  have hstate' : OpenBoundaryMPSTwoSiteMinimality.state (3 + m)
      (positiveRepresentative x') =
      OpenBoundaryMPSMarginalBirationality.mpsState (3 + m)
        (OpenBoundaryMPSTwoSiteMinimality.core p 0)
        (OpenBoundaryMPSTwoSiteMinimality.core p 1)
        (OpenBoundaryMPSTwoSiteMinimality.left p)
        (OpenBoundaryMPSQuotient.positiveBoundary p) := by
    have hrep := quotientCoordinates_positiveRepresentative p hpσ
    rw [hrep]
    exact positiveBoundary_state_eq m p
  have hSsubx : Ssub x' = ψ' := by
    apply Subtype.ext
    change z • OpenBoundaryMPSTwoSiteMinimality.state (3 + m)
        (positiveRepresentative x') = (ψ' : Word (3 + m) → ℂ)
    rw [hstate']
    exact hphase.symm
  let U : Set Coordinates := Ssub ⁻¹' O ∩ quotientValidityDomain m ∩
    {y | eval y J ≠ 0}
  have hUopen : IsOpen U := by
    simpa [U, inter_assoc] using
      (hSsubcont.isOpen_preimage O hO).inter
        ((quotientValidityDomain_open m).inter
          (isOpen_ne.preimage (MvPolynomial.continuous_eval J)))
  have hx'U : x' ∈ U := by
    refine ⟨?_, hx'J⟩
    refine ⟨?_, ?_⟩
    · change Ssub x' ∈ O
      rw [hSsubx]
      exact hψ'O
    · exact ⟨hx'σ, hρx', hx'lead⟩
  obtain ⟨K, q, f, ε, hε, hdim, hf0, hfc, hf, hpos⟩ :=
    (hJfiber x' hx'J).2 U hUopen hx'U
  obtain ⟨hKpos, y, hyU, hyx, hyrec⟩ := hpos (by decide)
  let φ₀ : Word (3 + m) → ℂ := S y
  have hφ₀ : φ₀ ∈ OpenBoundaryMPSMarginalBirationality.openBoundaryMPS (3 + m) := by
    exact openBoundaryMPS_smul (by
      exact ⟨OpenBoundaryMPSTwoSiteMinimality.core (positiveRepresentative y) 0,
        OpenBoundaryMPSTwoSiteMinimality.core (positiveRepresentative y) 1,
        OpenBoundaryMPSTwoSiteMinimality.left (positiveRepresentative y),
        OpenBoundaryMPSTwoSiteMinimality.right (positiveRepresentative y), rfl⟩) z
  let φ : OpenBoundaryMPSMarginalBirationality.openBoundaryMPS (3 + m) := ⟨φ₀, hφ₀⟩
  have hφV : φ ∈ V := hOV (by
    simpa [φ, φ₀, S, Ssub] using hyU.1.1)
  refine ⟨φ, hφV, ?_, ?_⟩
  · have hdens := record_equality_density (1 + m) hx'σ hyU.1.2.1
      (by
        intro h
        apply hx'lead
        rw [leadingPolynomial_eval m x' hx'σ.le]
        simp [h])
      hyrec
    have hzsq : Complex.normSq z = 1 := by
      rw [← Complex.sq_norm, hz]
      norm_num
    have hq2_scale (u : Coordinates) :
        actualQ2RawPrefix m (z • OpenBoundaryMPSTwoSiteMinimality.state
          (3 + m) (positiveRepresentative u)) =
          Complex.normSq z • actualQ2RawPrefix m
            (OpenBoundaryMPSTwoSiteMinimality.state
              (3 + m) (positiveRepresentative u)) := by
      unfold actualQ2RawPrefix
      rw [show (fun w =>
          (z • OpenBoundaryMPSTwoSiteMinimality.state (3 + m)
            (positiveRepresentative u)) (q2WordCast m w)) =
          z • (fun w => OpenBoundaryMPSTwoSiteMinimality.state (3 + m)
            (positiveRepresentative u) (q2WordCast m w)) by rfl]
      exact rawPrefix_scale_local 2 (1 + m) z
        (fun w => OpenBoundaryMPSTwoSiteMinimality.state
          (3 + m) (positiveRepresentative u) (q2WordCast m w))
    have hcast (u : OpenBoundaryMPSTwoSiteMinimality.Parameter) :
        (fun w : Word (2 + (1 + m)) =>
          OpenBoundaryMPSTwoSiteMinimality.state (3 + m) u (q2WordCast m w)) =
        OpenBoundaryMPSTwoSiteMinimality.state (2 + (1 + m)) u := by
      funext w
      simp [q2WordCast, OpenBoundaryMPSTwoSiteMinimality.state,
        OpenBoundaryMPSMarginalBirationality.mpsState, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm]
    have hψstate : (ψ' : Word (3 + m) → ℂ) = z •
        OpenBoundaryMPSTwoSiteMinimality.state (3 + m)
          (positiveRepresentative x') := by
      simpa [hstate'] using hphase
    rw [show (φ : Word (3 + m) → ℂ) = z •
        OpenBoundaryMPSTwoSiteMinimality.state (3 + m)
          (positiveRepresentative y) by rfl,
      hψstate]
    rw [hq2_scale, hq2_scale, hzsq]
    simp only [one_smul]
    change OpenBoundaryMPSDensityRecovery.rawPrefix 2 (1 + m)
        (fun w => OpenBoundaryMPSTwoSiteMinimality.state (3 + m)
          (positiveRepresentative y) (q2WordCast m w)) =
      OpenBoundaryMPSDensityRecovery.rawPrefix 2 (1 + m)
        (fun w => OpenBoundaryMPSTwoSiteMinimality.state (3 + m)
          (positiveRepresentative x') (q2WordCast m w))
    rw [hcast, hcast]
    exact hdens
  · intro hphaseφ
    obtain ⟨lambda, hlam, hphaseEq⟩ := hphaseφ
    have hNormSq : Complex.normSq lambda = 1 := by
      rw [← Complex.sq_norm, hlam]
      norm_num
    have hzsq : Complex.normSq z = 1 := by
      rw [← Complex.sq_norm, hz]
      norm_num
    have hQeq : quotientRawPrefix m y = quotientRawPrefix m x' := by
      have hraw := congrArg (fun v : Word (3 + m) → ℂ =>
          OpenBoundaryMPSDensityRecovery.rawPrefix 3 m v) hphaseEq
      have hφraw : OpenBoundaryMPSDensityRecovery.rawPrefix 3 m
          (φ : Word (3 + m) → ℂ) = quotientRawPrefix m y := by
        change OpenBoundaryMPSDensityRecovery.rawPrefix 3 m (z •
          OpenBoundaryMPSTwoSiteMinimality.state (3 + m)
            (positiveRepresentative y)) = _
        rw [rawPrefix_scale_local]
        have hzsq : Complex.normSq z = 1 := by
          rw [← Complex.sq_norm, hz]
          norm_num
        rw [hzsq]
        simpa [quotientRawPrefix]
      rw [hφraw] at hraw
      rw [rawPrefix_scale_local 3 m lambda, hNormSq] at hraw
      have hψQ : OpenBoundaryMPSDensityRecovery.rawPrefix 3 m
          (ψ' : Word (3 + m) → ℂ) = quotientRawPrefix m x' := by
        simpa [Qψ] using hx'Q
      rw [hψQ] at hraw
      norm_num at hraw
      exact hraw
    have hx'y := quotientCoordinates_retraction_local m y hyU.1.2.1
      (by exact hyU.1.2.2.1)
    have hxx := quotientCoordinates_retraction_local m x' hx'σ hρx'
    apply hyx
    rw [← hxx, ← hx'y, hQeq]

end D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSIntrinsicQ2Fiber
