/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSitePhysicalRankAssembly
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSitePhysicalRankAssembly
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: A nonvanishing slice minor gives full rank of the graph readout. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSitePhysicalRankBridge
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteGraphReadout
import Mathlib.LinearAlgebra.Matrix.Nondegenerate

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.SevenSitePhysicalRankAssembly

open Function Set Filter Matrix MvPolynomial
open scoped Matrix Kronecker Matrix.Norms.Elementwise ComplexConjugate Topology BigOperators
open SevenSitePhysicalRankBridge
open SevenSiteCriticalCertificate (V observedRow criticalMatrix rotationObservation rotationIndex)
open PeriodicMPSCompactReadout (Readout readout_apply)
open PeriodicMPSAmbiguityDensity (changePhysical pairBasis changePhysical_unitary_raw)
open TwoQubitMarginalReflection (Bits Density)
open private pauliFrame pauliFrame_hermitian trace_is_real
  from D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reflection.TwoQubitMarginalReflection
open private isHermitian_pairGram
  from D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteCompactReadout
open private certificate_pauli
  from D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteReadoutDerivative

open private phase phase_normSq centeredFrame frameTangent sectionNorm
  differentiable_ordinaryRaw differentiable_ordinaryMass hasDerivAt_eval_slice_line
  from D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSitePhysicalRankBridge

noncomputable section

private abbrev Bond := PeriodicMPSParentIntersection.Bond

private def complexMoment (ab : Fin 4 × Fin 4) (M : Density) : ℂ :=
  ((pauliFrame ab.1 ⊗ₖ pauliFrame ab.2) * M).trace

private theorem moment_real (ab : Fin 4 × Fin 4) {M : Density} (hM : M.IsHermitian) :
    ((complexMoment ab M).re : ℂ) = complexMoment ab M := by
  apply trace_is_real _ hM
  change (pauliFrame ab.1 ⊗ₖ pauliFrame ab.2)ᴴ = _
  rw [conjTranspose_kronecker, (pauliFrame_hermitian ab.1).eq, (pauliFrame_hermitian ab.2).eq]

private theorem rawRows_eq_moment (p : Ordinary) (i : Fin 10) :
    rawRows p i = (complexMoment (observedRow i) (ordinaryRaw p)).re := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [rawRows, ordinaryMass, complexMoment, observedRow, pauliFrame, one_kronecker_one]
  · rw [SevenSiteReadoutDerivative.observedRow_succ]
    exact readout_apply _ _

section

open private readout from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteCriticalCertificate

private theorem eval_value_eq_moment (x : SlicePoint) (ab : Fin 4 × Fin 4) :
    eval (fun i => (x i : ℂ)) (V Complex.I ab) =
      complexMoment ab (ordinaryRaw (sliceOrdinary x)) := by
  let d := (x 0 : ℂ) + Complex.I * (x 3 : ℂ)
  let e := (x 2 : ℂ) + Complex.I * (x 4 : ℂ)
  obtain ⟨A, ht, hs, hd, he, hk⟩ :=
    PeriodicMPSFiveSiteCoordinates.exists_trace_coordinates 1 0 d e (x 1)
  have hA : ((A 1).trace, (A 0).det, (A 1).det, (A 0 * A 1).trace) =
      sliceOrdinary x := by
    rw [sliceOrdinary, physicalChart_center, hs, hd, he, hk]
  have hp : SevenSiteCriticalCertificate.sliceBlock Complex.I (fun j => (x j : ℂ)) true =
      SevenSiteCriticalCertificate.alignedInvariants A := by
    simp [SevenSiteCriticalCertificate.sliceBlock, SevenSiteCriticalCertificate.alignedInvariants,
      hd, he, hk, d, e]
  have hm : SevenSiteCriticalCertificate.sliceBlock Complex.I (fun j => (x j : ℂ)) false =
      star ∘ SevenSiteCriticalCertificate.alignedInvariants A := by
    funext j
    fin_cases j <;>
      simp [SevenSiteCriticalCertificate.sliceBlock, SevenSiteCriticalCertificate.alignedInvariants,
        hd, he, hk, d, e, Complex.star_def]
  rw [SevenSiteCriticalCertificate.eval_value, SevenSiteCriticalCertificate.slicedObservation,
    hp, hm, ← hA, ordinaryRaw_actual A ht]
  simp only [SevenSiteCriticalCertificate.observation, readout,
    certificate_pauli, SevenSiteCriticalCertificate.rawGram_eq_rawTwo A ht hs,
    complexMoment, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.kroneckerMap_apply]
  rw [Finset.sum_comm]

end

open PeriodicMPSCompactReadout (readout)

private theorem eval_value_real (x : SlicePoint) (ab : Fin 4 × Fin 4) :
    ((eval (fun i => (x i : ℂ)) (V Complex.I ab)).re : ℂ) =
      eval (fun i => (x i : ℂ)) (V Complex.I ab) := by
  rw [eval_value_eq_moment]
  exact moment_real _ (isHermitian_pairGram _)

private theorem eval_partial_real (x : SlicePoint) (ab : Fin 4 × Fin 4) (j : Fin 5) :
    ((eval (fun i => (x i : ℂ)) (pderiv j (V Complex.I ab))).re : ℂ) =
      eval (fun i => (x i : ℂ)) (pderiv j (V Complex.I ab)) := by
  have h := hasDerivAt_eval_slice_line (V Complex.I ab) x j
  have hReal := (Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 h).ofReal_comp
  have eq (t : ℝ) := eval_value_real (x + t • Pi.single j 1) ab
  exact (hReal.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => (eq t).symm)).unique h

private def sectionTrace (v : Rotation) : ℂ :=
  (Complex.ofRealCLM v.2.1 - Complex.I * Complex.ofRealCLM v.1) / 2

private def unitaryLine (j : Fin 3) (t : ℝ) : Bond :=
  (sectionUnitary (sectionTrace (rotationLine j t)) (phase (rotationLine j t).2.2)
    (phase_normSq _)).val

private def normLine (j : Fin 3) (t : ℝ) : ℂ :=
  sectionNorm (sectionTrace (rotationLine j t))

private theorem normLine_zero (j : Fin 3) : normLine j 0 = 1 := by
  fin_cases j <;> simp [normLine, sectionNorm, sectionTrace, rotationLine]

private theorem hasDerivAt_normLine (j : Fin 3) : HasDerivAt (normLine j) 0 0 := by
  have hsq : HasDerivAt (fun t : ℝ => 1 + (t / 2) ^ 2) 0 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).div_const 2).pow 2).const_add 1
  have hs := (hsq.sqrt (by norm_num)).ofReal_comp
  have hc : HasDerivAt (fun _ : ℝ => (1 : ℂ)) 0 0 := hasDerivAt_const _ _
  have hh (t : ℝ) : Complex.normSq
      ((0 - Complex.I * (t : ℂ)) / 2) = (t / 2) ^ 2 := by
    simp only [zero_sub, Complex.normSq_div, Complex.normSq_neg, Complex.normSq_mul,
      Complex.normSq_I, Complex.normSq_ofReal, one_mul]
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) from rfl, Complex.normSq_ofReal]
    ring
  have hk (t : ℝ) : Complex.normSq ((t : ℂ) / 2) = (t / 2) ^ 2 := by
    rw [Complex.normSq_div, Complex.normSq_ofReal,
      show (2 : ℂ) = ((2 : ℝ) : ℂ) from rfl, Complex.normSq_ofReal]
    ring
  have hfirst (t : ℝ) : normLine 0 t = (Real.sqrt (1 + (t / 2) ^ 2) : ℂ) := by
    change (Real.sqrt (1 + Complex.normSq ((0 - Complex.I * (t : ℂ)) / 2)) : ℂ) = _
    rw [hh]
  have hsecond (t : ℝ) : normLine 1 t = (Real.sqrt (1 + (t / 2) ^ 2) : ℂ) := by
    change (Real.sqrt (1 + Complex.normSq (((t : ℂ) - Complex.I * 0) / 2)) : ℂ) = _
    rw [mul_zero, sub_zero, hk]
  have hthird (t : ℝ) : normLine 2 t = 1 := by
    change (Real.sqrt (1 + Complex.normSq ((0 - Complex.I * 0) / 2)) : ℂ) = _
    simp
  fin_cases j
  · change HasDerivAt (normLine 0) 0 0
    rw [show normLine 0 = _ from funext hfirst]
    simpa using hs
  · change HasDerivAt (normLine 1) 0 0
    rw [show normLine 1 = _ from funext hsecond]
    simpa using hs
  · change HasDerivAt (normLine 2) 0 0
    rw [show normLine 2 = _ from funext hthird]
    exact hc

private theorem unitaryLine_zero (j : Fin 3) : unitaryLine j 0 = 1 := by
  change (normLine j 0)⁻¹ • centeredFrame (rotationLine j 0) = 1
  rw [normLine_zero]
  fin_cases j <;>
    ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [centeredFrame, rotationLine, sectionMatrix, phase, Matrix.one_apply]

private theorem hasDerivAt_unitaryLine (j : Fin 3) (a b : Fin 2) :
    HasDerivAt (fun t => unitaryLine j t a b) (frameTangent j a b) 0 := by
  have h := ((hasDerivAt_normLine j).inv (by rw [normLine_zero]; exact one_ne_zero)).fun_mul
    (hasDerivAt_centeredFrame j a b)
  change HasDerivAt (fun t => (normLine j t)⁻¹ * centeredFrame (rotationLine j t) a b)
    (frameTangent j a b) 0
  simpa only [Pi.inv_apply, normLine_zero, inv_one, zero_div, neg_zero, zero_mul, one_mul,
    zero_add, add_zero] using h

private theorem hasDerivAt_normScalar (j : Fin 3) :
    HasDerivAt (fun t => normLine j t ^ 7 * star (normLine j t ^ 7)) 0 0 := by
  have h : HasDerivAt (fun t => normLine j t ^ 7) 0 0 := by
    simpa only [mul_zero] using (hasDerivAt_normLine j).fun_pow 7
  have hc := (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp_hasDerivAt 0 h
  simpa [Function.comp_def, Complex.conjCLE_apply, Complex.star_def] using h.fun_mul hc

private def MatrixJet {m n : Type*} (f : ℝ → Matrix m n ℂ) (df : Matrix m n ℂ) : Prop :=
  ∀ i j, HasDerivAt (fun t => f t i j) (df i j) 0

private theorem jet_const {m n : Type*} (M : Matrix m n ℂ) :
    MatrixJet (fun _ => M) 0 :=
  fun _ _ => hasDerivAt_const _ _

private theorem jet_mul {m n p : Type*} [Fintype n] {A : ℝ → Matrix m n ℂ}
    {B : ℝ → Matrix n p ℂ} {dA : Matrix m n ℂ} {dB : Matrix n p ℂ}
    (hA : MatrixJet A dA) (hB : MatrixJet B dB) :
    MatrixJet (fun t => A t * B t) (dA * B 0 + A 0 * dB) := by
  intro i j
  simpa only [Matrix.mul_apply, Matrix.add_apply, Finset.sum_add_distrib] using
    (HasDerivAt.fun_sum (u := Finset.univ) fun k _ => (hA i k).fun_mul (hB k j))

private theorem jet_adjoint {m n : Type*} {A : ℝ → Matrix m n ℂ} {dA : Matrix m n ℂ}
    (hA : MatrixJet A dA) : MatrixJet (fun t => (A t)ᴴ) dAᴴ := by
  intro i j
  change HasDerivAt (fun t => Complex.conjCLE (A t j i)) (Complex.conjCLE (dA j i)) 0
  exact (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp_hasDerivAt 0 (hA j i)

private theorem jet_kron {A B : ℝ → Bond} {dA dB : Bond}
    (hA : MatrixJet A dA) (hB : MatrixJet B dB) :
    MatrixJet (fun t => A t ⊗ₖ B t) ((dA ⊗ₖ B 0) + (A 0 ⊗ₖ dB)) := by
  intro i j
  simpa only [Matrix.kroneckerMap_apply, Matrix.add_apply] using
    (hA i.1 j.1).fun_mul (hB i.2 j.2)

private theorem jet_trace {n : Type*} [Fintype n] {A : ℝ → Matrix n n ℂ}
    {dA : Matrix n n ℂ} (hA : MatrixJet A dA) :
    HasDerivAt (fun t => (A t).trace) dA.trace 0 := by
  simpa only [Matrix.trace, Matrix.diag_apply] using
    (HasDerivAt.fun_sum (u := Finset.univ) fun i _ => hA i i)

private theorem hasJet_adjointPauli (j : Fin 3) (a : Fin 4) :
    MatrixJet (fun t => (unitaryLine j t)ᴴ * pauliFrame a * unitaryLine j t)
      (((rotationIndex j a).1 : ℂ) • pauliFrame (rotationIndex j a).2) := by
  have hU : MatrixJet (unitaryLine j) (frameTangent j) := hasDerivAt_unitaryLine j
  have h := jet_mul (jet_mul (jet_adjoint hU) (jet_const (pauliFrame a))) hU
  have hT : (frameTangent j)ᴴ = -frameTangent j := by
    simp only [frameTangent, conjTranspose_add, conjTranspose_smul,
      (pauliFrame_hermitian j.succ).eq, Complex.star_def, map_div₀,
      map_neg, Complex.conj_I, map_ofNat, neg_neg, neg_add]
    split <;> simp [conjTranspose_smul, Complex.star_def, map_div₀, neg_div, neg_smul]
  have he :
      (frameTangent j)ᴴ * pauliFrame a + pauliFrame a * frameTangent j =
        (((rotationIndex j a).1 : ℂ) • pauliFrame (rotationIndex j a).2) := by
    rw [hT, ← pauli_commutator_eq_rotationIndex]
    by_cases hj : j = 2 <;>
      simp [frameTangent, hj, add_mul, mul_add, Matrix.smul_mul,
        Matrix.mul_smul, smul_sub, neg_smul, neg_div] <;> abel
  simpa only [unitaryLine_zero, conjTranspose_one, mul_zero, add_zero, one_mul,
    mul_one, he] using h

private theorem hasDerivAt_complexMoment_rotation (x : SlicePoint) (ab : Fin 4 × Fin 4)
    (j : Fin 3) :
    HasDerivAt (fun t => complexMoment ab (ordinaryRaw (physicalChart 1 (rotationLine j t, x))))
      (eval (fun i => (x i : ℂ))
        (rotationObservation (C Complex.I) X j ab)) 0 := by
  let A := fun t : ℝ => (unitaryLine j t)ᴴ * pauliFrame ab.1 * unitaryLine j t
  let B := fun t : ℝ => (unitaryLine j t)ᴴ * pauliFrame ab.2 * unitaryLine j t
  let M := ordinaryRaw (sliceOrdinary x)
  have h := (hasDerivAt_normScalar j).fun_mul
    (jet_trace (jet_mul (jet_kron (hasJet_adjointPauli j ab.1)
      (hasJet_adjointPauli j ab.2)) (jet_const M)))
  have he (t : ℝ) : complexMoment ab (ordinaryRaw (physicalChart 1 (rotationLine j t, x))) =
      (normLine j t ^ 7 * star (normLine j t ^ 7)) * (((A t) ⊗ₖ (B t)) * M).trace := by
    have hc := ordinaryRaw_physicalChart 1 (by simp) (rotationLine j t, x)
    simp only [one_mul] at hc
    rw [complexMoment, hc, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
    change _ * ((pauliFrame ab.1 ⊗ₖ pauliFrame ab.2) *
      ((unitaryLine j t ⊗ₖ unitaryLine j t) * M *
        (unitaryLine j t ⊗ₖ unitaryLine j t)ᴴ)).trace = _
    congr 1
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm _ (_ᴴ), Matrix.conjTranspose_kronecker]
    unfold A B
    simp only [Matrix.mul_kronecker_mul, Matrix.mul_assoc]
  have hd :
      eval (fun i => (x i : ℂ)) (rotationObservation (C Complex.I) X j ab) =
        (((((rotationIndex j ab.1).1 : ℂ) • pauliFrame (rotationIndex j ab.1).2) ⊗ₖ B 0 +
          A 0 ⊗ₖ (((rotationIndex j ab.2).1 : ℂ) • pauliFrame (rotationIndex j ab.2).2)) *
            M).trace := by
    rw [SevenSiteCriticalCertificate.map_rotationObservation, eval_C]
    simp only [eval_X, rotationObservation, ← SevenSiteCriticalCertificate.eval_value,
      eval_value_eq_moment, complexMoment, M, A, B, unitaryLine_zero, conjTranspose_one,
      one_mul, mul_one, smul_kronecker, kronecker_smul, add_mul, smul_mul_assoc, trace_add,
      trace_smul, smul_eq_mul]
  rw [hd]
  apply HasDerivAt.congr_of_eventuallyEq _ (Filter.Eventually.of_forall he)
  simpa only [normLine_zero, one_pow, star_one, one_mul, zero_mul, zero_add, mul_zero,
    add_zero, A, B] using h

/-- The three physical columns are the real derivatives along the actual section. -/
theorem hasDerivAt_rawRows_rotation (x : SlicePoint) (i : Fin 10) (j : Fin 3) :
    HasDerivAt (fun t => rawRows (physicalChart 1 (rotationLine j t, x)) i)
      (eval (fun k => (x k : ℂ))
        (rotationObservation (C Complex.I) X j (observedRow i))).re 0 := by
  simpa only [Function.comp_def, Complex.reCLM_apply, rawRows_eq_moment] using
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0
      (hasDerivAt_complexMoment_rotation x (observedRow i) j)

private theorem eval_rotation_real (x : SlicePoint) (ab : Fin 4 × Fin 4) (j : Fin 3) :
    ((eval (fun k => (x k : ℂ)) (rotationObservation (C Complex.I) X j ab)).re : ℂ) =
      eval (fun k => (x k : ℂ)) (rotationObservation (C Complex.I) X j ab) := by
  rw [SevenSiteCriticalCertificate.map_rotationObservation, eval_C]
  simp only [eval_X]
  dsimp only [rotationObservation]
  simp only [← SevenSiteCriticalCertificate.eval_value, Complex.add_re, Complex.mul_re,
    Complex.intCast_re, Complex.intCast_im, zero_mul, sub_zero, Complex.ofReal_add,
    Complex.ofReal_mul, Complex.ofReal_intCast, eval_value_real]

private abbrev Tangent := Rotation × SlicePoint

private def rawChart (v : Tangent) : Fin 10 → ℝ := rawRows (physicalChart 1 v)

private theorem differentiable_rawRows : Differentiable ℝ rawRows := by
  apply differentiable_pi.mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact differentiable_ordinaryMass
  · exact (ContinuousLinearMap.proj j).differentiable.comp
      (readout.differentiable.comp differentiable_ordinaryRaw)

private theorem differentiableAt_rawChart (v : Tangent) : DifferentiableAt ℝ rawChart v :=
  differentiable_rawRows.differentiableAt.comp v (analyticAt_physicalChart 1 v).differentiableAt

private def augmented (x : SlicePoint) : Tangent × ℝ →L[ℝ] (Fin 10 → ℝ) :=
  (fderiv ℝ rawChart (0, x)).comp (ContinuousLinearMap.fst ℝ _ _) +
    ((ContinuousLinearMap.id ℝ ℝ).smulRight (rawRows (sliceOrdinary x))).comp
      (ContinuousLinearMap.snd ℝ _ _)

private def columnTangent (i : Fin 9) : Tangent × ℝ :=
  if h : i.val < 5 then ((0, Pi.single ⟨i.val, h⟩ 1), 0)
  else if i = 5 then (0, 1)
  else ((rotationLine ⟨i.val - 6, by omega⟩ 1, 0), 0)

private theorem column_jet {x : SlicePoint} {u : Tangent} {v : ℝ → Tangent} {a : ℝ}
    {i : Fin 10} (hv : HasFDerivAt v ((ContinuousLinearMap.id ℝ ℝ).smulRight u) 0)
    (hv0 : v 0 = (0, x)) (h : HasDerivAt (fun t => rawChart (v t) i) a 0) :
    fderiv ℝ rawChart (0, x) u i = a := by
  have hD : HasFDerivAt rawChart (fderiv ℝ rawChart (0, x)) (v 0) := by
    rw [hv0]
    exact (differentiableAt_rawChart (0, x)).hasFDerivAt
  have hcomp := hD.comp 0 hv
  have g := ((ContinuousLinearMap.proj i : (Fin 10 → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp
    0 hcomp).hasDerivAt
  exact (by simpa [Function.comp_def] using g :
    HasDerivAt (fun t => rawChart (v t) i) (fderiv ℝ rawChart (0, x) u i) 0).unique h

private theorem augmented_column (x : SlicePoint) (deleted : Fin 10) (i j : Fin 9) :
    (augmented x (columnTangent j) (deleted.succAbove i) : ℂ) =
      eval (fun k => (x k : ℂ)) (criticalMatrix Complex.I deleted i j) := by
  let r := deleted.succAbove i
  change (augmented x (columnTangent j) r : ℂ) = _
  have haug (u : Tangent) : augmented x (u, 0) r = fderiv ℝ rawChart (0, x) u r := by
    change fderiv ℝ rawChart (0, x) u r + (0 : ℝ) * rawRows (sliceOrdinary x) r = _
    rw [zero_mul, add_zero]
  by_cases hj : j.val < 5
  · let k : Fin 5 := ⟨j.val, hj⟩
    let u : Tangent := (0, Pi.single k 1)
    let v : ℝ → Tangent := fun t => (0, x) + t • u
    have hv : HasFDerivAt v ((ContinuousLinearMap.id ℝ ℝ).smulRight u) 0 := by
      simpa [v, Function.comp_def] using
        (((ContinuousLinearMap.id ℝ ℝ).smulRight u).hasFDerivAt.const_add (0, x))
    have he (t : ℝ) : v t = (0, x + t • Pi.single k 1) := by
      simp [v, u, Prod.smul_mk, Prod.mk_add_mk]
    have h := column_jet (x := x) (i := r) hv (by simp [v]) (by
      simpa only [he, rawChart, sliceOrdinary] using hasDerivAt_rawRows_slice x r k)
    simp only [columnTangent, criticalMatrix, dite_eq_left hj, haug]
    change ((fderiv ℝ rawChart (0, x) u r : ℝ) : ℂ) = _
    rw [h, eval_partial_real]
  · by_cases hr : j = 5
    · subst j
      simpa [columnTangent, augmented, criticalMatrix, rawRows_slice_eq_eval, r] using
        eval_value_real x (observedRow r)
    · let k : Fin 3 := ⟨j.val - 6, by omega⟩
      let u : Tangent := (rotationLine k 1, 0)
      let v : ℝ → Tangent := fun t => (0, x) + t • u
      have hv : HasFDerivAt v ((ContinuousLinearMap.id ℝ ℝ).smulRight u) 0 := by
        simpa [v, Function.comp_def] using
          (((ContinuousLinearMap.id ℝ ℝ).smulRight u).hasFDerivAt.const_add (0, x))
      have hline (k' : Fin 3) (t : ℝ) : t • rotationLine k' 1 = rotationLine k' t := by
        fin_cases k' <;> simp [rotationLine, Prod.smul_mk]
      have he (t : ℝ) : v t = (rotationLine k t, x) := by
        simp [v, u, Prod.smul_mk, Prod.mk_add_mk, hline]
      have h := column_jet (x := x) (i := r) hv (by simp [v]) (by
        simpa only [he, rawChart] using hasDerivAt_rawRows_rotation x r k)
      simp only [columnTangent, criticalMatrix, dite_eq_right hj, ite_eq_right hr, haug]
      change ((fderiv ℝ rawChart (0, x) u r : ℝ) : ℂ) = _
      rw [h, eval_rotation_real]

private def coordinates (w : Tangent × ℝ) : Fin 9 → ℝ :=
  ![w.1.2 0, w.1.2 1, w.1.2 2, w.1.2 3, w.1.2 4, w.2, w.1.1.1, w.1.1.2.1, w.1.1.2.2]

private theorem coordinates_injective : Injective coordinates := by
  intro a b h
  have h' (i : Fin 9) := congrFun h i
  refine Prod.ext (Prod.ext (Prod.ext (h' 6) (Prod.ext (h' 7) (h' 8))) ?_) (h' 5)
  funext i
  fin_cases i
  exacts [h' 0, h' 1, h' 2, h' 3, h' 4]

private theorem sum_columnTangent (w : Tangent × ℝ) :
    ∑ j : Fin 9, coordinates w j • columnTangent j = w := by
  rcases w with ⟨⟨⟨a, b, c⟩, x⟩, z⟩
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, columnTangent]
  norm_num [coordinates, rotationLine, Prod.smul_mk, Prod.mk_add_mk, zero_add]
  funext i
  fin_cases i <;> simp [Pi.single, Pi.smul_apply]

private theorem injective_augmented (x : SlicePoint) (deleted : Fin 10)
    (hm : eval (fun k => (x k : ℂ)) (criticalMatrix Complex.I deleted).det ≠ 0) :
    Injective (augmented x) := by
  let M : Matrix (Fin 9) (Fin 9) ℂ :=
    (criticalMatrix Complex.I deleted).map (eval (fun k => (x k : ℂ)))
  have hm' : M.det ≠ 0 := by
    rw [RingHom.map_det] at hm
    exact hm
  have he (w : Tangent × ℝ) (i : Fin 9) :
      (M *ᵥ (fun j => (coordinates w j : ℂ))) i =
        (augmented x w (deleted.succAbove i) : ℂ) := by
    calc
      _ = ∑ j : Fin 9, ((coordinates w j •
          augmented x (columnTangent j)) (deleted.succAbove i) : ℂ) := by
        simp only [Matrix.mulVec, dotProduct, M, Matrix.map_apply, ← augmented_column,
          Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul]
        exact Finset.sum_congr rfl fun j _ => mul_comm _ _
      _ = _ := by
        have hsum := congrArg (fun v : Fin 10 → ℝ => v (deleted.succAbove i))
          (map_sum (augmented x) (fun j => coordinates w j • columnTangent j) Finset.univ)
        rw [← Complex.ofReal_sum]
        apply congrArg Complex.ofReal
        simpa only [map_smul, sum_columnTangent, Finset.sum_apply] using hsum.symm
  intro a b hab
  apply coordinates_injective
  have hvec := Matrix.mulVec_injective_of_det_ne_zero hm'
    (show M *ᵥ (fun j => (coordinates a j : ℂ)) =
        M *ᵥ (fun j => (coordinates b j : ℂ)) by
      funext i
      rw [he, he, hab])
  exact funext fun i => Complex.ofReal_injective (congrFun hvec i)

/-- A nonzero evaluated physical cofactor forces injectivity of the literal trace-one
adjacent marginal differential at the aligned positive slice. -/
theorem ordinaryMarginal_injective_of_slice_minor (x : SlicePoint)
    (hx : 0 < x 1) (hA : ordinaryAmplitude (sliceOrdinary x) ≠ 0) (deleted : Fin 10)
    (hm : eval (fun k => (x k : ℂ)) (criticalMatrix Complex.I deleted).det ≠ 0) :
    Injective (fderiv ℝ ordinaryMarginal (sliceOrdinary x)) := by
  apply (ordinaryMarginal_injective_iff_augmented _ hA).mpr
  let P := fderiv ℝ (physicalChart 1) ((0 : Rotation), x)
  have hP := bijective_fderiv_physicalChart_center x hx
  have hchart := (analyticAt_physicalChart 1 ((0 : Rotation), x)).differentiableAt
  have hD : fderiv ℝ rawChart (0, x) =
      (fderiv ℝ rawRows (sliceOrdinary x)).comp P :=
    fderiv_comp _ differentiable_rawRows.differentiableAt hchart
  have hS (v : Tangent) (z : ℝ) :
      augmented x (v, z) =
        Fin.cons (fderiv ℝ ordinaryMass (sliceOrdinary x) (P v) +
          z * ordinaryMass (sliceOrdinary x))
          (fderiv ℝ (readout ∘ ordinaryRaw) (sliceOrdinary x) (P v) +
            z • readout (ordinaryRaw (sliceOrdinary x))) := by
    have hrow (i : Fin 10) :
        fderiv ℝ (fun p => rawRows p i) (sliceOrdinary x) =
          (ContinuousLinearMap.proj i).comp (fderiv ℝ rawRows (sliceOrdinary x)) :=
      ((ContinuousLinearMap.proj i : (Fin 10 → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp _
        differentiable_rawRows.differentiableAt.hasFDerivAt).fderiv
    have hMass :
        fderiv ℝ rawRows (sliceOrdinary x) (P v) 0 =
          fderiv ℝ ordinaryMass (sliceOrdinary x) (P v) :=
      (congrArg (fun L : Ordinary →L[ℝ] ℝ => L (P v)) (hrow 0)).symm
    have hReadout (j : Fin 9) :
        fderiv ℝ rawRows (sliceOrdinary x) (P v) j.succ =
          fderiv ℝ (readout ∘ ordinaryRaw) (sliceOrdinary x) (P v) j := by
      have hd : DifferentiableAt ℝ (readout ∘ ordinaryRaw) (sliceOrdinary x) :=
        (readout.differentiable.comp differentiable_ordinaryRaw).differentiableAt
      have hr := ((ContinuousLinearMap.proj j : Readout →L[ℝ] ℝ).hasFDerivAt.comp
        (sliceOrdinary x) hd.hasFDerivAt).fderiv
      have hl := congrArg (fun L : Ordinary →L[ℝ] ℝ => L (P v)) (hrow j.succ)
      have hh := congrArg (fun L : Ordinary →L[ℝ] ℝ => L (P v)) hr
      exact hl.symm.trans hh
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change fderiv ℝ rawChart (0, x) v 0 + z * ordinaryMass (sliceOrdinary x) = _
      rw [hD, ContinuousLinearMap.comp_apply, hMass] <;> rfl
    · change fderiv ℝ rawChart (0, x) v j.succ + z * readout (ordinaryRaw (sliceOrdinary x)) j =
        fderiv ℝ (readout ∘ ordinaryRaw) (sliceOrdinary x) (P v) j +
          z * readout (ordinaryRaw (sliceOrdinary x)) j
      rw [hD, ContinuousLinearMap.comp_apply, hReadout]
  rintro ⟨a, s⟩ ⟨b, t⟩ hab
  obtain ⟨v, hv⟩ := hP.2 a
  obtain ⟨w, hw⟩ := hP.2 b
  have hEq : augmented x (v, s) = augmented x (w, t) := by
    rw [hS, hS, hv, hw]
    exact congrArg (fun p : ℝ × Readout => Fin.cons (α := fun _ : Fin 10 => ℝ) p.1 p.2) hab
  have h := injective_augmented x deleted hm hEq
  exact Prod.ext (hv.symm.trans ((congrArg (fun p : Tangent × ℝ => P p.1) h).trans hw))
    (congrArg (fun p : Tangent × ℝ => p.2) h)


open private gaussianI gaussianToResidue_i gaussianToComplex_i map_raw_cofactor
  from D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteCriticalCharZero

/-- The origin of the certified affine line, in real slice coordinates. -/
def representative : SlicePoint := SevenSiteCriticalCertificate.origin ℝ

open SevenSiteCriticalCertificate in
theorem representative_minor :
    eval (fun k => (representative k : ℂ)) (criticalMatrix Complex.I 0).det ≠ 0 := by
  let a : Fin 5 → GaussianInt := origin GaussianInt
  let D : MvPolynomial (Fin 5) GaussianInt := (criticalMatrix gaussianI 0).det
  have hC : GaussianInt.toComplex (eval a D) =
      eval (fun k => (representative k : ℂ)) (criticalMatrix Complex.I 0).det := by
    rw [MvPolynomial.map_eval]
    dsimp only [D]
    rw [map_raw_cofactor, gaussianToComplex_i]
    apply congrArg (fun y : Fin 5 → ℂ => eval y (criticalMatrix Complex.I 0).det)
    funext i
    fin_cases i <;> simp [a, representative, origin, map_ofNat]
  have hF : gaussianToResidue (eval a D) =
      eval (point (0 : F)) (criticalMatrix imaginary 0).det := by
    rw [MvPolynomial.map_eval]
    dsimp only [D]
    rw [map_raw_cofactor, gaussianToResidue_i]
    apply congrArg (fun y : Fin 5 → F => eval y (criticalMatrix imaginary 0).det)
    funext i
    fin_cases i <;> simp [a, point, origin, map_ofNat]
  obtain ⟨q, _, hq, _, _, _, _⟩ := seven_site_modular_resultant
  have h431 : eval (point (0 : F)) (criticalMatrix imaginary 0).det = (431 : F) := by
    rw [hq, map_mul, eval_X, ← eval_affineRestriction,
      actual_line_quotient_eq 0 (.inl rfl) q hq, eval_lineQuotient]
    decide +kernel
  intro h
  have hzero : eval a D = 0 :=
    GaussianInt.toComplex_injective (by simpa only [hC, map_zero] using h)
  have hz : eval (point (0 : F)) (criticalMatrix imaginary 0).det = 0 := by
    rw [← hF, hzero, map_zero]
  rw [h431] at hz
  exact (by decide +kernel : (431 : F) ≠ 0) hz

theorem representative_rank :
    Injective (fderiv ℝ ordinaryMarginal (sliceOrdinary representative)) := by
  have hk : 0 < representative 1 := by
    norm_num [representative, SevenSiteCriticalCertificate.origin]
  apply ordinaryMarginal_injective_of_slice_minor representative hk _ 0 representative_minor
  intro h
  rw [sliceOrdinary, physicalChart_center, ordinaryAmplitude] at h
  have hzero := (SevenSiteTraceBase.amplitude_first_eq_zero_iff _ _ _ _).mp h
  exact (Complex.ofReal_ne_zero.mpr hk.ne') (by simpa using hzero.2.2)

open private mix_associates changePhysical_one rawTwo_scaled
  from D5.S3.Quantum.TensorNetworks.PeriodicMPSAmbiguityDensity
open private sectionNorm_pos differentiable_ordinaryAmplitude
  from D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSitePhysicalRankBridge

private abbrev Core := Fin 2 → Bond

private def coreOrdinary (A : Core) : Ordinary :=
  ((A 1).trace, (A 0).det, (A 1).det, (A 0 * A 1).trace)

private def restoredCore (U : Bond) (A : Core) : Core :=
  ((changePhysical U A 0).trace)⁻¹ • changePhysical U A

/-- The first trace before restoration of the affine coordinates. -/
def firstTrace (U : Bond) (p : Ordinary) : ℂ :=
  U 0 0 + U 0 1 * p.1

/-- Invariant coordinates after a fixed physical change and restoration of first trace one. -/
def fixedChart (U : Bond) (p : Ordinary) : Ordinary :=
  let s := p.1
  let d := p.2.1
  let e := p.2.2.1
  let k := p.2.2.2
  let τ := firstTrace U p
  let detAt (i : Fin 2) := d * U i 0 ^ 2 + (s - k) * U i 0 * U i 1 + e * U i 1 ^ 2
  let mix := U 0 0 * U 1 0 * (1 - 2 * d) +
    (U 0 0 * U 1 1 + U 0 1 * U 1 0) * k + U 0 1 * U 1 1 * (s ^ 2 - 2 * e)
  ((U 1 0 + U 1 1 * s) / τ, detAt 0 / τ ^ 2, detAt 1 / τ ^ 2, mix / τ ^ 2)

private theorem core_firstTrace (U : Bond) (A : Core) (hA : (A 0).trace = 1) :
    (changePhysical U A 0).trace = firstTrace U (coreOrdinary A) := by
  simp [changePhysical, firstTrace, coreOrdinary, Fin.sum_univ_two, trace_add, trace_smul,
    smul_eq_mul, hA]

private theorem restoredCore_trace (U : Bond) (A : Core)
    (h : (changePhysical U A 0).trace ≠ 0) : (restoredCore U A 0).trace = 1 := by
  simp [restoredCore, trace_smul, smul_eq_mul, h]

private theorem fixedChart_core (U : Bond) (A : Core) (hA : (A 0).trace = 1) :
    fixedChart U (coreOrdinary A) = coreOrdinary (restoredCore U A) := by
  let B := changePhysical U A
  let τ := (B 0).trace
  have hB (i : Fin 2) : B i = U i 0 • A 0 + U i 1 • A 1 := by
    simp [B, changePhysical, Fin.sum_univ_two]
  have hdet (i : Fin 2) : (B i).det = (A 0).det * U i 0 ^ 2 +
      ((A 1).trace - (A 0 * A 1).trace) * U i 0 * U i 1 + (A 1).det * U i 1 ^ 2 := by
    rw [hB]
    simpa [PeriodicMPSUniformDeterminantPencil.pencil,
      PeriodicMPSUniformHardCorePencilDecoder.crossDet, hA] using
      PeriodicMPSUniformHardCorePencilDecoder.det_pencil_binary A (U i 0) (U i 1)
  have hself (C : Bond) : (C * C).trace = C.trace ^ 2 - 2 * C.det := by
    simp [Matrix.trace_fin_two, Matrix.det_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  have hmix : (B 0 * B 1).trace =
      U 0 0 * U 1 0 * (1 - 2 * (A 0).det) +
      (U 0 0 * U 1 1 + U 0 1 * U 1 0) * (A 0 * A 1).trace +
      U 0 1 * U 1 1 * ((A 1).trace ^ 2 - 2 * (A 1).det) := by
    rw [hB 0, hB 1]
    simp only [add_mul, mul_add, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_add,
      Matrix.trace_smul, smul_eq_mul, hself, hA, one_pow, Matrix.trace_mul_comm (A 1) (A 0)]
    ring
  have hs : (B 1).trace = U 1 0 + U 1 1 * (A 1).trace := by
    rw [hB 1]
    simp [trace_add, trace_smul, smul_eq_mul, hA]
  unfold fixedChart
  rw [← core_firstTrace U A hA]
  change (_, _, _, _) = coreOrdinary (τ⁻¹ • B)
  simp only [coreOrdinary, Pi.smul_apply, trace_smul, det_smul,
    Fintype.card_fin, Matrix.smul_mul, Matrix.mul_smul, smul_eq_mul, hs, hdet, hmix,
    div_eq_mul_inv, inv_pow]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> ring

private theorem analyticAt_fixedChart (U : Bond) (p : Ordinary) (h : firstTrace U p ≠ 0) :
    AnalyticAt ℝ (fixedChart U) p := by
  have hs : AnalyticAt ℝ (fun q : Ordinary => q.1) p := analyticAt_fst
  have htail : AnalyticAt ℝ (fun q : Ordinary => q.2) p := analyticAt_snd
  have hd : AnalyticAt ℝ (fun q : Ordinary => q.2.1) p := analyticAt_fst.comp htail
  have hpair : AnalyticAt ℝ (fun q : Ordinary => q.2.2) p := analyticAt_snd.comp htail
  have he : AnalyticAt ℝ (fun q : Ordinary => q.2.2.1) p := analyticAt_fst.comp hpair
  have hk : AnalyticAt ℝ (fun q : Ordinary => q.2.2.2) p := analyticAt_snd.comp hpair
  have hτ : AnalyticAt ℝ (firstTrace U) p := by
    unfold firstTrace
    fun_prop
  have hτ₂ : AnalyticAt ℝ (fun q => firstTrace U q ^ 2) p := hτ.fun_pow 2
  have hτ₂ne : firstTrace U p ^ 2 ≠ 0 := pow_ne_zero 2 h
  unfold fixedChart
  dsimp only
  refine (AnalyticAt.fun_div ?_ hτ h).prod
    ((AnalyticAt.fun_div ?_ hτ₂ hτ₂ne).prod
      ((AnalyticAt.fun_div ?_ hτ₂ hτ₂ne).prod (AnalyticAt.fun_div ?_ hτ₂ hτ₂ne))) <;>
    fun_prop

private theorem changePhysical_smul (U : Bond) (z : ℂ) (A : Core) :
    changePhysical U (z • A) = z • changePhysical U A := by
  funext i
  simp only [changePhysical, Pi.smul_apply, Finset.smul_sum, smul_smul]
  exact Finset.sum_congr rfl fun j _ => by rw [mul_comm]

private theorem fixedChart_left_inv (U : Matrix.unitaryGroup (Fin 2) ℂ) (p : Ordinary)
    (hp : firstTrace U.val p ≠ 0) :
    fixedChart U.valᴴ (fixedChart U.val p) = p := by
  obtain ⟨A, hA, hs, hd, he, hk⟩ :=
    PeriodicMPSFiveSiteCoordinates.exists_trace_coordinates 1 p.1 p.2.1 p.2.2.1 p.2.2.2
  have ha : coreOrdinary A = p := by
    rcases p with ⟨s, d, e, k⟩
    exact Prod.ext hs (Prod.ext hd (Prod.ext he hk))
  let B := restoredCore U.val A
  let τ := (changePhysical U.val A 0).trace
  have hτ : τ ≠ 0 := by rw [show τ = _ from core_firstTrace _ _ hA, ha]; exact hp
  have hB : (B 0).trace = 1 := restoredCore_trace _ _ hτ
  have hU : U.valᴴ * U.val = 1 := Matrix.mem_unitaryGroup_iff'.mp U.property
  have hMix : changePhysical U.valᴴ B = τ⁻¹ • A := by
    rw [show B = τ⁻¹ • changePhysical U.val A from rfl, changePhysical_smul,
      mix_associates, hU, changePhysical_one]
  have hTrace : (changePhysical U.valᴴ B 0).trace = τ⁻¹ := by
    simp [hMix, trace_smul, smul_eq_mul, hA]
  rw [← ha, fixedChart_core U.val A hA, fixedChart_core U.valᴴ B hB]
  change coreOrdinary (restoredCore U.valᴴ B) = coreOrdinary A
  unfold restoredCore
  rw [hTrace, hMix, inv_inv, smul_smul, mul_inv_cancel₀ hτ, one_smul]

private theorem firstTrace_inverse (U : Matrix.unitaryGroup (Fin 2) ℂ) (p : Ordinary)
    (hp : firstTrace U.val p ≠ 0) :
    firstTrace U.valᴴ (fixedChart U.val p) ≠ 0 := by
  obtain ⟨A, hA, hs, hd, he, hk⟩ :=
    PeriodicMPSFiveSiteCoordinates.exists_trace_coordinates 1 p.1 p.2.1 p.2.2.1 p.2.2.2
  have ha : coreOrdinary A = p := by
    rcases p with ⟨s, d, e, k⟩
    exact Prod.ext hs (Prod.ext hd (Prod.ext he hk))
  let τ := (changePhysical U.val A 0).trace
  have hτ : τ ≠ 0 := by rw [show τ = _ from core_firstTrace _ _ hA, ha]; exact hp
  have hU : U.valᴴ * U.val = 1 := Matrix.mem_unitaryGroup_iff'.mp U.property
  rw [← ha, fixedChart_core U.val A hA, ← core_firstTrace _ _ (restoredCore_trace _ _ hτ)]
  change (changePhysical U.valᴴ (τ⁻¹ • changePhysical U.val A) 0).trace ≠ 0
  rw [changePhysical_smul, mix_associates, hU, changePhysical_one]
  simpa [trace_smul, smul_eq_mul, hA] using inv_ne_zero hτ

private theorem pairBasis_gram (U : Matrix.unitaryGroup (Fin 2) ℂ) :
    (pairBasis U.val)ᴴ * pairBasis U.val = 1 := by
  change (U.val ⊗ₖ U.val)ᴴ * (U.val ⊗ₖ U.val) = 1
  have hU : U.valᴴ * U.val = 1 := Matrix.mem_unitaryGroup_iff'.mp U.property
  rw [conjTranspose_kronecker, ← mul_kronecker_mul, hU, one_kronecker_one]

private def conjugation (U : Matrix.unitaryGroup (Fin 2) ℂ) : Density →L[ℝ] Density :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => pairBasis U.val * M * (pairBasis U.val)ᴴ
      map_add' := by intro M N; simp [mul_add, add_mul]
      map_smul' := by intro t M; simp }

private theorem conjugation_injective (U : Matrix.unitaryGroup (Fin 2) ℂ) :
    Injective (conjugation U) := by
  let K := pairBasis U.val
  have hK : Kᴴ * K = 1 := pairBasis_gram U
  intro M N h
  change K * M * Kᴴ = K * N * Kᴴ at h
  have recover (L : Density) : Kᴴ * (K * L * Kᴴ) * K = L := by
    rw [← mul_assoc Kᴴ (K * L) Kᴴ, ← mul_assoc Kᴴ K L, hK, one_mul, mul_assoc, hK, mul_one]
  simpa only [recover] using congrArg (fun L : Density => Kᴴ * L * K) h

private theorem trace_conjugation (U : Matrix.unitaryGroup (Fin 2) ℂ) (M : Density) :
    (conjugation U M).trace = M.trace := by
  change (pairBasis U.val * M * (pairBasis U.val)ᴴ).trace = M.trace
  rw [trace_mul_comm, ← mul_assoc, pairBasis_gram, one_mul]

private theorem fixedChart_raw (U : Matrix.unitaryGroup (Fin 2) ℂ) (p : Ordinary)
    (hp : firstTrace U.val p ≠ 0) :
    ordinaryRaw (fixedChart U.val p) =
      Complex.normSq ((firstTrace U.val p)⁻¹ ^ 7) • conjugation U (ordinaryRaw p) := by
  obtain ⟨A, hA, hs, hd, he, hk⟩ :=
    PeriodicMPSFiveSiteCoordinates.exists_trace_coordinates 1 p.1 p.2.1 p.2.2.1 p.2.2.2
  have ha : coreOrdinary A = p := by
    rcases p with ⟨s, d, e, k⟩
    exact Prod.ext hs (Prod.ext hd (Prod.ext he hk))
  let τ := (changePhysical U.val A 0).trace
  have hτ : τ = firstTrace U.val p := (core_firstTrace _ _ hA).trans (congrArg _ ha)
  let B := restoredCore U.val A
  have hτne : τ ≠ 0 := by rwa [hτ]
  have ht : (B 0).trace = 1 := restoredCore_trace U.val A hτne
  have hb : fixedChart U.val p = coreOrdinary B := by
    rw [← ha, fixedChart_core U.val A hA]
  have hRawA : ordinaryRaw p = PeriodicMPSTwoSiteAmbiguity.rawTwo A 3 :=
    (congrArg ordinaryRaw ha.symm).trans (ordinaryRaw_actual A hA)
  have hRawB : ordinaryRaw (fixedChart U.val p) = PeriodicMPSTwoSiteAmbiguity.rawTwo B 3 :=
    (congrArg ordinaryRaw hb).trans (ordinaryRaw_actual B ht)
  rw [hRawB, hRawA, show B = τ⁻¹ • changePhysical U.val A from rfl,
    rawTwo_scaled, changePhysical_unitary_raw]
  change (τ⁻¹ ^ 7 * star (τ⁻¹ ^ 7)) • _ = _
  simp only [Complex.star_def, Complex.mul_conj, hτ]
  rfl

private theorem fixedChart_marginal (U : Matrix.unitaryGroup (Fin 2) ℂ) (p : Ordinary)
    (hp : firstTrace U.val p ≠ 0) :
    ordinaryMarginal (fixedChart U.val p) = conjugation U (ordinaryMarginal p) := by
  let c := Complex.normSq ((firstTrace U.val p)⁻¹ ^ 7)
  have hc : c ≠ 0 := (Complex.normSq_pos.mpr (pow_ne_zero _ (inv_ne_zero hp))).ne'
  have hm : ordinaryMass (fixedChart U.val p) = c * ordinaryMass p := by
    change (ordinaryRaw (fixedChart U.val p)).trace.re = c * (ordinaryRaw p).trace.re
    rw [fixedChart_raw U p hp, Matrix.trace_smul, Complex.smul_re, trace_conjugation]
    rfl
  rw [ordinaryMarginal_eq_normalizedRaw, ordinaryMarginal_eq_normalizedRaw,
    hm, fixedChart_raw U p hp, map_smul, smul_smul]
  change ((c * ordinaryMass p)⁻¹ * c) • _ = _
  rw [_root_.mul_inv_rev, mul_assoc, inv_mul_cancel₀ hc, mul_one]

/-- Transport of the literal differential under a fixed physical unitary and the
local inverse obtained by undoing that unitary and restoring first trace one. -/
theorem ordinaryMarginal_injective_fixedChart
    (U : Matrix.unitaryGroup (Fin 2) ℂ) (p : Ordinary) (hp : firstTrace U.val p ≠ 0)
    (hA : ordinaryAmplitude p ≠ 0) (hB : ordinaryAmplitude (fixedChart U.val p) ≠ 0)
    (h : Injective (fderiv ℝ ordinaryMarginal p)) :
    Injective (fderiv ℝ ordinaryMarginal (fixedChart U.val p)) := by
  let F := fixedChart U.val
  let G := fixedChart U.valᴴ
  have hF : DifferentiableAt ℝ F p := (analyticAt_fixedChart _ _ hp).differentiableAt
  have hG : DifferentiableAt ℝ G (F p) :=
    (analyticAt_fixedChart _ _ (firstTrace_inverse U p hp)).differentiableAt
  have hnear : ∀ᶠ q in 𝓝 p, firstTrace U.val q ≠ 0 := by
    have ht : Continuous (firstTrace U.val) := by unfold firstTrace; fun_prop
    exact ht.continuousAt.eventually_ne hp
  have hInv : G ∘ F =ᶠ[𝓝 p] id :=
    hnear.mono (fun q hq => fixedChart_left_inv U q hq)
  have hCov : ordinaryMarginal ∘ F =ᶠ[𝓝 p] conjugation U ∘ ordinaryMarginal :=
    hnear.mono (fun q hq => fixedChart_marginal U q hq)
  let P := fderiv ℝ F p
  have hI : (fderiv ℝ G (F p)).comp P = ContinuousLinearMap.id ℝ Ordinary := by
    rw [← fderiv_comp p hG hF, hInv.fderiv_eq, fderiv_id]
  have hinj : Injective P := by
    intro a b hab
    simpa only [← ContinuousLinearMap.comp_apply, hI, ContinuousLinearMap.id_apply] using
      congrArg (fderiv ℝ G (F p)) hab
  have hsurj : Surjective P :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp
      (show Injective P.toLinearMap from hinj)
  have hD : (fderiv ℝ ordinaryMarginal (F p)).comp P =
      (conjugation U).comp (fderiv ℝ ordinaryMarginal p) := by
    have hB' : DifferentiableAt ℝ ordinaryMarginal (F p) :=
      differentiableAt_ordinaryMarginal _ hB
    have hRight : HasFDerivAt (conjugation U ∘ ordinaryMarginal)
        ((conjugation U).comp (fderiv ℝ ordinaryMarginal p)) p :=
      (conjugation U).hasFDerivAt.comp p (differentiableAt_ordinaryMarginal p hA).hasFDerivAt
    exact (hB'.hasFDerivAt.comp p hF.hasFDerivAt).unique (hRight.congr_of_eventuallyEq hCov)
  have hcomp : Injective (fderiv ℝ ordinaryMarginal (F p) ∘ P) := by
    change Injective ((fderiv ℝ ordinaryMarginal (F p)).comp P)
    rw [hD]
    exact (conjugation_injective U).comp h
  exact hcomp.of_comp_right hsurj

private theorem fixedChart_section (s l : ℂ) (hl : Complex.normSq l = 1) (x : SlicePoint) :
    fixedChart (sectionUnitary s l hl).val (sliceOrdinary x) =
      unalign (s, (x 0 : ℂ) + Complex.I * (x 3 : ℂ),
        l ^ 2 * ((x 2 : ℂ) + Complex.I * (x 4 : ℂ)), l * (x 1 : ℂ)) := by
  let d := (x 0 : ℂ) + Complex.I * (x 3 : ℂ)
  let e := (x 2 : ℂ) + Complex.I * (x 4 : ℂ)
  obtain ⟨A, ht, hs, hd, he, hk⟩ :=
    PeriodicMPSFiveSiteCoordinates.exists_trace_coordinates 1 0 d e (x 1)
  let S := sectionMatrix s l
  let U := sectionUnitary s l hl
  let r := (sectionNorm s : ℂ)
  have hr : r ≠ 0 := Complex.ofReal_ne_zero.mpr (sectionNorm_pos s).ne'
  have hAs : coreOrdinary A = sliceOrdinary x := by
    rw [sliceOrdinary, physicalChart_center]
    simp [coreOrdinary, hs, hd, he, hk, d, e]
  have hS := sectionMatrix_invariants A ht hs s l
  have hU : changePhysical U.val A = r⁻¹ • changePhysical S A := by
    funext i
    change changePhysical (r⁻¹ • S) A i = _
    simp [changePhysical, Matrix.smul_apply, smul_smul, smul_eq_mul]
  have htr : (changePhysical U.val A 0).trace = r⁻¹ := by
    rw [hU]
    simp [S, trace_smul, smul_eq_mul, hS.1]
  have hrest : restoredCore U.val A = changePhysical S A := by
    rw [restoredCore, htr, hU, inv_inv, smul_smul, mul_inv_cancel₀ hr, one_smul]
  rw [← hAs, fixedChart_core _ _ ht, hrest]
  simpa only [coreOrdinary, S, hd, he, hk] using hS.2

/-- The slice certificate applies at an arbitrary frozen rotated chart center. -/
theorem ordinaryMarginal_injective_of_rotated_minor
    (s l : ℂ) (hl : Complex.normSq l = 1) (x : SlicePoint) (hx : 0 < x 1)
    (hA : ordinaryAmplitude (sliceOrdinary x) ≠ 0) (p : Ordinary)
    (hp : p = unalign (s, (x 0 : ℂ) + Complex.I * (x 3 : ℂ),
        l ^ 2 * ((x 2 : ℂ) + Complex.I * (x 4 : ℂ)), l * (x 1 : ℂ)))
    (hB : ordinaryAmplitude p ≠ 0) (deleted : Fin 10)
    (hm : eval (fun k => (x k : ℂ)) (criticalMatrix Complex.I deleted).det ≠ 0) :
    Injective (fderiv ℝ ordinaryMarginal p) := by
  let U := sectionUnitary s l hl
  have ht : firstTrace U.val (sliceOrdinary x) ≠ 0 := by
    rw [sliceOrdinary, physicalChart_center]
    change ((sectionNorm s : ℂ)⁻¹ * 1 + U.val 0 1 * 0) ≠ 0
    simpa using inv_ne_zero (Complex.ofReal_ne_zero.mpr (sectionNorm_pos s).ne')
  have hp' : fixedChart U.val (sliceOrdinary x) = p :=
    (fixedChart_section s l hl x).trans hp.symm
  rw [← hp'] at hB ⊢
  exact ordinaryMarginal_injective_fixedChart U _ ht hA hB
    (ordinaryMarginal_injective_of_slice_minor x hx hA deleted hm)

/-- The positive aligned mixed trace and the other four real slice coordinates. -/
def alignedSlice (p : Ordinary) : SlicePoint :=
  let (_, d, E, K) := align p
  let r := Real.sqrt (Complex.normSq K)
  let l := K / (r : ℂ)
  let e := E / l ^ 2
  ![d.re, r, e.re, d.im, e.im]

theorem ordinaryMarginal_injective_of_minor (p : Ordinary) (hp : ordinaryAmplitude p ≠ 0)
    (hK : (align p).2.2.2 ≠ 0) (deleted : Fin 10)
    (hm : eval (fun i => (alignedSlice p i : ℂ)) (criticalMatrix Complex.I deleted).det ≠ 0) :
    Injective (fderiv ℝ ordinaryMarginal p) := by
  let q := align p
  let K := q.2.2.2
  let r := Real.sqrt (Complex.normSq K)
  let l := K / (r : ℂ)
  let x := alignedSlice p
  have hr : 0 < r := Real.sqrt_pos.2 (Complex.normSq_pos.2 hK)
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hlne : l ≠ 0 := div_ne_zero hK hrC
  have hl : Complex.normSq l = 1 := by
    rw [show l = K / (r : ℂ) from rfl, Complex.normSq_div, Complex.normSq_ofReal]
    rw [← pow_two, Real.sq_sqrt (Complex.normSq_nonneg K),
      div_self (Complex.normSq_pos.2 hK).ne']
  have hx : 0 < x 1 := hr
  have hA : ordinaryAmplitude (sliceOrdinary x) ≠ 0 := by
    intro hz
    rw [sliceOrdinary, physicalChart_center, ordinaryAmplitude] at hz
    have hz' := (SevenSiteTraceBase.amplitude_first_eq_zero_iff _ _ _ _).mp hz
    exact (Complex.ofReal_ne_zero.mpr hx.ne') (by simpa using hz'.2.2)
  have hd : (x 0 : ℂ) + Complex.I * (x 3 : ℂ) = q.2.1 := by
    change (q.2.1.re : ℂ) + Complex.I * (q.2.1.im : ℂ) = q.2.1
    rw [mul_comm Complex.I, Complex.re_add_im]
  have he : (x 2 : ℂ) + Complex.I * (x 4 : ℂ) = q.2.2.1 / l ^ 2 := by
    change ((q.2.2.1 / l ^ 2).re : ℂ) + Complex.I * ((q.2.2.1 / l ^ 2).im : ℂ) = _
    rw [mul_comm Complex.I, Complex.re_add_im]
  have hk : l * (x 1 : ℂ) = K := div_mul_cancel₀ _ hrC
  have hq : p = unalign (q.1, (x 0 : ℂ) + Complex.I * (x 3 : ℂ),
      l ^ 2 * ((x 2 : ℂ) + Complex.I * (x 4 : ℂ)), l * (x 1 : ℂ)) := by
    rw [hd, he, ← mul_div_assoc, mul_div_cancel_left₀ _ (pow_ne_zero 2 hlne), hk]
    exact (unalign_align p).symm
  exact ordinaryMarginal_injective_of_rotated_minor q.1 l hl x hx hA p hq hp deleted hm

section Graph

open SevenSiteCompactGraph SevenSiteGraphReadout

def asOrdinary : Parameters →L[ℝ] Ordinary :=
  LinearMap.toContinuousLinearMap
    { toFun := fun u => (u 0, u 1, u 2, u 3)
      map_add' := by intro a b; rfl
      map_smul' := by intro a b; rfl }

private theorem asOrdinary_injective : Injective asOrdinary := by
  intro a b h
  have h₀ : a 0 = b 0 := congrArg Prod.fst h
  have h₁ : a 1 = b 1 := congrArg (fun w : Ordinary => w.2.1) h
  have h₂ : a 2 = b 2 := congrArg (fun w : Ordinary => w.2.2.1) h
  have h₃ : a 3 = b 3 := congrArg (fun w : Ordinary => w.2.2.2) h
  funext i
  fin_cases i
  exacts [h₀, h₁, h₂, h₃]

/-- Ambient analytic-coordinate formula for the ordinary graph readout. -/
def graphReadout (u : Parameters) : Readout :=
  readout (ordinaryMarginal (asOrdinary u))

theorem graphReadout_eqOn : EqOn graphReadout (observe ∘ chart) chart.source := by
  intro u hu
  change graphReadout u = readout (PeriodicMPSUniformHardCoreLocalization.twoSiteObservation 5
    (chart u).val.2)
  have hs : u ∈ chartDomain := hu
  have hchart : (chart u).val = SevenSiteCompactGraph.graph (traceChart u) := by
    change (chart.toFun u).val = _
    simp only [chart, dite_eq_left hs]
  rw [hchart]
  rfl

theorem injective_fderiv_graphReadout (u : Parameters) (hu : u ∈ chart.source)
    (hK : (align (asOrdinary u)).2.2.2 ≠ 0) (deleted : Fin 10)
    (hm : eval (fun i => (alignedSlice (asOrdinary u) i : ℂ))
      (criticalMatrix Complex.I deleted).det ≠ 0) :
    Injective (fderiv ℝ graphReadout u) := by
  have hA : ordinaryAmplitude (asOrdinary u) ≠ 0 := hu
  have h := (ordinaryMarginal_injective_iff_readout _ hA).mp
    (ordinaryMarginal_injective_of_minor _ hA hK deleted hm)
  have hd : DifferentiableAt ℝ (readout ∘ ordinaryMarginal) (asOrdinary u) :=
    readout.differentiableAt.comp _ (differentiableAt_ordinaryMarginal _ hA)
  change Injective (fderiv ℝ ((readout ∘ ordinaryMarginal) ∘ asOrdinary) u)
  rw [fderiv_comp u hd asOrdinary.differentiableAt, ContinuousLinearMap.fderiv]
  exact h.comp asOrdinary_injective

end Graph

#print axioms ordinaryMarginal_injective_of_slice_minor
#print axioms representative_minor
#print axioms representative_rank
#print axioms ordinaryMarginal_injective_of_minor
#print axioms injective_fderiv_graphReadout

end

end D5.S3.Quantum.TensorNetworks.SevenSitePhysicalRankAssembly
