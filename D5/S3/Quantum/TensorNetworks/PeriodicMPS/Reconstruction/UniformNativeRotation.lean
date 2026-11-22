/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/UniformNativeRotation
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/UniformNativeRotation
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: Physical rotation columns of the uniform ordinary chart. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.UniformNativeSliceReadout
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSitePhysicalRankAssembly

/-!
# Physical rotation columns of the uniform ordinary chart

The covariance of the adjacent Gram matrix holds with any number of residual
sites, including zero. At the centered chart the derivative of the scalar
length factor is zero, leaving the signed action on each Pauli index.

For the augmented matrix, use `rawReadout_slice_eq_eval` for column 5,
`fderiv_rawReadout_sliceColumn` for columns 0 through 4, and
`fderiv_rawReadout_rotationColumn` for columns 6 through 8. All three use
`observedRow`. Precompose with `deleted.succAbove` for a deleted row.
For rank, pull the derivative back by `bijective_fderiv_physicalChart_center`
when `0 < x 1`, and apply `UniformRankNormalization.finrank_rawReadout_span`
when the ordinary amplitude is nonzero.
-/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.UniformNativeRotation

open Matrix MvPolynomial
open scoped BigOperators Matrix Kronecker Matrix.Norms.Elementwise
open PeriodicMPSParentIntersection (Bond Word wordMatrix wordMatrix_append)
open PeriodicMPSUniformHardCoreMarginalWitness (pairGram)
open PeriodicMPSAmbiguityDensity (changePhysical pairBasis)
open UniformMPSExpectedDimensionRefutation (traceWord)
open TwoQubitMarginalReflection (Bits Density)
open PeriodicMPSCompactReadout (readout readout_apply)
open SevenSitePhysicalRankBridge
  (Rotation SlicePoint physicalChart physicalChart_center sliceOrdinary rotationLine
    sectionMatrix sectionUnitary sectionMatrix_invariants analyticAt_physicalChart)
open SevenSiteCriticalCertificate (V observedRow rotationIndex rotationObservation)
open SevenSiteReadoutDerivative (observedRow_succ)
open UniformRankNormalization (Ordinary ordinaryAmplitude ordinaryRaw ordinaryMass rawReadout)
open PeriodicMPSUniformNativeSliceReadout (rawSlicePolynomial eval_rawSlicePolynomial_eq_moment)

open private join from
  D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformHardCoreMarginalWitness
open private wordBasis wordMatrix_changePhysical wordMatrix_scaled wordBasis_transpose
  wordBasis_star wordBasis_mul wordBasis_one from
  D5.S3.Quantum.TensorNetworks.PeriodicMPSAmbiguityDensity
open private pauliFrame from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reflection.TwoQubitMarginalReflection
open private phase phase_normSq sectionNorm sectionNorm_pos from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSitePhysicalRankBridge
open private complexMoment moment_real sectionTrace unitaryLine normLine normLine_zero
  hasDerivAt_normLine unitaryLine_zero jet_mul jet_kron jet_const jet_trace hasJet_adjointPauli
  eval_value_eq_moment from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSitePhysicalRankAssembly
open private isHermitian_pairGram from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteCompactReadout
open private differentiable_ordinaryMass differentiable_ordinaryRaw from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.UniformRankNormalization
open private rawRow rawRow_apply from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.UniformNativeSliceReadout

noncomputable section

private abbrev Core := Fin 2 → Bond

private def adjacentAmplitudes (m : ℕ) (A : Core) : Matrix Bits (Word m) ℂ :=
  fun p w => traceWord 2 2 (2 + m) A (join p w)

private theorem adjacentAmplitudes_apply (m : ℕ) (A : Core) (i j : Fin 2) (w : Word m) :
    adjacentAmplitudes m A (i, j) w = (A i * A j * wordMatrix A w).trace := by
  change (wordMatrix A (Fin.append ![i, j] w)).trace = _
  rw [wordMatrix_append]
  simp [wordMatrix, List.ofFn_succ]

private theorem pairGram_eq_adjacentAmplitudes (m : ℕ) (A : Core) :
    pairGram (m := m) (traceWord 2 2 (2 + m) A) =
      adjacentAmplitudes m A * (adjacentAmplitudes m A)ᴴ := by
  ext p q
  simp only [pairGram, adjacentAmplitudes, Matrix.mul_apply, Matrix.conjTranspose_apply]

private theorem adjacentAmplitudes_changePhysical (m : ℕ) (U : Bond) (A : Core) :
    adjacentAmplitudes m (changePhysical U A) =
      pairBasis U * adjacentAmplitudes m A * (wordBasis U m).transpose := by
  classical
  ext ⟨i, j⟩ w
  rw [adjacentAmplitudes_apply m (changePhysical U A), wordMatrix_changePhysical]
  simp only [changePhysical, Matrix.mul_apply, Matrix.transpose_apply, pairBasis]
  simp only [Finset.sum_mul, Finset.mul_sum, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro v _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [adjacentAmplitudes_apply]
  ring

private theorem pairGram_changePhysical_unitary (m : ℕ)
    (U : Matrix.unitaryGroup (Fin 2) ℂ) (A : Core) :
    pairGram (m := m) (traceWord 2 2 (2 + m) (changePhysical U.val A)) =
      pairBasis U.val * pairGram (m := m) (traceWord 2 2 (2 + m) A) * (pairBasis U.val)ᴴ := by
  have hu : U.val.transpose * (U.val.transpose)ᴴ = 1 :=
    Matrix.mem_unitaryGroup_iff.mp (Matrix.transpose_mem_unitaryGroup_iff.mpr U.property)
  have hword : (wordBasis U.val m).transpose * ((wordBasis U.val m).transpose)ᴴ = 1 := by
    rw [← wordBasis_transpose, ← wordBasis_star, ← wordBasis_mul, hu, wordBasis_one]
  rw [pairGram_eq_adjacentAmplitudes m (changePhysical U.val A),
    pairGram_eq_adjacentAmplitudes m A, adjacentAmplitudes_changePhysical,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Matrix.transpose _) (Matrix.conjTranspose _) _, hword, Matrix.one_mul]

private theorem adjacentAmplitudes_scaled (m : ℕ) (z : ℂ) (A : Core) :
    adjacentAmplitudes m (z • A) = z ^ (2 + m) • adjacentAmplitudes m A := by
  ext p w
  change (wordMatrix (z • A) (join p w)).trace = z ^ (2 + m) * (wordMatrix A (join p w)).trace
  rw [wordMatrix_scaled, Matrix.trace_smul, smul_eq_mul]

private theorem pairGram_scaled (m : ℕ) (z : ℂ) (A : Core) :
    pairGram (m := m) (traceWord 2 2 (2 + m) (z • A)) =
      (z ^ (2 + m) * star (z ^ (2 + m))) • pairGram (m := m) (traceWord 2 2 (2 + m) A) := by
  rw [pairGram_eq_adjacentAmplitudes m (z • A), pairGram_eq_adjacentAmplitudes m A,
    adjacentAmplitudes_scaled, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul]

private theorem pairGram_sectionMatrix (m : ℕ) (A : Core) (s l : ℂ)
    (hl : Complex.normSq l = 1) :
    let U := (sectionUnitary s l hl).val
    let r : ℂ := sectionNorm s
    pairGram (m := m) (traceWord 2 2 (2 + m) (changePhysical (sectionMatrix s l) A)) =
      r ^ (2 * (2 + m)) •
        (pairBasis U * pairGram (m := m) (traceWord 2 2 (2 + m) A) * (pairBasis U)ᴴ) := by
  dsimp only
  let r : ℂ := sectionNorm s
  let U := sectionUnitary s l hl
  have hr : r ≠ 0 := Complex.ofReal_ne_zero.2 (sectionNorm_pos s).ne'
  have hframe : sectionMatrix s l = r • U.val := by
    change sectionMatrix s l = r • (r⁻¹ • sectionMatrix s l)
    rw [smul_smul, mul_inv_cancel₀ hr, one_smul]
  have hmix : changePhysical (sectionMatrix s l) A = r • changePhysical U.val A := by
    rw [hframe]
    funext i
    simp only [changePhysical, Pi.smul_apply, Matrix.smul_apply, Finset.smul_sum,
      smul_eq_mul, mul_smul]
  have hstar : star r = r := by
    simpa only [r, Complex.star_def] using Complex.conj_ofReal (sectionNorm s)
  rw [hmix, pairGram_scaled, pairGram_changePhysical_unitary, star_pow, hstar, ← pow_add,
    ← two_mul]

private theorem ordinaryRaw_actual (m : ℕ) (A : Core) (ht : (A 0).trace = 1) :
    ordinaryRaw m ((A 1).trace, (A 0).det, (A 1).det, (A 0 * A 1).trace) =
      pairGram (m := m) (traceWord 2 2 (2 + m) A) := by
  have hAmplitude :
      ordinaryAmplitude m ((A 1).trace, (A 0).det, (A 1).det, (A 0 * A 1).trace) =
        traceWord 2 2 (2 + m) A := by
    funext w
    simpa only [ordinaryAmplitude, ht, SevenSiteTraceBase.wordProduct, traceWord] using
      SevenSiteTraceBase.wordPolynomial_eq_trace A w
  rw [ordinaryRaw, hAmplitude]

/-- The ordinary raw marginal is transported by the physical section, with
one norm factor for each ket and bra site. -/
theorem ordinaryRaw_physicalChart (m : ℕ) (centerPhase : ℂ)
    (hPhase : Complex.normSq centerPhase = 1) (v : Rotation × SlicePoint) :
    let s := sectionTrace v.1
    let l := centerPhase * phase v.1.2.2
    let hl : Complex.normSq l = 1 := by
      change Complex.normSq (centerPhase * phase v.1.2.2) = 1
      rw [Complex.normSq_mul, hPhase, phase_normSq, one_mul]
    let U := (sectionUnitary s l hl).val
    let r : ℂ := sectionNorm s
    ordinaryRaw m (physicalChart centerPhase v) =
      r ^ (2 * (2 + m)) • (pairBasis U * ordinaryRaw m (sliceOrdinary v.2) * (pairBasis U)ᴴ) := by
  dsimp only
  let x := v.2
  let d := (x 0 : ℂ) + Complex.I * (x 3 : ℂ)
  let e := (x 2 : ℂ) + Complex.I * (x 4 : ℂ)
  let s := sectionTrace v.1
  let l := centerPhase * phase v.1.2.2
  obtain ⟨A, ht, hs, hd, he, hk⟩ :=
    PeriodicMPSFiveSiteCoordinates.exists_trace_coordinates 1 0 d e (x 1)
  let B := changePhysical (sectionMatrix s l) A
  have hB := sectionMatrix_invariants A ht hs s l
  have hBp : ((B 1).trace, (B 0).det, (B 1).det, (B 0 * B 1).trace) =
      physicalChart centerPhase v := by
    change _ = SevenSitePhysicalRankBridge.unalign (s, d, l ^ 2 * e, l * (x 1 : ℂ))
    rw [← hd, ← he, ← hk]
    exact hB.2
  have hAp : ((A 1).trace, (A 0).det, (A 1).det, (A 0 * A 1).trace) = sliceOrdinary x := by
    rw [sliceOrdinary, physicalChart_center, hs, hd, he, hk]
  have hl : Complex.normSq l = 1 := by
    change Complex.normSq (centerPhase * phase v.1.2.2) = 1
    rw [Complex.normSq_mul, hPhase, phase_normSq, one_mul]
  rw [← hBp, ordinaryRaw_actual m B hB.1, ← hAp, ordinaryRaw_actual m A ht]
  exact pairGram_sectionMatrix m A s l hl

private theorem hasDerivAt_lengthFactor (m : ℕ) (j : Fin 3) :
    HasDerivAt (fun t => normLine j t ^ (2 * (2 + m))) 0 0 := by
  simpa only [mul_zero] using (hasDerivAt_normLine j).fun_pow (2 * (2 + m))

/-- The two-factor signed Pauli action in the existing X, Y, Z column order. -/
def rotationPolynomial (m : ℕ) (j : Fin 3) (ab : Fin 4 × Fin 4) : MvPolynomial (Fin 5) ℂ :=
  let a := rotationIndex j ab.1
  let b := rotationIndex j ab.2
  (a.1 : MvPolynomial (Fin 5) ℂ) * rawSlicePolynomial m (a.2, ab.2) +
    (b.1 : MvPolynomial (Fin 5) ℂ) * rawSlicePolynomial m (ab.1, b.2)

@[simp] theorem rotationPolynomial_trace (m : ℕ) (j : Fin 3) :
    rotationPolynomial m j (0, 0) = 0 := by
  fin_cases j <;> simp [rotationPolynomial, rotationIndex]

/-- The signed polynomial is the derivative of the literal complex Pauli
contraction on the exact ordinary chart. The identity test gives the raw trace. -/
theorem hasDerivAt_rawPauliMoment_rotation (m : ℕ) (x : SlicePoint) (ab : Fin 4 × Fin 4)
    (j : Fin 3) :
    HasDerivAt (fun t =>
      ((pauliFrame ab.1 ⊗ₖ pauliFrame ab.2) *
        ordinaryRaw m (physicalChart 1 (rotationLine j t, x))).trace)
      (eval (fun k => (x k : ℂ)) (rotationPolynomial m j ab)) 0 := by
  let A := fun t : ℝ => (unitaryLine j t)ᴴ * pauliFrame ab.1 * unitaryLine j t
  let B := fun t : ℝ => (unitaryLine j t)ᴴ * pauliFrame ab.2 * unitaryLine j t
  let M := ordinaryRaw m (sliceOrdinary x)
  have h := (hasDerivAt_lengthFactor m j).fun_mul
    (jet_trace (jet_mul (jet_kron (hasJet_adjointPauli j ab.1)
      (hasJet_adjointPauli j ab.2)) (jet_const M)))
  have he (t : ℝ) :
      complexMoment ab (ordinaryRaw m (physicalChart 1 (rotationLine j t, x))) =
        normLine j t ^ (2 * (2 + m)) * ((A t ⊗ₖ B t) * M).trace := by
    have hc := ordinaryRaw_physicalChart m 1 (by simp) (rotationLine j t, x)
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
      eval (fun k => (x k : ℂ)) (rotationPolynomial m j ab) =
        (((((rotationIndex j ab.1).1 : ℂ) • pauliFrame (rotationIndex j ab.1).2) ⊗ₖ B 0 +
          A 0 ⊗ₖ (((rotationIndex j ab.2).1 : ℂ) • pauliFrame (rotationIndex j ab.2).2)) *
            M).trace := by
    simp only [rotationPolynomial, map_add, map_mul, map_intCast,
      eval_rawSlicePolynomial_eq_moment, M, A, B, unitaryLine_zero, conjTranspose_one,
      one_mul, mul_one, smul_kronecker, kronecker_smul, add_mul, smul_mul_assoc, trace_add,
      trace_smul, smul_eq_mul]
  change HasDerivAt
    (fun t => complexMoment ab (ordinaryRaw m (physicalChart 1 (rotationLine j t, x)))) _ 0
  rw [hd]
  apply HasDerivAt.congr_of_eventuallyEq _ (Filter.Eventually.of_forall he)
  simpa only [normLine_zero, one_pow, one_mul, zero_mul, zero_add, mul_zero, add_zero, A, B]
    using h

private theorem rawReadout_eq_moment (m : ℕ) (p : Ordinary) (i : Fin 10) :
    rawRow i (rawReadout m p) = (complexMoment (observedRow i) (ordinaryRaw m p)).re := by
  rw [rawRow_apply]
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [rawReadout, ordinaryMass, complexMoment, observedRow, pauliFrame]
  · rw [observedRow_succ]
    exact readout_apply _ _

/-- The three rotation directions differentiate the trace and nine actual
Pauli readings in the same row order as the certificate. -/
theorem hasDerivAt_rawReadout_rotation (m : ℕ) (x : SlicePoint) (i : Fin 10) (j : Fin 3) :
    HasDerivAt (fun t =>
      let v := rawReadout m (physicalChart 1 (rotationLine j t, x))
      Fin.cons (α := fun _ => ℝ) v.1 v.2 i)
      (eval (fun k => (x k : ℂ)) (rotationPolynomial m j (observedRow i))).re 0 := by
  have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0
    (hasDerivAt_rawPauliMoment_rotation m x (observedRow i) j)
  change HasDerivAt (fun t =>
    (complexMoment (observedRow i) (ordinaryRaw m (physicalChart 1 (rotationLine j t, x)))).re)
    (eval (fun k => (x k : ℂ)) (rotationPolynomial m j (observedRow i))).re 0 at h
  simpa only [← rawReadout_eq_moment, rawRow_apply] using h

/-- The rotation columns of the full eight-coordinate Fréchet derivative,
in the product codomain used for rank normalization. -/
theorem fderiv_rawReadout_rotationColumn (m : ℕ) (x : SlicePoint) (i : Fin 10) (j : Fin 3) :
    let v := fderiv ℝ (rawReadout m ∘ physicalChart 1) (0, x) (rotationLine j 1, 0)
    Fin.cons (α := fun _ => ℝ) v.1 v.2 i =
      (eval (fun k => (x k : ℂ)) (rotationPolynomial m j (observedRow i))).re := by
  let u : Rotation × SlicePoint := (rotationLine j 1, 0)
  let line : ℝ → Rotation × SlicePoint := fun t => (0, x) + t • u
  have hline : HasDerivAt line u 0 := by
    simpa only [line, Function.comp_def, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.id_apply, one_smul] using
      (((ContinuousLinearMap.id ℝ ℝ).smulRight u).hasFDerivAt.const_add (0, x)).hasDerivAt
  have hraw : Differentiable ℝ (rawReadout m) :=
    (differentiable_ordinaryMass m).prodMk
      (readout.differentiable.comp (differentiable_ordinaryRaw m))
  let F := rawReadout m ∘ physicalChart 1
  have hF : DifferentiableAt ℝ F (0, x) :=
    hraw.differentiableAt.comp (0, x) (analyticAt_physicalChart 1 (0, x)).differentiableAt
  have hFline : HasFDerivAt F (fderiv ℝ F (0, x)) (line 0) := by
    simpa only [line, zero_smul, add_zero] using hF.hasFDerivAt
  have h := (rawRow i).hasFDerivAt.comp_hasDerivAt 0 (hFline.comp_hasDerivAt 0 hline)
  have hrotation (t : ℝ) : t • rotationLine j 1 = rotationLine j t := by
    fin_cases j <;> simp [rotationLine, Prod.smul_mk]
  have hpoint (t : ℝ) : line t = (rotationLine j t, x) := by
    simp [line, u, Prod.smul_mk, Prod.mk_add_mk, hrotation]
  dsimp only
  exact (by
    simpa only [Function.comp_def, F, hpoint, rawRow_apply] using h :
    HasDerivAt (fun t =>
      let v := rawReadout m (physicalChart 1 (rotationLine j t, x))
      Fin.cons (α := fun _ => ℝ) v.1 v.2 i)
      (Fin.cons (α := fun _ => ℝ) (fderiv ℝ F (0, x) u).1 (fderiv ℝ F (0, x) u).2 i) 0).unique
    (hasDerivAt_rawReadout_rotation m x i j)

/-- Complex evaluation of the signed columns at real slice coordinates is
the complexification of their real evaluation. -/
theorem eval_rotationPolynomial_real (m : ℕ) (x : SlicePoint) (j : Fin 3)
    (ab : Fin 4 × Fin 4) :
    ((eval (fun k => (x k : ℂ)) (rotationPolynomial m j ab)).re : ℂ) =
      eval (fun k => (x k : ℂ)) (rotationPolynomial m j ab) := by
  have hvalue (p : Fin 4 × Fin 4) :
      ((eval (fun k => (x k : ℂ)) (rawSlicePolynomial m p)).re : ℂ) =
        eval (fun k => (x k : ℂ)) (rawSlicePolynomial m p) := by
    rw [eval_rawSlicePolynomial_eq_moment]
    exact moment_real p (isHermitian_pairGram (ordinaryAmplitude m (sliceOrdinary x)))
  simp only [rotationPolynomial, map_add, map_mul, map_intCast, Complex.add_re,
    Complex.mul_re, Complex.intCast_re, Complex.intCast_im, zero_mul, sub_zero,
    Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_intCast, hvalue]

/-- At residual length five the signed columns specialize to the existing
seven-site certificate, before taking the real part. -/
theorem eval_rotationPolynomial_five (x : SlicePoint) (j : Fin 3) (ab : Fin 4 × Fin 4) :
    eval (fun k => (x k : ℂ)) (rotationPolynomial 5 j ab) =
      eval (fun k => (x k : ℂ)) (rotationObservation (C Complex.I) X j ab) := by
  have hvalue (p : Fin 4 × Fin 4) :
      eval (fun k => (x k : ℂ)) (rawSlicePolynomial 5 p) =
        eval (fun k => (x k : ℂ)) (V Complex.I p) := by
    rw [eval_rawSlicePolynomial_eq_moment, eval_value_eq_moment]; rfl
  rw [SevenSiteCriticalCertificate.map_rotationObservation, eval_C]
  simp only [rotationPolynomial, map_add, map_mul, map_intCast, hvalue, eval_X,
    rotationObservation, ← SevenSiteCriticalCertificate.eval_value]

#print axioms ordinaryRaw_physicalChart
#print axioms fderiv_rawReadout_rotationColumn
#print axioms eval_rotationPolynomial_five

end

end D5.S3.Quantum.TensorNetworks.UniformNativeRotation
