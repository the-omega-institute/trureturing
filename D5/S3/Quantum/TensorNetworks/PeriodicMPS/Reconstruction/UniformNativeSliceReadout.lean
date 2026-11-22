/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/UniformNativeSliceReadout
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/UniformNativeSliceReadout
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: Raw Pauli readouts on the uniform physical slice. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformNativeTransferReadout
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSitePhysicalRankBridge
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.UniformRankNormalization

/-!
# Raw Pauli readouts on the uniform physical slice

The two trace blocks use independent determinant coordinates until the physical
specialization. The Pauli insertion is linear in the residual transfer power.
On the physical slice the raw trace and nine Pauli rows are polynomial in the
five real slice coordinates, so their actual directional derivatives are
given by the corresponding polynomial partials.
-/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformNativeSliceReadout

open Matrix MvPolynomial
open scoped BigOperators Matrix Kronecker Matrix.Norms.Elementwise
open PeriodicMPSUniformAntisymmetricTransfer
  (BondMatrix TransferMatrix mixedTransfer mixedRaw conjugateCore)
open PeriodicMPSUniformHardCoreTransferRecurrence (TwoBits binaryInsertion)
open PeriodicMPSUniformNativeTransferReadout
  (mixedTransfer_pow_eq_sum_wordProducts pairGram_traceWord_eq_mixedRaw)
open SevenSiteTraceBase (Word wordPolynomial wordProduct wordPolynomial_eq_trace)
open private form map_form from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteTraceBase
open SevenSitePhysicalRankBridge
  (Rotation SlicePoint physicalChart sliceOrdinary physicalChart_center analyticAt_physicalChart)
open SevenSiteCriticalCertificate (observedRow sliceBlock)
open SevenSiteReadoutDerivative (observedRow_succ)
open PeriodicMPSCompactReadout (Readout readout readout_apply)
open UniformRankNormalization (ordinaryAmplitude ordinaryRaw ordinaryMass rawReadout)
open PeriodicMPSFiveSiteCoordinates (exists_trace_coordinates)
open UniformMPSExpectedDimensionRefutation (traceWord)

open private pauli map_pauli from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteCriticalCertificate
open private pauliFrame from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reflection.TwoQubitMarginalReflection
open private certificate_pauli from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteReadoutDerivative
open private hasDerivAt_eval_slice_line from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSitePhysicalRankBridge
open private differentiable_ordinaryMass differentiable_ordinaryRaw from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.UniformRankNormalization

noncomputable section

variable {R : Type*} [CommRing R]

/-- Trace-aligned word with invariant order `(d, k, e)`. -/
private def alignedWord (z : Fin 3 → R) {n : ℕ} (w : Word n) : R :=
  wordPolynomial 1 0 (z 0) (z 2) (z 1) (List.ofFn w)

private theorem map_alignedWord {S : Type*} [CommRing S] (f : R →+* S)
    (z : Fin 3 → R) {n : ℕ} (w : Word n) :
    f (alignedWord z w) = alignedWord (f ∘ z) w := by
  unfold alignedWord wordPolynomial
  simp only [Function.comp_apply, ← map_one f, ← map_zero f, map_form]
  rcases form (1 : R) 0 (z 0) (z 2) (z 1) (List.ofFn w) with ⟨u, a, b, c⟩
  simp [map_ofNat]

/-- The adjacent Pauli contraction with independent ket and bra invariants. -/
def alignedMoment (m : ℕ) (ι : R) (ket bra : Fin 3 → R) (ab : Fin 4 × Fin 4) : R :=
  ∑ q : TwoBits, ∑ p : TwoBits,
    (pauli ι ab.1 ⊗ₖ pauli ι ab.2) q p *
      (∑ w : Word m, alignedWord ket (Fin.append ![p.1, p.2] w) *
        alignedWord bra (Fin.append ![q.1, q.2] w))

/-- The Pauli coefficient of entry `(p,q)` is the observable entry
`(q,p)`. The transfer itself is in bra-first order. -/
def pauliInsertion (ι : R) (ket bra : Fin 2 → BondMatrix R)
    (ab : Fin 4 × Fin 4) : TransferMatrix R :=
  ∑ q : TwoBits, ∑ p : TwoBits,
    (pauli ι ab.1 ⊗ₖ pauli ι ab.2) q p • binaryInsertion bra ket q p

private theorem wordProduct_prefix (A : Fin 2 → BondMatrix R) (p : TwoBits)
    {m : ℕ} (w : Word m) :
    wordProduct A (Fin.append ![p.1, p.2] w) = A p.1 * A p.2 * wordProduct A w := by
  unfold wordProduct
  rw [List.ofFn_comp' (Fin.append ![p.1, p.2] w) A, List.ofFn_fin_append,
    List.map_append, List.prod_append, List.map_ofFn]
  simp [List.ofFn_succ, Function.comp_def]

/-- In the aligned invariants of any independently realized ket and bra,
each raw Pauli contraction is the trace of its insertion times the residual
mixed transfer power. -/
theorem alignedMoment_eq_transferPower (m : ℕ) (ι : R)
    (ket bra : Fin 2 → BondMatrix R) (hk0 : (ket 0).trace = 1) (hk1 : (ket 1).trace = 0)
    (hb0 : (bra 0).trace = 1) (hb1 : (bra 1).trace = 0) (ab : Fin 4 × Fin 4) :
    alignedMoment m ι ![(ket 0).det, (ket 0 * ket 1).trace, (ket 1).det]
      ![(bra 0).det, (bra 0 * bra 1).trace, (bra 1).det] ab =
      (pauliInsertion ι ket bra ab * mixedTransfer ket bra ^ m).trace := by
  have entry (p q : TwoBits) :
      (∑ w : Word m,
        alignedWord ![(ket 0).det, (ket 0 * ket 1).trace, (ket 1).det]
            (Fin.append ![p.1, p.2] w) *
          alignedWord ![(bra 0).det, (bra 0 * bra 1).trace, (bra 1).det]
            (Fin.append ![q.1, q.2] w)) = mixedRaw ket bra m p q := by
    change _ = (binaryInsertion bra ket q p * mixedTransfer ket bra ^ m).trace
    rw [mixedTransfer_pow_eq_sum_wordProducts, Matrix.mul_sum, Matrix.trace_sum]
    apply Finset.sum_congr rfl
    intro w _
    have hket := wordPolynomial_eq_trace ket (Fin.append ![p.1, p.2] w)
    have hbra := wordPolynomial_eq_trace bra (Fin.append ![q.1, q.2] w)
    rw [hk0, hk1, wordProduct_prefix] at hket
    rw [hb0, hb1, wordProduct_prefix] at hbra
    change wordPolynomial 1 0 (ket 0).det (ket 1).det (ket 0 * ket 1).trace
        (List.ofFn (Fin.append ![p.1, p.2] w)) *
      wordPolynomial 1 0 (bra 0).det (bra 1).det (bra 0 * bra 1).trace
        (List.ofFn (Fin.append ![q.1, q.2] w)) =
      (binaryInsertion bra ket q p * (wordProduct bra w ⊗ₖ wordProduct ket w)).trace
    rw [hket, hbra, binaryInsertion, ← Matrix.mul_kronecker_mul, Matrix.trace_kronecker]
    exact mul_comm _ _
  simp only [alignedMoment, entry, mixedRaw, pauliInsertion, Finset.sum_mul,
    Matrix.trace_sum, smul_mul_assoc, Matrix.trace_smul, smul_eq_mul]

private theorem trace_pauli_mul_mixedRaw (m : ℕ) (ι : R)
    (ket bra : Fin 2 → BondMatrix R) (ab : Fin 4 × Fin 4) :
    ((pauli ι ab.1 ⊗ₖ pauli ι ab.2) * mixedRaw ket bra m).trace =
      (pauliInsertion ι ket bra ab * mixedTransfer ket bra ^ m).trace := by
  conv_rhs =>
    simp only [pauliInsertion, Finset.sum_mul, Matrix.trace_sum, smul_mul_assoc,
      Matrix.trace_smul, smul_eq_mul]
  rfl

private theorem map_pauliInsertionCoeff {S : Type*} [CommRing S] (f : R →+* S)
    (ι : R) (ab : Fin 4 × Fin 4) (p q : TwoBits) :
    f ((pauli ι ab.1 ⊗ₖ pauli ι ab.2) q p) =
      (pauli (f ι) ab.1 ⊗ₖ pauli (f ι) ab.2) q p := by
  simp only [Matrix.kroneckerMap_apply, map_mul, map_pauli]

/-- Polynomial on the real slice in order `(Re d, k, Re e, Im d, Im e)`.
The index pair `(0,0)` is the raw trace. -/
def rawSlicePolynomial (m : ℕ) (ab : Fin 4 × Fin 4) : MvPolynomial (Fin 5) ℂ :=
  alignedMoment m (C Complex.I) (sliceBlock (C Complex.I) X true)
    (sliceBlock (C Complex.I) X false) ab

private theorem eval_rawSlicePolynomial (m : ℕ) (x : SlicePoint) (ab : Fin 4 × Fin 4) :
    eval (fun j => (x j : ℂ)) (rawSlicePolynomial m ab) =
      alignedMoment m Complex.I (sliceBlock Complex.I (fun j => (x j : ℂ)) true)
        (sliceBlock Complex.I (fun j => (x j : ℂ)) false) ab := by
  let f := eval (fun j => (x j : ℂ))
  have h (b : Bool) :
      f ∘ sliceBlock (C Complex.I) X b = sliceBlock Complex.I (fun j => (x j : ℂ)) b := by
    funext i
    cases b <;> fin_cases i <;> simp [f, sliceBlock, Function.comp_apply]
  simp only [rawSlicePolynomial, alignedMoment, ← show f = eval _ from rfl,
    map_sum, map_mul, map_pauliInsertionCoeff, map_alignedWord, h, f, eval_C]

/-- Exact evaluation of every slice Pauli polynomial by the mixed transfer
power. The five real arguments specialize the bra invariants by conjugation. -/
theorem eval_rawSlicePolynomial_eq_transferPower (m : ℕ) (x : SlicePoint)
    (A : Fin 2 → BondMatrix ℂ) (ht : (A 0).trace = 1) (hs : (A 1).trace = 0)
    (hd : (A 0).det = (x 0 : ℂ) + Complex.I * (x 3 : ℂ))
    (he : (A 1).det = (x 2 : ℂ) + Complex.I * (x 4 : ℂ))
    (hk : (A 0 * A 1).trace = (x 1 : ℂ)) (ab : Fin 4 × Fin 4) :
    eval (fun j => (x j : ℂ)) (rawSlicePolynomial m ab) =
      (pauliInsertion Complex.I A (conjugateCore A) ab *
        mixedTransfer A (conjugateCore A) ^ m).trace := by
  let f := starRingEnd ℂ
  have htrace (M : BondMatrix ℂ) : (f.mapMatrix M).trace = f M.trace :=
    (AddMonoidHom.map_trace f M).symm
  have hdet (M : BondMatrix ℂ) : (f.mapMatrix M).det = f M.det :=
    (RingHom.map_det f M).symm
  have hb0 : (conjugateCore A 0).trace = 1 := by
    change (f.mapMatrix (A 0)).trace = _
    rw [htrace, ht, map_one]
  have hb1 : (conjugateCore A 1).trace = 0 := by
    change (f.mapMatrix (A 1)).trace = _
    rw [htrace, hs, map_zero]
  have hket : sliceBlock Complex.I (fun j => (x j : ℂ)) true =
      ![(A 0).det, (A 0 * A 1).trace, (A 1).det] := by
    simp [sliceBlock, hd, he, hk]
  have hbra : sliceBlock Complex.I (fun j => (x j : ℂ)) false =
      ![(conjugateCore A 0).det, (conjugateCore A 0 * conjugateCore A 1).trace,
        (conjugateCore A 1).det] := by
    change _ = ![(f.mapMatrix (A 0)).det, (f.mapMatrix (A 0) * f.mapMatrix (A 1)).trace,
      (f.mapMatrix (A 1)).det]
    rw [← map_mul, htrace, hdet, hdet, hd, he, hk]
    simp [f, sliceBlock]
  rw [eval_rawSlicePolynomial, hket, hbra, alignedMoment_eq_transferPower m _ A _ ht hs hb0 hb1]

private theorem ordinaryRaw_slice_eq_mixedRaw (m : ℕ) (x : SlicePoint)
    (A : Fin 2 → BondMatrix ℂ) (ht : (A 0).trace = 1) (hs : (A 1).trace = 0)
    (hd : (A 0).det = (x 0 : ℂ) + Complex.I * (x 3 : ℂ))
    (he : (A 1).det = (x 2 : ℂ) + Complex.I * (x 4 : ℂ))
    (hk : (A 0 * A 1).trace = (x 1 : ℂ)) :
    ordinaryRaw m (sliceOrdinary x) = mixedRaw A (conjugateCore A) m := by
  have hA : ordinaryAmplitude m (sliceOrdinary x) = traceWord 2 2 (2 + m) A := by
    have hcoord : sliceOrdinary x = ((A 1).trace, (A 0).det, (A 1).det, (A 0 * A 1).trace) := by
      rw [sliceOrdinary, physicalChart_center, hs, hd, he, hk]
    funext w
    simpa only [hcoord, ordinaryAmplitude, ht, wordProduct, traceWord] using wordPolynomial_eq_trace A w
  rw [ordinaryRaw, hA, pairGram_traceWord_eq_mixedRaw]

/-- At each physical slice point, the polynomial gives the literal
expectation against the unnormalized adjacent marginal. -/
theorem eval_rawSlicePolynomial_eq_moment (m : ℕ) (x : SlicePoint) (ab : Fin 4 × Fin 4) :
    eval (fun j => (x j : ℂ)) (rawSlicePolynomial m ab) =
      ((pauliFrame ab.1 ⊗ₖ pauliFrame ab.2) * ordinaryRaw m (sliceOrdinary x)).trace := by
  obtain ⟨A, ht, hs, hd, he, hk⟩ := exists_trace_coordinates 1 0
    ((x 0 : ℂ) + Complex.I * (x 3 : ℂ)) ((x 2 : ℂ) + Complex.I * (x 4 : ℂ)) (x 1)
  rw [eval_rawSlicePolynomial_eq_transferPower m x A ht hs hd he hk,
    ordinaryRaw_slice_eq_mixedRaw m x A ht hs hd he hk,
    ← trace_pauli_mul_mixedRaw, certificate_pauli, certificate_pauli]

/-- In the trace row, the Pauli insertion contracts to two more transfer steps. -/
theorem eval_rawTrace_eq_transferPower (m : ℕ) (x : SlicePoint)
    (A : Fin 2 → BondMatrix ℂ) (ht : (A 0).trace = 1) (hs : (A 1).trace = 0)
    (hd : (A 0).det = (x 0 : ℂ) + Complex.I * (x 3 : ℂ))
    (he : (A 1).det = (x 2 : ℂ) + Complex.I * (x 4 : ℂ))
    (hk : (A 0 * A 1).trace = (x 1 : ℂ)) :
    eval (fun j => (x j : ℂ)) (rawSlicePolynomial m (0, 0)) =
      (mixedTransfer A (conjugateCore A) ^ (2 + m)).trace := by
  rw [eval_rawSlicePolynomial_eq_moment, ordinaryRaw_slice_eq_mixedRaw m x A ht hs hd he hk,
    show pauliFrame 0 = 1 from rfl, one_kronecker_one, Matrix.one_mul,
    PeriodicMPSUniformAntisymmetricTransfer.mixedRaw_trace, Nat.add_comm m 2]

/-- The value column of the augmented physical readout in certificate row order. -/
theorem rawReadout_slice_eq_eval (m : ℕ) (x : SlicePoint) (i : Fin 10) :
    Fin.cons (α := fun _ => ℝ) (rawReadout m (sliceOrdinary x)).1
      (rawReadout m (sliceOrdinary x)).2 i =
      (eval (fun j => (x j : ℂ)) (rawSlicePolynomial m (observedRow i))).re := by
  rw [eval_rawSlicePolynomial_eq_moment]
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [rawReadout, ordinaryMass, observedRow, pauliFrame]
  · rw [observedRow_succ]
    exact readout_apply _ _

/-- The five real slice columns are the actual derivatives of the augmented
physical readout. This identity works at every residual length. -/
theorem hasDerivAt_rawReadout_slice (m : ℕ) (x : SlicePoint) (i : Fin 10) (j : Fin 5) :
    HasDerivAt (fun t : ℝ =>
      let v := rawReadout m (sliceOrdinary (x + t • Pi.single j 1))
      Fin.cons (α := fun _ => ℝ) v.1 v.2 i)
      (eval (fun k => (x k : ℂ)) (pderiv j (rawSlicePolynomial m (observedRow i)))).re 0 := by
  simpa only [Function.comp_def, Complex.reCLM_apply, rawReadout_slice_eq_eval] using
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0
      (hasDerivAt_eval_slice_line (rawSlicePolynomial m (observedRow i)) x j)

private def rawRow (i : Fin 10) : (ℝ × Readout) →L[ℝ] ℝ :=
  Fin.cases (ContinuousLinearMap.fst ℝ ℝ Readout)
    (fun j => (ContinuousLinearMap.proj j).comp (ContinuousLinearMap.snd ℝ ℝ Readout)) i

private theorem rawRow_apply (i : Fin 10) (v : ℝ × Readout) :
    rawRow i v = Fin.cons (α := fun _ => ℝ) v.1 v.2 i :=
  Fin.cases rfl (fun _ => rfl) i

/-- The slice columns of the full physical chart differential, in the
same product codomain as the raw rank-normalization theorem. -/
theorem fderiv_rawReadout_sliceColumn (m : ℕ) (x : SlicePoint) (i : Fin 10) (j : Fin 5) :
    let v := fderiv ℝ (rawReadout m ∘ physicalChart 1) (0, x) (0, Pi.single j 1)
    Fin.cons (α := fun _ => ℝ) v.1 v.2 i =
      (eval (fun k => (x k : ℂ)) (pderiv j (rawSlicePolynomial m (observedRow i)))).re := by
  let u : Rotation × SlicePoint := (0, Pi.single j 1)
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
  have hpoint (t : ℝ) : line t = (0, x + t • Pi.single j 1) := by
    simp [line, u, Prod.smul_mk, Prod.mk_add_mk]
  dsimp only
  exact (by
    simpa only [Function.comp_def, F, hpoint, sliceOrdinary, rawRow_apply] using h :
    HasDerivAt (fun t : ℝ =>
      let v := rawReadout m (sliceOrdinary (x + t • Pi.single j 1))
      Fin.cons (α := fun _ => ℝ) v.1 v.2 i)
      (Fin.cons (α := fun _ => ℝ) (fderiv ℝ F (0, x) u).1 (fderiv ℝ F (0, x) u).2 i) 0).unique
    (hasDerivAt_rawReadout_slice m x i j)

#print axioms alignedMoment_eq_transferPower
#print axioms eval_rawTrace_eq_transferPower
#print axioms fderiv_rawReadout_sliceColumn

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformNativeSliceReadout
