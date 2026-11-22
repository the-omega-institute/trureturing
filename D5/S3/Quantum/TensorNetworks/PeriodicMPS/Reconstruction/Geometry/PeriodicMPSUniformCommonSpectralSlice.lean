/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformCommonSpectralSlice
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformCommonSpectralSlice
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: The determinant chart and literal witness agree on their slice derivatives. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformCommonSpectralRankTransport
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.UniformNativeSliceReadout

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformCommonSpectralRankTransport

open Matrix MvPolynomial TrivSqZeroExt
open scoped BigOperators Kronecker
open PeriodicMPSCommonSpectralJets (Bits Entry)
open PeriodicMPSUniformSpecialSpectralDomains (witnessK)
open SevenSiteCriticalCertificate (sliceBlock observedRow)
open PeriodicMPSUniformNativeSliceReadout (alignedMoment rawSlicePolynomial)

open private pauli from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteCriticalCertificate
open private alignedWord map_alignedWord map_pauliInsertionCoeff from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.UniformNativeSliceReadout

open private dual fst_dual snd_dual jetEval jetEval_C jetEval_X fst_jetEval from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformCommonSpectralRankTransport

noncomputable section

/-- Embed the five native slice variables in the independent trace blocks. -/
def sliceCoordinates {R : Type*} [CommRing R] (ι : R) (x : Fin 5 → R) :
    Coordinate → R :=
  fun a =>
    let z := sliceBlock ι x (a.1 == 0)
    (![1, 0, z 0, z 2, z 1] : Fin 5 → R) a.2

/-- Complex Cartesian slice point for the real independent-block witness. -/
def nativeWitnessSlice : Fin 5 → ℂ :=
  ![2, (witnessK : ℝ), -1, Complex.I, -Complex.I]

theorem sliceCoordinates_nativeWitnessSlice :
    sliceCoordinates Complex.I nativeWitnessSlice = Complex.ofReal ∘ witnessCoordinates := by
  rw [witnessCoordinates_eq]
  funext i
  rcases i with ⟨b, j⟩
  fin_cases b <;> fin_cases j <;>
    norm_num [sliceCoordinates, sliceBlock, nativeWitnessSlice, Function.comp_apply, ← pow_two,
      Complex.I_sq]

/-- The Pauli contraction on the exact exposed Gram entries, with the
observable evaluated at the transposed matrix index. -/
def pauliGram {R : Type*} [CommRing R] (ι : R) (G : Entry → R) (ab : Fin 4 × Fin 4) : R :=
  ∑ q : Bits, ∑ p : Bits, (pauli ι ab.1 ⊗ₖ pauli ι ab.2) q p * G (p, q)

theorem alignedMoment_eq_pauliGram {R : Type*} [CommRing R] (m : ℕ) (ι : R)
    (x : Fin 5 → R) (ab : Fin 4 × Fin 4) :
    alignedMoment m ι (sliceBlock ι x true) (sliceBlock ι x false) ab =
      pauliGram ι (gramChart m (sliceCoordinates ι x)) ab := by
  unfold alignedMoment pauliGram
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun p _ => ?_
  congr 1

/-- Evaluate the actual native slice polynomial after complexification. -/
theorem eval_rawSlicePolynomial_eq_pauliGram (m : ℕ) (x : Fin 5 → ℂ) (ab : Fin 4 × Fin 4) :
    eval x (rawSlicePolynomial m ab) = pauliGram Complex.I
      (gramChart m (sliceCoordinates Complex.I x)) ab := by
  rw [← alignedMoment_eq_pauliGram]
  let f := eval x
  have h (b : Bool) : f ∘ sliceBlock (C Complex.I) X b = sliceBlock Complex.I x b := by
    funext i
    cases b <;> fin_cases i <;> simp [f, sliceBlock, Function.comp_apply]
  simp only [rawSlicePolynomial, alignedMoment, ← show f = eval _ from rfl,
    map_sum, map_mul, map_pauliInsertionCoeff, map_alignedWord, h, f, eval_C]

theorem eval_rawSlicePolynomial_nativeWitness (m : ℕ) (i : Fin 10) :
    eval nativeWitnessSlice (rawSlicePolynomial m (observedRow i)) =
      pauliGram Complex.I (Complex.ofReal ∘ gramChart m witnessCoordinates) (observedRow i) := by
  rw [eval_rawSlicePolynomial_eq_pauliGram, sliceCoordinates_nativeWitnessSlice]
  have h : gramChart m (Complex.ofReal ∘ witnessCoordinates) =
      Complex.ofReal ∘ gramChart m witnessCoordinates := by
    funext ab
    exact (map_gramChart Complex.ofRealHom m witnessCoordinates ab).symm
  rw [h]

/-- Linear part of the affine embedding `sliceCoordinates`. -/
def sliceDirection {R : Type*} [CommRing R] (ι : R) (v : Fin 5 → R) :
    Coordinate → R :=
  fun a =>
    let z := sliceBlock ι v (a.1 == 0)
    (![0, 0, z 0, z 2, z 1] : Fin 5 → R) a.2

private theorem sliceCoordinates_jet (x v : Fin 5 → ℂ) :
    sliceCoordinates (inlHom ℂ ℂ Complex.I) (fun i => dual (x i) (v i)) =
      fun a => dual (sliceCoordinates Complex.I x a) (sliceDirection Complex.I v a) := by
  funext a
  rcases a with ⟨b, j⟩
  fin_cases b <;> fin_cases j <;> apply TrivSqZeroExt.ext <;>
    simp [sliceCoordinates, sliceDirection, sliceBlock]

private theorem jetEval_rawSlicePolynomial (m : ℕ) (x v : Fin 5 → ℂ)
    (ab : Fin 4 × Fin 4) :
    jetEval x v (rawSlicePolynomial m ab) =
      pauliGram (inlHom ℂ ℂ Complex.I)
        (gramChart m (fun a => dual (sliceCoordinates Complex.I x a)
          (sliceDirection Complex.I v a))) ab := by
  rw [← sliceCoordinates_jet, ← alignedMoment_eq_pauliGram]
  let f := jetEval x v
  have h (b : Bool) : f ∘ sliceBlock (C Complex.I) X b =
      sliceBlock (inlHom ℂ ℂ Complex.I) (fun i => dual (x i) (v i)) b := by
    funext i
    cases b <;> fin_cases i <;> simp [f, sliceBlock, Function.comp_apply]
  change f (rawSlicePolynomial m ab) = _
  simp only [rawSlicePolynomial, alignedMoment, map_sum, map_mul, map_pauliInsertionCoeff,
    map_alignedWord, h, f, jetEval_C]

private theorem snd_pauliGram (m : ℕ) (x v : Coordinate → ℂ) (ab : Fin 4 × Fin 4) :
    (pauliGram (inlHom ℂ ℂ Complex.I)
      (gramChart m (fun a => dual (x a) (v a))) ab).snd =
        pauliGram Complex.I (gramDifferential m x v) ab := by
  simp only [pauliGram, snd_sum]
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun p _ => ?_
  rw [← map_pauliInsertionCoeff (inlHom ℂ ℂ) Complex.I ab p q]
  simp only [DualNumber.snd_mul, inlHom_apply, fst_inl, snd_inl, zero_mul, add_zero,
    gramDifferential_apply]

private theorem snd_jetEval_single (p : MvPolynomial (Fin 5) ℂ) (x : Fin 5 → ℂ) (j : Fin 5) :
    (jetEval x (Pi.single j 1) p).snd = eval x (pderiv j p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    rw [pderiv_mul]
    by_cases hi : i = j
    · subst i
      simp [hp, fst_jetEval, mul_comm, add_comm]
    · simp [hp, fst_jetEval, pderiv_X_of_ne hi, Pi.single_eq_of_ne hi, mul_comm]

/-- The five native slice partials are actual invariant Gram derivatives
followed by the native Pauli contraction. -/
theorem eval_pderiv_rawSlicePolynomial (m : ℕ) (x : Fin 5 → ℂ) (j : Fin 5)
    (ab : Fin 4 × Fin 4) :
    eval x (pderiv j (rawSlicePolynomial m ab)) =
      pauliGram Complex.I (gramDifferential m (sliceCoordinates Complex.I x)
        (sliceDirection Complex.I (Pi.single j 1))) ab := by
  rw [← snd_jetEval_single, jetEval_rawSlicePolynomial, snd_pauliGram]

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformCommonSpectralRankTransport
