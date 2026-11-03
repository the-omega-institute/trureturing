/- GID: D5/S3/Quantum/Information/ProductMarginZhangYeung
   generality: G
   mirror-B: D5/B/S3/Quantum/Information/ProductMarginZhangYeung
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual density and spectral information of the equal-spectrum product-margin family. -/

import D5.S3.Quantum.Information.ProductMarginQubitOrder
import D5.S3.Quantum.Information.QubitEntropyContraction
import D5.S3.Quantum.Information.ProductMarginEntropyCertificate
import D5.S3.Quantum.Information.OrthogonalRecordEntropy
import D5.S3.Quantum.Divergence.CanonicalProductRecovery
import D5.S3.Quantum.Divergence.CanonicalChannelDPI
import D5.S3.Quantum.Foundation.FinitePreparationChannel

/-! Actual product-margin density matrices and their spectral entropy ports. -/

noncomputable section
namespace D5.S3.Quantum.Information.ProductMarginZhangYeung
open _root_.Matrix
open scoped ComplexOrder MatrixOrder Kronecker
open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
open D5.S3.Quantum.Divergence.VonNeumannEntropyPinching
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Information.OrthogonalRecordEntropy
open D5.S3.Quantum.Information.QubitNormalFormState
open D5.S3.Quantum.Divergence.LegacyRelativeEntropyBoundary
open D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy

private theorem mutual_information_relative_entropy
    {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (rho : DensityState (a × b))
    (hA : (CStarMatrix.ofMatrix.symm (marginalRight rho).1).PosDef)
    (hB : (CStarMatrix.ofMatrix.symm (marginalLeft rho).1).PosDef) :
    extendedQuantumRelativeEntropy (fromLegacyDensityState rho)
      (fromLegacyDensityState (productState (marginalRight rho) (marginalLeft rho))) =
      (quantumMutualInformation rho : WithTop ℝ) := by
  have h := D5.S3.Quantum.Divergence.CanonicalProductRecovery.canonical_product_recovery_chain
    (fromLegacyDensityState rho) (fromLegacyDensityState (marginalRight rho))
    (fromLegacyDensityState (marginalLeft rho)) hA hB
  dsimp only at h
  rcases h with ⟨hs, _, _, _, _, _, _, hf⟩
  have hfin : finiteTraceLogRelativeEntropy (fromLegacyDensityState rho)
      (fromLegacyDensityState (productState (marginalRight rho) (marginalLeft rho))) =
      quantumMutualInformation rho := by
    simpa only [toLegacy_fromLegacy_densityState, finiteTraceLogRelativeEntropy_self,
      add_zero] using hf
  rw [extendedQuantumRelativeEntropy_eq_coe_of_support (by
    simpa only [toLegacy_fromLegacy_densityState] using hs), hfin]

private theorem mutual_information_dpi
    {a b c d : Type*} [Fintype a] [DecidableEq a] [Nonempty a]
    [Fintype b] [DecidableEq b] [Nonempty b]
    [Fintype c] [DecidableEq c] [Nonempty c]
    [Fintype d] [DecidableEq d] [Nonempty d]
    (rho : DensityState (a × b)) (sigma : DensityState (c × d))
    (channel : D5.S3.Quantum.Foundation.FiniteStateChannel.QuantumChannel (a × b) (c × d))
    (hrhoA : (CStarMatrix.ofMatrix.symm (marginalRight rho).1).PosDef)
    (hrhoB : (CStarMatrix.ofMatrix.symm (marginalLeft rho).1).PosDef)
    (hsigmaA : (CStarMatrix.ofMatrix.symm (marginalRight sigma).1).PosDef)
    (hsigmaB : (CStarMatrix.ofMatrix.symm (marginalLeft sigma).1).PosDef)
    (hstate : channel.mapState (fromLegacyDensityState rho) = fromLegacyDensityState sigma)
    (hproduct : channel.mapState
      (fromLegacyDensityState (productState (marginalRight rho) (marginalLeft rho))) =
      fromLegacyDensityState (productState (marginalRight sigma) (marginalLeft sigma))) :
    quantumMutualInformation sigma ≤ quantumMutualInformation rho := by
  have h := D5.S3.Quantum.Divergence.CanonicalChannelDPI.extended_quantum_relative_entropy_channel_dpi
    channel (fromLegacyDensityState rho)
    (fromLegacyDensityState (productState (marginalRight rho) (marginalLeft rho)))
  rw [hstate, hproduct, mutual_information_relative_entropy sigma hsigmaA hsigmaB,
    mutual_information_relative_entropy rho hrhoA hrhoB] at h
  exact WithTop.coe_le_coe.mp h

abbrev Bit := Fin 2
abbrev CD := Bit × Bit
abbrev AB := Bit × Bit

/-- Independent local parameters range over the entire closed first-quadrant disk. -/
structure LocalPair where
  x : ℝ
  z : ℝ
  x_nonneg : 0 ≤ x
  z_nonneg : 0 ≤ z
  disk : x ^ 2 + z ^ 2 ≤ 1

def LocalPair.plus (c : LocalPair) : DensityState Bit := qubitState c.x c.z c.disk
def LocalPair.minus (c : LocalPair) : DensityState Bit :=
  qubitState c.x (-c.z) (by nlinarith [c.disk])
def LocalPair.average (c : LocalPair) : DensityState Bit :=
  qubitState c.x 0 (by nlinarith [c.disk, sq_nonneg c.z])

def positiveMargin (c d : LocalPair) : DensityState CD := productState c.plus d.plus
def negativeMargin (c d : LocalPair) : DensityState CD := productState c.minus d.minus

/-- No commutation, real-entry or rank constraint is imposed on the common lower matrix. -/
structure Coupling (c d : LocalPair) where
  K : Matrix CD CD ℂ
  positive : K.PosSemidef
  le_positive : K ≤ CStarMatrix.ofMatrix.symm (positiveMargin c d).1
  le_negative : K ≤ CStarMatrix.ofMatrix.symm (negativeMargin c d).1

def block {c d : LocalPair} (k : Coupling c d) (ab : AB) : Matrix CD CD ℂ :=
  (1 / 2 : ℝ) • if ab.1 = 0 then
    if ab.2 = 0 then CStarMatrix.ofMatrix.symm (positiveMargin c d).1 - k.K else k.K
  else if ab.2 = 0 then k.K else CStarMatrix.ofMatrix.symm (negativeMargin c d).1 - k.K

private theorem block_positive {c d : LocalPair} (k : Coupling c d) (ab : AB) :
    (block k ab).PosSemidef := by
  unfold block
  apply Matrix.PosSemidef.smul _ (by norm_num : (0 : ℝ) ≤ 1 / 2)
  split_ifs
  · exact Matrix.le_iff.mp k.le_positive
  · exact k.positive
  · exact k.positive
  · exact Matrix.le_iff.mp k.le_negative

/-- The original four blocks, placed on the two classical pointer registers. -/
def actualMatrix {c d : LocalPair} (k : Coupling c d) : Matrix (AB × CD) (AB × CD) ℂ :=
  ∑ ab : AB, CStarMatrix.ofMatrix.symm (pointerState ab).1 ⊗ₖ block k ab

private theorem actual_positive {c d : LocalPair} (k : Coupling c d) :
    (actualMatrix k).PosSemidef :=
  Matrix.posSemidef_sum _ (fun ab _ => (density_posSemidef (pointerState ab)).kronecker
    (block_positive k ab))

private theorem actual_trace {c d : LocalPair} (k : Coupling c d) :
    (actualMatrix k).trace = 1 := by
  simp only [actualMatrix, Matrix.trace_sum, Matrix.trace_kronecker]
  have ht (ab : AB) : (CStarMatrix.ofMatrix.symm (pointerState ab).1).trace = 1 :=
    (pointerState ab).2.2
  simp only [ht, one_mul, Fintype.sum_prod_type, Fin.sum_univ_two, block,
    Matrix.trace_smul, Matrix.trace_sub]
  norm_num only [Fin.isValue, Prod.fst, Prod.snd, ↓reduceIte, one_ne_zero,
    (positiveMargin c d).2.2, (negativeMargin c d).2.2]
  have hp : (CStarMatrix.ofMatrix.symm (positiveMargin c d).1).trace = 1 :=
    (positiveMargin c d).2.2
  have hq : (CStarMatrix.ofMatrix.symm (negativeMargin c d).1).trace = 1 :=
    (negativeMargin c d).2.2
  simp only [Matrix.trace_sub, hp, hq, Complex.real_smul,
    Complex.ofReal_div, Complex.ofReal_one]
  norm_num
  <;> ring

/-- An actual sixteen-dimensional density state, including zero and singular blocks. -/
def actualState {c d : LocalPair} (k : Coupling c d) : DensityState (AB × CD) :=
  ⟨CStarMatrix.ofMatrix (actualMatrix k),
    map_nonneg CStarMatrix.ofMatrixStarAlgEquiv (actual_positive k).nonneg, actual_trace k⟩

private theorem actual_entry {c d : LocalPair} (k : Coupling c d) (a b : AB) (i j : CD) :
    actualMatrix k (a,i) (b,j) = if a = b then block k a i j else 0 := by
  simp [actualMatrix, pointerState, productState, Matrix.sum_apply,
    Matrix.kronecker_apply, Matrix.diagonal_apply, ite_mul]

/-- The physical CD marginal is the average of the two product margins. -/
def productMixture (c d : LocalPair) : DensityState CD :=
  mixtureState (fun _ : Bit => (1 / 2 : ℝ)) (by intro; norm_num)
    (by norm_num [Fin.sum_univ_two])
    (fun b => if b = 0 then positiveMargin c d else negativeMargin c d)

private theorem actual_cd {c d : LocalPair} (k : Coupling c d) :
    marginalLeft (actualState k) = productMixture c d := by
  apply Subtype.ext
  change CStarMatrix.ofMatrix (partialTraceLeft (actualMatrix k)) = _
  apply congrArg CStarMatrix.ofMatrix
  ext i j
  simp only [partialTraceLeft, actual_entry, ↓reduceIte, Fintype.sum_prod_type,
    Fin.sum_univ_two, productMixture, mixtureState, Matrix.sum_apply]
  simp [block, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  <;> ring

private theorem trace_coupling_range {c d : LocalPair} (k : Coupling c d) :
    0 ≤ k.K.trace.re ∧ k.K.trace.re ≤ 1 := by
  refine ⟨(Complex.nonneg_iff.mp k.positive.trace_nonneg).1, ?_⟩
  have ht := (Complex.nonneg_iff.mp (Matrix.le_iff.mp k.le_positive).trace_nonneg).1
  have hp : (CStarMatrix.ofMatrix.symm (positiveMargin c d).1).trace = 1 :=
    (positiveMargin c d).2.2
  rw [Matrix.trace_sub, hp, Complex.sub_re] at ht
  norm_num at ht
  linarith

private def reindexState {a b : Type*} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] (e : b ≃ a) (rho : DensityState a) : DensityState b := by
  refine ⟨CStarMatrix.ofMatrix ((CStarMatrix.ofMatrix.symm rho.1).submatrix e e),
    map_nonneg CStarMatrix.ofMatrixStarAlgEquiv ((density_posSemidef rho).submatrix e).nonneg, ?_⟩
  change (∑ i : b, CStarMatrix.ofMatrix.symm rho.1 (e i) (e i)) = 1
  exact (e.sum_comp (fun i => CStarMatrix.ofMatrix.symm rho.1 i i)).trans rho.2.2

private theorem entropy_reindex {a b : Type*} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] (e : b ≃ a) (rho : DensityState a) :
    vonNeumannEntropy (reindexState e rho) = vonNeumannEntropy rho := by
  rw [InputInformationBalance.entropy_eq_sum, InputInformationBalance.entropy_eq_sum]
  let M := CStarMatrix.ofMatrix.symm rho.1
  let hM := (density_posSemidef rho).isHermitian
  have hc : (M.submatrix e e).charpoly =
      ∏ i : b, (Polynomial.X - Polynomial.C ((hM.eigenvalues (e i) : ℝ) : ℂ)) := by
    change (Matrix.reindex e.symm e.symm M).charpoly = _
    rw [Matrix.charpoly_reindex, hM.charpoly_eq, ← e.prod_comp]
    rfl
  change (∑ i : b, Real.negMulLog (((density_posSemidef rho).submatrix e).1.eigenvalues i)) =
    ∑ i : a, Real.negMulLog (hM.eigenvalues i)
  rw [spectral_sum_eq_of_charpoly_prod _ (fun i => hM.eigenvalues (e i)) Real.negMulLog hc]
  exact e.sum_comp (fun i => Real.negMulLog (hM.eigenvalues i))

private theorem mutual_information_swap {a b : Type*} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] (rho : DensityState (a × b)) :
    quantumMutualInformation (reindexState (Equiv.prodComm b a) rho) =
      quantumMutualInformation rho := by
  have hr : marginalRight (reindexState (Equiv.prodComm b a) rho) = marginalLeft rho := by
    apply Subtype.ext
    rfl
  have hl : marginalLeft (reindexState (Equiv.prodComm b a) rho) = marginalRight rho := by
    apply Subtype.ext
    rfl
  simp only [quantumMutualInformation, hr, hl, entropy_reindex]
  ring

private def rowEquiv : ((Bit × CD) × Bit) ≃ (AB × CD) where
  toFun p := ((p.1.1, p.2), p.1.2)
  invFun p := ((p.1.1, p.2), p.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

private def columnEquiv : ((Bit × CD) × Bit) ≃ (AB × CD) where
  toFun p := ((p.2, p.1.1), p.1.2)
  invFun p := ((p.1.2, p.2), p.1.1)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Trace out B from the actual ABCD density. -/
def actualACD {c d : LocalPair} (k : Coupling c d) : DensityState (Bit × CD) :=
  marginalRight (reindexState rowEquiv (actualState k))
/-- Trace out A from the actual ABCD density. -/
def actualBCD {c d : LocalPair} (k : Coupling c d) : DensityState (Bit × CD) :=
  marginalRight (reindexState columnEquiv (actualState k))

def rowMixture (c d : LocalPair) : DensityState (Bit × CD) :=
  recordState (fun _ : Bit => (1 / 2 : ℝ)) (by intro; norm_num)
    (by norm_num [Fin.sum_univ_two])
    (fun b => if b = 0 then positiveMargin c d else negativeMargin c d)

private theorem record_entry {a b : Type*} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] (p : a → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    (rho : a → DensityState b) (i j : a) (r t : b) :
    CStarMatrix.ofMatrix.symm (recordState p hp hs rho).1 (i,r) (j,t) =
      if i = j then (p i : ℂ) * CStarMatrix.ofMatrix.symm (rho i).1 r t else 0 := by
  change (∑ v : a, p v • ((Matrix.diagonal
      (fun j => if j = v then (1 : ℂ) else 0)) ⊗ₖ
      CStarMatrix.ofMatrix.symm (rho v).1)) (i,r) (j,t) = _
  simp [Matrix.sum_apply, Matrix.smul_apply, Matrix.kronecker_apply,
    Matrix.diagonal_apply, ite_mul, Complex.real_smul]

private theorem actual_acd {c d : LocalPair} (k : Coupling c d) :
    actualACD k = rowMixture c d := by
  apply Subtype.ext
  apply CStarMatrix.ofMatrix.symm.injective
  ext ⟨a,i⟩ ⟨b,j⟩
  change (∑ t : Bit, actualMatrix k ((a,t),i) ((b,t),j)) =
    CStarMatrix.ofMatrix.symm (rowMixture c d).1 (a,i) (b,j)
  simp only [actual_entry, Fin.sum_univ_two, rowMixture, record_entry]
  fin_cases a <;> fin_cases b <;>
    simp [block, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul] <;> ring

private theorem actual_bcd {c d : LocalPair} (k : Coupling c d) :
    actualBCD k = rowMixture c d := by
  apply Subtype.ext
  apply CStarMatrix.ofMatrix.symm.injective
  ext ⟨a,i⟩ ⟨b,j⟩
  change (∑ t : Bit, actualMatrix k ((t,a),i) ((t,b),j)) =
    CStarMatrix.ofMatrix.symm (rowMixture c d).1 (a,i) (b,j)
  simp only [actual_entry, Fin.sum_univ_two, rowMixture, record_entry]
  fin_cases a <;> fin_cases b <;>
    simp [block, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul] <;> ring

private theorem average_faithful (c : LocalPair) (hx : c.x < 1) :
    (CStarMatrix.ofMatrix.symm c.average.1).PosDef := by
  apply (density_posSemidef c.average).posDef_iff_det_ne_zero.mpr
  intro hz
  have hr := congrArg Complex.re hz
  have hp : 0 < 1 - c.x ^ 2 := by nlinarith [c.x_nonneg]
  norm_num [LocalPair.average, qubitState, qubitMatrix, Matrix.det_fin_two,
    Complex.mul_re, Complex.div_re] at hr
  nlinarith

private theorem record_entropy {a b : Type*} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] (p : a → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    (rho : a → DensityState b) :
    vonNeumannEntropy (recordState p hp hs rho) =
      D5.S3.Entropy.MaxEntropy.shannonEntropy p + ∑ i, p i * vonNeumannEntropy (rho i) := by
  have ho : Pairwise (fun i j =>
      (productState (pointerState i) (rho i)).1 *
        (productState (pointerState j) (rho j)).1 = 0) := by
    intro i j hij
    change (CStarMatrix.ofMatrix.symm (pointerState i).1 ⊗ₖ
      CStarMatrix.ofMatrix.symm (rho i).1) *
      (CStarMatrix.ofMatrix.symm (pointerState j).1 ⊗ₖ
      CStarMatrix.ofMatrix.symm (rho j).1) = 0
    rw [← Matrix.mul_kronecker_mul]
    have hpij : CStarMatrix.ofMatrix.symm (pointerState i).1 *
        CStarMatrix.ofMatrix.symm (pointerState j).1 = 0 := pointerState_orthogonal hij
    rw [hpij, Matrix.zero_kronecker]
  unfold recordState
  rw [orthogonal_mixture_entropy p hp hs _ ho]
  simp only [vonNeumannEntropy_productState, entropy_pointerState, zero_add]

private theorem uniform_entropy :
    D5.S3.Entropy.MaxEntropy.shannonEntropy (fun _ : Bit => (1 / 2 : ℝ)) = Real.log 2 := by
  simp [D5.S3.Entropy.MaxEntropy.shannonEntropy, Fin.sum_univ_two,
    Real.negMulLog, Real.log_div]

private theorem local_equal_entropy (c : LocalPair) :
    vonNeumannEntropy c.minus = vonNeumannEntropy c.plus := by
  simp only [LocalPair.minus, LocalPair.plus, qubit_state_entropy, neg_sq]

private theorem row_entropy (c d : LocalPair) :
    vonNeumannEntropy (rowMixture c d) = Real.log 2 +
      vonNeumannEntropy c.plus + vonNeumannEntropy d.plus := by
  simp only [rowMixture, record_entropy, uniform_entropy, Fin.sum_univ_two]
  simp only [Fin.isValue, ↓reduceIte, one_ne_zero, negativeMargin, positiveMargin,
    vonNeumannEntropy_productState, local_equal_entropy]
  ring

private theorem average_mixture (c : LocalPair) :
    mixtureState (fun _ : Bit => (1 / 2 : ℝ)) (by intro; norm_num)
      (by norm_num [Fin.sum_univ_two]) (fun i => if i = 0 then c.plus else c.minus) =
      c.average := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mixtureState, Fin.sum_univ_two, LocalPair.plus, LocalPair.minus,
      LocalPair.average, qubitState, qubitMatrix] <;> ring

private theorem product_marginals (c d : LocalPair) :
    marginalRight (productMixture c d) = c.average ∧
      marginalLeft (productMixture c d) = d.average := by
  constructor
  · unfold productMixture
    rw [marginalRight_mixture]
    simpa only [positiveMargin, negativeMargin, apply_ite, marginalRight_productState]
      using average_mixture c
  · unfold productMixture
    rw [marginalLeft_mixture]
    simpa only [positiveMargin, negativeMargin, apply_ite, marginalLeft_productState]
      using average_mixture d

private def acEquiv : ((Bit × Bit) × Bit) ≃ (Bit × CD) where
  toFun p := (p.1.1, (p.1.2, p.2))
  invFun p := ((p.1, p.2.1), p.2.2)
  left_inv _ := rfl
  right_inv _ := rfl
private def adEquiv : ((Bit × Bit) × Bit) ≃ (Bit × CD) where
  toFun p := (p.1.1, (p.2, p.1.2))
  invFun p := ((p.1, p.2.2), p.2.1)
  left_inv _ := rfl
  right_inv _ := rfl

def actualAC {c d : LocalPair} (k : Coupling c d) : DensityState (Bit × Bit) :=
  marginalRight (reindexState acEquiv (actualACD k))
def actualAD {c d : LocalPair} (k : Coupling c d) : DensityState (Bit × Bit) :=
  marginalRight (reindexState adEquiv (actualACD k))
def actualBC {c d : LocalPair} (k : Coupling c d) : DensityState (Bit × Bit) :=
  marginalRight (reindexState acEquiv (actualBCD k))
def actualBD {c d : LocalPair} (k : Coupling c d) : DensityState (Bit × Bit) :=
  marginalRight (reindexState adEquiv (actualBCD k))

private def uniformBit : DensityState Bit :=
  mixtureState (fun _ : Bit => (1 / 2 : ℝ)) (by intro; norm_num)
    (by norm_num [Fin.sum_univ_two]) pointerState

private theorem uniform_bit_entropy : vonNeumannEntropy uniformBit = Real.log 2 := by
  rw [uniformBit, orthogonal_mixture_entropy _ _ _ _ pointerState_orthogonal]
  simp only [entropy_pointerState, mul_zero, Finset.sum_const_zero, add_zero, uniform_entropy]

private def localRecord (c : LocalPair) : DensityState (Bit × Bit) :=
  recordState (fun _ : Bit => (1 / 2 : ℝ)) (by intro; norm_num)
    (by norm_num [Fin.sum_univ_two]) (fun i => if i = 0 then c.plus else c.minus)

private theorem local_record_entropy (c : LocalPair) :
    vonNeumannEntropy (localRecord c) = Real.log 2 + vonNeumannEntropy c.plus := by
  simp only [localRecord, record_entropy, uniform_entropy, Fin.sum_univ_two,
    Fin.isValue, ↓reduceIte, one_ne_zero, local_equal_entropy]
  ring

private theorem row_a (c d : LocalPair) : marginalRight (rowMixture c d) = uniformBit := by
  unfold rowMixture recordState
  rw [marginalRight_mixture]
  simp only [marginalRight_productState]
  rfl

private theorem row_ac (c d : LocalPair) :
    marginalRight (reindexState acEquiv (rowMixture c d)) = localRecord c := by
  apply Subtype.ext
  apply CStarMatrix.ofMatrix.symm.injective
  ext ⟨a,i⟩ ⟨b,j⟩
  change (∑ t : Bit, CStarMatrix.ofMatrix.symm (rowMixture c d).1 (a,(i,t)) (b,(j,t))) =
    CStarMatrix.ofMatrix.symm (localRecord c).1 (a,i) (b,j)
  simp only [rowMixture, localRecord, record_entry, Fin.sum_univ_two]
  fin_cases a <;> fin_cases b <;> fin_cases i <;> fin_cases j <;>
    simp [positiveMargin, negativeMargin, productState, Matrix.kroneckerMap,
      LocalPair.plus, LocalPair.minus, qubitState, qubitMatrix] <;> ring

private theorem row_ad (c d : LocalPair) :
    marginalRight (reindexState adEquiv (rowMixture c d)) = localRecord d := by
  apply Subtype.ext
  apply CStarMatrix.ofMatrix.symm.injective
  ext ⟨a,i⟩ ⟨b,j⟩
  change (∑ t : Bit, CStarMatrix.ofMatrix.symm (rowMixture c d).1 (a,(t,i)) (b,(t,j))) =
    CStarMatrix.ofMatrix.symm (localRecord d).1 (a,i) (b,j)
  simp only [rowMixture, localRecord, record_entry, Fin.sum_univ_two]
  fin_cases a <;> fin_cases b <;> fin_cases i <;> fin_cases j <;>
    simp [positiveMargin, negativeMargin, productState, Matrix.kroneckerMap,
      LocalPair.plus, LocalPair.minus, qubitState, qubitMatrix] <;> ring

private def abProbability {c d : LocalPair} (k : Coupling c d) (ab : AB) : ℝ :=
  if ab.1 = ab.2 then (1 - k.K.trace.re) / 2 else k.K.trace.re / 2

private theorem ab_probability_nonneg {c d : LocalPair} (k : Coupling c d) (ab : AB) :
    0 ≤ abProbability k ab := by
  have hk := trace_coupling_range k
  unfold abProbability
  split_ifs <;> linarith [hk.1, hk.2]

private theorem ab_probability_sum {c d : LocalPair} (k : Coupling c d) :
    ∑ ab : AB, abProbability k ab = 1 := by
  simp [abProbability, Fintype.sum_prod_type, Fin.sum_univ_two]
  ring

private theorem actual_ab {c d : LocalPair} (k : Coupling c d) :
    marginalRight (actualState k) =
      mixtureState (abProbability k) (ab_probability_nonneg k) (ab_probability_sum k) pointerState := by
  apply Subtype.ext
  apply CStarMatrix.ofMatrix.symm.injective
  ext a b
  change (∑ i : CD, actualMatrix k (a,i) (b,i)) = _
  simp only [actual_entry]
  have hptr (i j : AB) : CStarMatrix.ofMatrix.symm
      (mixtureState (abProbability k) (ab_probability_nonneg k) (ab_probability_sum k) pointerState).1 i j =
      if i = j then (abProbability k i : ℂ) else 0 := by
    change (∑ v : AB, abProbability k v • Matrix.diagonal
      (fun j => if j = v then (1 : ℂ) else 0)) i j = _
    simp [Matrix.sum_apply, Matrix.smul_apply, Matrix.diagonal_apply, ite_mul,
      Complex.real_smul]
  rw [hptr]
  have hkreal : (k.K.trace.re : ℂ) = k.K.trace := by
    apply Complex.ext
    · simp
    · simpa using (Complex.nonneg_iff.mp k.positive.trace_nonneg).2
  have hp : (CStarMatrix.ofMatrix.symm (positiveMargin c d).1).trace = 1 :=
    (positiveMargin c d).2.2
  have hq : (CStarMatrix.ofMatrix.symm (negativeMargin c d).1).trace = 1 :=
    (negativeMargin c d).2.2
  have hb (ab : AB) : (block k ab).trace = (abProbability k ab : ℂ) := by
    rcases ab with ⟨a,b⟩
    fin_cases a <;> fin_cases b <;>
      simp [block, abProbability, Matrix.trace_smul, Matrix.trace_sub,
        hp, hq, Complex.real_smul] <;> push_cast <;> rw [hkreal] <;> ring
  by_cases h : a = b
  · subst b
    simp only [↓reduceIte]
    exact hb a
  · simp [h]

private theorem ab_entropy {c d : LocalPair} (k : Coupling c d) :
    vonNeumannEntropy (marginalRight (actualState k)) = Real.log 2 + Real.binEntropy k.K.trace.re := by
  rw [actual_ab, orthogonal_mixture_entropy _ _ _ _ pointerState_orthogonal]
  simp only [entropy_pointerState, mul_zero, Finset.sum_const_zero, add_zero]
  simp only [D5.S3.Entropy.MaxEntropy.shannonEntropy, Fintype.sum_prod_type,
    Fin.sum_univ_two, abProbability]
  norm_num only [Fin.isValue, Prod.fst, Prod.snd, ↓reduceIte, one_ne_zero, zero_ne_one]
  rw [show (1 - k.K.trace.re) / 2 = (1 - k.K.trace.re) * (1 / 2) by ring,
    show k.K.trace.re / 2 = k.K.trace.re * (1 / 2) by ring,
    Real.negMulLog_mul, Real.negMulLog_mul,
    Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  simp [Real.negMulLog, Real.log_div]
  <;> ring

private theorem holevo_value (c : LocalPair) :
    qubitHolevo c.x c.z c.disk = vonNeumannEntropy c.average - vonNeumannEntropy c.plus := by
  change vonNeumannEntropy c.average -
    (vonNeumannEntropy c.plus + vonNeumannEntropy c.minus) / 2 = _
  rw [local_equal_entropy]
  ring

/-- The original natural-log Zhang--Yeung convention, evaluated on actual partial traces. -/
def zhangYeungGap {c d : LocalPair} (k : Coupling c d) : ℝ :=
  let a := vonNeumannEntropy (marginalRight (actualACD k))
  let b := vonNeumannEntropy (marginalRight (actualBCD k))
  let ab := vonNeumannEntropy (marginalRight (actualState k))
  let ac := vonNeumannEntropy (actualAC k)
  let ad := vonNeumannEntropy (actualAD k)
  let bc := vonNeumannEntropy (actualBC k)
  let bd := vonNeumannEntropy (actualBD k)
  let acd := vonNeumannEntropy (actualACD k)
  let bcd := vonNeumannEntropy (actualBCD k)
  let cd := vonNeumannEntropy (marginalLeft (actualState k))
  let ce := vonNeumannEntropy (marginalRight (marginalLeft (actualState k)))
  let de := vonNeumannEntropy (marginalLeft (marginalLeft (actualState k)))
  2 * (ac + ad - a - acd) + (bc + bd - b - bcd) + (a + b - ab) +
    (ad + cd - de - acd) + (ac + cd - ce - acd) - (ce + de - cd)

/-- The original spectral gap on the actual sixteen-dimensional density, with no
information estimate or rank hypothesis supplied as an assumption. -/
theorem actual_gap_identity (c d : LocalPair) (k : Coupling c d) :
    zhangYeungGap k = Real.log 2 - Real.binEntropy k.K.trace.re +
      qubitHolevo c.x c.z c.disk + qubitHolevo d.x d.z d.disk -
      3 * quantumMutualInformation (productMixture c d) := by
  simp only [zhangYeungGap, actualAC, actualAD, actualBC, actualBD,
    actual_acd, actual_bcd, row_a, row_ac, row_ad, uniform_bit_entropy,
    local_record_entropy, row_entropy, ab_entropy, actual_cd,
    (product_marginals c d).1, (product_marginals c d).2,
    holevo_value, quantumMutualInformation]
  ring

private theorem local_record_marginals (c : LocalPair) :
    marginalRight (localRecord c) = uniformBit ∧
    marginalLeft (localRecord c) = c.average := by
  constructor
  · unfold localRecord recordState
    rw [marginalRight_mixture]
    simp only [marginalRight_productState]
    rfl
  · unfold localRecord recordState
    rw [marginalLeft_mixture]
    simpa only [marginalLeft_productState] using average_mixture c

private theorem local_record_information (c : LocalPair) :
    quantumMutualInformation (localRecord c) = qubitHolevo c.x c.z c.disk := by
  rw [quantumMutualInformation, (local_record_marginals c).1,
    (local_record_marginals c).2, uniform_bit_entropy, local_record_entropy, holevo_value]
  ring

private theorem uniform_faithful :
    (CStarMatrix.ofMatrix.symm uniformBit.1).PosDef := by
  have he : uniformBit = qubitState 0 0 (by norm_num) := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [uniformBit, mixtureState, pointerState, Fin.sum_univ_two,
        qubitState, qubitMatrix, Matrix.diagonal_apply]
  rw [he]
  exact average_faithful ⟨0, 0, le_refl _, le_refl _, by norm_num⟩ (by norm_num)

private theorem local_preparation_information
    (rho sigma : DensityState (Bit × Bit)) (p : Bit → DensityState Bit)
    (hrA : (CStarMatrix.ofMatrix.symm (marginalRight rho).1).PosDef)
    (hrB : (CStarMatrix.ofMatrix.symm (marginalLeft rho).1).PosDef)
    (hsA : (CStarMatrix.ofMatrix.symm (marginalRight sigma).1).PosDef)
    (hsB : (CStarMatrix.ofMatrix.symm (marginalLeft sigma).1).PosDef)
    (he : ∀ r t : Bit × Bit,
      ∑ i : Bit, CStarMatrix.ofMatrix.symm rho.1 (r.1,i) (t.1,i) *
        CStarMatrix.ofMatrix.symm (p i).1 r.2 t.2 =
          CStarMatrix.ofMatrix.symm sigma.1 r t)
    (hp : ∀ r t : Bit × Bit,
      ∑ i : Bit, CStarMatrix.ofMatrix.symm
          (productState (marginalRight rho) (marginalLeft rho)).1 (r.1,i) (t.1,i) *
        CStarMatrix.ofMatrix.symm (p i).1 r.2 t.2 =
          CStarMatrix.ofMatrix.symm
            (productState (marginalRight sigma) (marginalLeft sigma)).1 r t) :
    quantumMutualInformation sigma ≤ quantumMutualInformation rho := by
  obtain ⟨channel, hc⟩ :=
    D5.S3.Quantum.Foundation.FinitePreparationChannel.finite_local_preparation_quantum_channel
      (fun i => fromLegacyDensityState (p i)) (s := Bit)
  have hm (u v : DensityState (Bit × Bit))
      (huv : ∀ r t : Bit × Bit,
        ∑ i : Bit, CStarMatrix.ofMatrix.symm u.1 (r.1,i) (t.1,i) *
          CStarMatrix.ofMatrix.symm (p i).1 r.2 t.2 =
            CStarMatrix.ofMatrix.symm v.1 r t) :
      channel.mapState (fromLegacyDensityState u) = fromLegacyDensityState v := by
    apply Subtype.ext
    apply CStarMatrix.ofMatrix.symm.injective
    ext r t
    change CStarMatrix.ofMatrix.symm
      (channel.toCompletelyPositiveMap
        (CStarMatrix.ofMatrix (CStarMatrix.ofMatrix.symm u.1))) r t = _
    rw [hc]
    exact huv r t
  exact mutual_information_dpi rho sigma channel hrA hrB hsA hsB
    (hm rho sigma he) (hm _ _ hp)

private theorem prepare_record_information (e f p : LocalPair)
    (he : e.x < 1) (hf : f.x < 1) (hfx : f.x = p.x) (hfz : f.z = e.z * p.z) :
    quantumMutualInformation (localRecord f) ≤ quantumMutualInformation (localRecord e) := by
  apply local_preparation_information (localRecord e) (localRecord f)
    (fun i => if i = 0 then p.plus else p.minus)
  · rw [(local_record_marginals e).1]; exact uniform_faithful
  · rw [(local_record_marginals e).2]; exact average_faithful e he
  · rw [(local_record_marginals f).1]; exact uniform_faithful
  · rw [(local_record_marginals f).2]; exact average_faithful f hf
  · intro ⟨a,i⟩ ⟨b,j⟩
    simp only [localRecord, record_entry, Fin.sum_univ_two]
    fin_cases a <;> fin_cases b <;> fin_cases i <;> fin_cases j <;>
      simp [LocalPair.plus, LocalPair.minus, qubitState, qubitMatrix, hfx, hfz] <;> ring
  · intro ⟨a,i⟩ ⟨b,j⟩
    rw [(local_record_marginals e).1, (local_record_marginals e).2,
      (local_record_marginals f).1, (local_record_marginals f).2]
    fin_cases a <;> fin_cases b <;> fin_cases i <;> fin_cases j <;>
      simp [productState, Matrix.kroneckerMap, uniformBit, mixtureState,
        pointerState, Fin.sum_univ_two, Matrix.diagonal_apply, LocalPair.average,
        LocalPair.plus, LocalPair.minus, qubitState, qubitMatrix, hfx] <;> ring

private def LocalPair.scaled (c : LocalPair) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    LocalPair :=
  ⟨c.x, t * c.z, c.x_nonneg, mul_nonneg ht.1 c.z_nonneg, by
    nlinarith [c.disk, mul_nonneg (show 0 ≤ 1 - t ^ 2 by nlinarith [ht.1, ht.2])
      (sq_nonneg c.z)]⟩

private theorem scaled_average (c : LocalPair) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (c.scaled t ht).average = c.average := rfl

private theorem swap_record_marginals (c : LocalPair) :
    marginalRight (reindexState (Equiv.prodComm Bit Bit) (localRecord c)) = c.average ∧
    marginalLeft (reindexState (Equiv.prodComm Bit Bit) (localRecord c)) = uniformBit := by
  constructor
  · exact (local_record_marginals c).2
  · exact (local_record_marginals c).1

private theorem prepare_product_information (c d p : LocalPair) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (hc : c.x < 1) (hd : d.x < 1)
    (hdx : d.x = p.x) (hdz : d.z = t * p.z) :
    quantumMutualInformation (productMixture c d) ≤
      quantumMutualInformation (localRecord (c.scaled t ht)) := by
  rw [← mutual_information_swap (localRecord (c.scaled t ht))]
  apply local_preparation_information
    (reindexState (Equiv.prodComm Bit Bit) (localRecord (c.scaled t ht)))
    (productMixture c d) (fun i => if i = 0 then p.plus else p.minus)
  · rw [(swap_record_marginals _).1, scaled_average]; exact average_faithful c hc
  · rw [(swap_record_marginals _).2]; exact uniform_faithful
  · rw [(product_marginals c d).1]; exact average_faithful c hc
  · rw [(product_marginals c d).2]; exact average_faithful d hd
  · intro ⟨a,i⟩ ⟨b,j⟩
    change (∑ v : Bit, CStarMatrix.ofMatrix.symm
      (localRecord (c.scaled t ht)).1 (v,a) (v,b) *
        CStarMatrix.ofMatrix.symm (if v = 0 then p.plus else p.minus).1 i j) = _
    simp only [localRecord, record_entry, ↓reduceIte, Fin.sum_univ_two]
    fin_cases a <;> fin_cases b <;> fin_cases i <;> fin_cases j <;>
      simp [productMixture, mixtureState, Fin.sum_univ_two, positiveMargin, negativeMargin,
        productState, Matrix.kroneckerMap, LocalPair.plus, LocalPair.minus,
        LocalPair.scaled, qubitState, qubitMatrix, hdx, hdz] <;> ring
  · intro ⟨a,i⟩ ⟨b,j⟩
    rw [(swap_record_marginals _).1, (swap_record_marginals _).2,
      scaled_average, (product_marginals c d).1, (product_marginals c d).2]
    fin_cases a <;> fin_cases b <;> fin_cases i <;> fin_cases j <;>
      simp [productState, Matrix.kroneckerMap, uniformBit, mixtureState,
        pointerState, Fin.sum_univ_two, Matrix.diagonal_apply, LocalPair.average,
        LocalPair.plus, LocalPair.minus, qubitState, qubitMatrix, hdx] <;> ring

private theorem mutual_information_nonneg (rho : DensityState (Bit × Bit))
    (hA : (CStarMatrix.ofMatrix.symm (marginalRight rho).1).PosDef)
    (hB : (CStarMatrix.ofMatrix.symm (marginalLeft rho).1).PosDef) :
    0 ≤ quantumMutualInformation rho := by
  have h := local_preparation_information rho
    (productState (marginalRight rho) uniformBit) (fun _ => uniformBit)
    hA hB (by rw [marginalRight_productState]; exact hA)
    (by rw [marginalLeft_productState]; exact uniform_faithful) ?_ ?_
  · simpa only [quantumMutualInformation_productState] using h
  · intro r t
    change (∑ i : Bit, CStarMatrix.ofMatrix.symm rho.1 (r.1,i) (t.1,i) *
      CStarMatrix.ofMatrix.symm uniformBit.1 r.2 t.2) =
        (∑ i : Bit, CStarMatrix.ofMatrix.symm rho.1 (r.1,i) (t.1,i)) *
          CStarMatrix.ofMatrix.symm uniformBit.1 r.2 t.2
    exact (Finset.sum_mul _ _ _).symm
  · intro r t
    rw [marginalRight_productState, marginalLeft_productState]
    change (∑ i : Bit, CStarMatrix.ofMatrix.symm (marginalRight rho).1 r.1 t.1 *
      CStarMatrix.ofMatrix.symm (marginalLeft rho).1 i i *
      CStarMatrix.ofMatrix.symm uniformBit.1 r.2 t.2) =
      CStarMatrix.ofMatrix.symm (marginalRight rho).1 r.1 t.1 *
        CStarMatrix.ofMatrix.symm uniformBit.1 r.2 t.2
    calc
      _ = CStarMatrix.ofMatrix.symm (marginalRight rho).1 r.1 t.1 *
          (∑ i : Bit, CStarMatrix.ofMatrix.symm (marginalLeft rho).1 i i) *
          CStarMatrix.ofMatrix.symm uniformBit.1 r.2 t.2 := by
        simp only [Finset.sum_mul, Finset.mul_sum]
      _ = _ := by
        have ht : (∑ i : Bit, CStarMatrix.ofMatrix.symm (marginalLeft rho).1 i i) = 1 :=
          (marginalLeft rho).2.2
        rw [ht]
        ring

private def LocalPair.radius (c : LocalPair) : ℝ := Real.sqrt (1 - c.x ^ 2)
private def LocalPair.reliability (c : LocalPair) : ℝ := c.z / c.radius

private theorem local_radius_sq (c : LocalPair) : c.radius ^ 2 = 1 - c.x ^ 2 :=
  Real.sq_sqrt (by nlinarith [c.disk, sq_nonneg c.z])

private def LocalPair.pure (c : LocalPair) : LocalPair :=
  ⟨c.x, c.radius, c.x_nonneg, Real.sqrt_nonneg _, by rw [local_radius_sq]; nlinarith⟩

private theorem reliability_range (c : LocalPair) (hx : c.x < 1) :
    c.reliability ∈ Set.Icc (0 : ℝ) 1 := by
  have hr : 0 < c.radius := Real.sqrt_pos.mpr (by nlinarith [c.x_nonneg])
  refine ⟨div_nonneg c.z_nonneg hr.le, (div_le_one hr).mpr ?_⟩
  have hs := local_radius_sq c
  nlinarith [c.disk, c.z_nonneg]

private theorem reliability_radius (c : LocalPair) (hx : c.x < 1) :
    c.reliability * c.radius = c.z := by
  have hr : c.radius ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by nlinarith [c.x_nonneg]))
  exact div_mul_cancel₀ _ hr

private theorem reliability_sq (c : LocalPair) :
    c.reliability ^ 2 = c.z ^ 2 / (1 - c.x ^ 2) := by
  rw [LocalPair.reliability, div_pow, local_radius_sq]

private theorem holevo_nonneg (c : LocalPair) : 0 ≤ qubitHolevo c.x c.z c.disk := by
  have h := D5.S3.Quantum.Information.QubitEntropyContraction.qubit_holevo_contraction
    c.disk (show (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by norm_num)
  simpa only [one_mul] using h.1

private theorem product_information_contraction (c d : LocalPair)
    (hc : c.x < 1) (hd : d.x < 1) :
    quantumMutualInformation (productMixture c d) ≤
      d.reliability ^ 2 * qubitHolevo c.x c.z c.disk := by
  have h := prepare_product_information c d d.pure d.reliability
    (reliability_range d hd) hc hd rfl (reliability_radius d hd).symm
  rw [local_record_information] at h
  exact h.trans (D5.S3.Quantum.Information.QubitEntropyContraction.qubit_holevo_contraction
    c.disk (reliability_range d hd)).2

private theorem product_information_swap (c d : LocalPair) :
    quantumMutualInformation (productMixture c d) =
      quantumMutualInformation (productMixture d c) := by
  have he : reindexState (Equiv.prodComm Bit Bit) (productMixture c d) =
      productMixture d c := by
    apply Subtype.ext
    ext ⟨a,i⟩ ⟨b,j⟩
    fin_cases a <;> fin_cases b <;> fin_cases i <;> fin_cases j <;>
      simp [reindexState, productMixture, mixtureState, Fin.sum_univ_two,
        positiveMargin, negativeMargin, productState, Matrix.kroneckerMap,
        LocalPair.plus, LocalPair.minus, qubitState, qubitMatrix] <;> ring
  rw [← he, mutual_information_swap]

private def classicalPair (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) : LocalPair :=
  ⟨0, s, le_refl _, hs.1, by nlinarith [hs.1, hs.2]⟩

private theorem product_information_absolute (c d : LocalPair)
    (hc : c.x < 1) (hd : d.x < 1) :
    quantumMutualInformation (productMixture c d) ≤ Real.log 2 -
      Real.binEntropy ((1 + c.reliability * d.reliability) / 2) := by
  have hct := reliability_range c hc
  have hdt := reliability_range d hd
  have hs : c.reliability * d.reliability ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨mul_nonneg hct.1 hdt.1, mul_le_one₀ hct.2 hdt.1 hdt.2⟩
  let e := classicalPair (c.reliability * d.reliability) hs
  let f := c.scaled d.reliability hdt
  have hprep := prepare_record_information e f c.pure (by norm_num [e, classicalPair]) hc rfl (by
    change d.reliability * c.z = (c.reliability * d.reliability) * c.radius
    calc
      _ = d.reliability * (c.reliability * c.radius) := by rw [reliability_radius c hc]
      _ = _ := by ring)
  have h := prepare_product_information c d d.pure d.reliability hdt hc hd rfl
    (reliability_radius d hd).symm
  have hle := h.trans hprep
  rw [local_record_information, holevo_value] at hle
  have heval : vonNeumannEntropy e.average - vonNeumannEntropy e.plus =
      Real.log 2 - Real.binEntropy ((1 + c.reliability * d.reliability) / 2) := by
    simp only [e, classicalPair, LocalPair.average, LocalPair.plus, qubit_state_entropy]
    rw [show (0 : ℝ) ^ 2 + (0 : ℝ) ^ 2 = 0 by norm_num, Real.sqrt_zero]
    rw [show (0 : ℝ) ^ 2 + (c.reliability * d.reliability) ^ 2 =
        (c.reliability * d.reliability) ^ 2 by ring, Real.sqrt_sq hs.1]
    rw [show ((1 : ℝ) + 0) / 2 = (2 : ℝ)⁻¹ by norm_num, Real.binEntropy_two_inv]
  exact hle.trans_eq heval

private theorem product_mixture_zero_left (c d : LocalPair) (hz : c.z = 0) :
    productMixture c d = productState c.average d.average := by
  apply Subtype.ext
  ext ⟨a,i⟩ ⟨b,j⟩
  fin_cases a <;> fin_cases b <;> fin_cases i <;> fin_cases j <;>
    simp [productMixture, mixtureState, Fin.sum_univ_two, positiveMargin, negativeMargin,
      productState, Matrix.kroneckerMap, LocalPair.average, LocalPair.plus, LocalPair.minus,
      qubitState, qubitMatrix, hz] <;> ring

/-- The original four-parameter product-margin theorem on its actual sixteen-dimensional
state. The closed disks and every complex positive common lower matrix remain in scope. -/
theorem actual_zhang_yeung_nonneg (c d : LocalPair) (k : Coupling c d) :
    0 ≤ zhangYeungGap k := by
  rw [actual_gap_identity]
  have hk : 0 ≤ k.K.trace.re := (trace_coupling_range k).1
  have hcchi := holevo_nonneg c
  have hdchi := holevo_nonneg d
  have hbin : 0 ≤ Real.log 2 - Real.binEntropy k.K.trace.re :=
    sub_nonneg.mpr Real.binEntropy_le_log_two
  by_cases hc : c.x < 1
  · by_cases hd : d.x < 1
    · have ha : c.reliability ^ 2 ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨sq_nonneg _, by nlinarith [(reliability_range c hc).1,
          (reliability_range c hc).2]⟩
      have hb : d.reliability ^ 2 ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨sq_nonneg _, by nlinarith [(reliability_range d hd).1,
          (reliability_range d hd).2]⟩
      have hs : Real.sqrt (c.reliability ^ 2 * d.reliability ^ 2) =
          c.reliability * d.reliability := by
        rw [← mul_pow, Real.sqrt_sq (mul_nonneg (reliability_range c hc).1
          (reliability_range d hd).1)]
      apply D5.S3.Quantum.Information.ProductMarginEntropyCertificate.information_budget_nonneg
        ha hb hk hcchi hdchi
      · apply mutual_information_nonneg
        · rw [(product_marginals c d).1]; exact average_faithful c hc
        · rw [(product_marginals c d).2]; exact average_faithful d hd
      · rw [reliability_sq, reliability_sq]
        exact D5.S3.Quantum.Information.ProductMarginQubitOrder.common_lower_trace_bound
          c.x_nonneg hc d.x_nonneg hd c.disk d.disk k.positive k.le_positive k.le_negative
      · exact product_information_contraction c d hc hd
      · rw [product_information_swap]
        exact product_information_contraction d c hd hc
      · rw [hs]
        exact product_information_absolute c d hc hd
    · have hz : d.z = 0 := by nlinarith [d.disk, d.z_nonneg, d.x_nonneg]
      have hj : quantumMutualInformation (productMixture c d) = 0 := by
        rw [product_information_swap, product_mixture_zero_left d c hz,
          quantumMutualInformation_productState]
      rw [hj]
      linarith
  · have hz : c.z = 0 := by nlinarith [c.disk, c.z_nonneg, c.x_nonneg]
    rw [product_mixture_zero_left c d hz, quantumMutualInformation_productState]
    linarith

#print axioms actual_zhang_yeung_nonneg

#print axioms actual_gap_identity

end D5.S3.Quantum.Information.ProductMarginZhangYeung
