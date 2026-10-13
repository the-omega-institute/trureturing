/- GID: D5/S3/Quantum/Recovery/PhaseBoundaryDiagonalReferenceReduction
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/PhaseBoundaryDiagonalReferenceReduction
   mirror-E: none(waiver:research-interface)
   anchors: []
   utility: none
   digest: Diagonal reference tests dominate actual common-instrument recovery. -/
import D5.S3.Quantum.Recovery.PhaseBoundarySpectralReduction
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

noncomputable section
namespace D5.S3.Quantum.Recovery.PhaseBoundaryDiagonalReferenceReduction
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteDiamondDistance
open D5.S3.Quantum.Foundation.FiniteTraceDistance
open D5.S3.Quantum.Recovery.PhaseBoundarySourceModel
open D5.S3.Quantum.Recovery.PhaseBoundaryFlagInstrument
open D5.S3.Quantum.Recovery.PhaseBoundarySpectralReduction
open Matrix
open scoped BigOperators CStarAlgebra ComplexOrder MatrixOrder
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

private abbrev Local := Qubit × Qubit
private abbrev Output := Qubit × (Qubit × Qubit)
private abbrev Instrument := FlagInstrument (S := Qubit) (J := Qubit) (A := Qubit) (B := Qubit)

private def basisInput (j : Qubit) : Unit × Qubit → ℂ := fun p => if p.2 = j then 1 else 0
private theorem basis_norm (j : Qubit) : star (basisInput j) ⬝ᵥ basisInput j = 1 := by
  simp [basisInput, dotProduct, Fintype.sum_prod_type]

private def columnMass {F : Type} [Fintype F] (v : F × Qubit → ℂ) (j : Qubit) : ℝ :=
  ∑ f, Complex.normSq (v (f,j))
private def amplitude {F : Type} [Fintype F] (v : F × Qubit → ℂ) (j : Qubit) : ℂ :=
  (Real.sqrt (columnMass v j) : ℂ)
private def normalizedColumn {F : Type} [Fintype F] [DecidableEq F] [Nonempty F]
    (v : F × Qubit → ℂ) (j : Qubit) (f : F) : ℂ :=
  if columnMass v j = 0 then if f = Classical.arbitrary F then 1 else 0
  else v (f,j) / amplitude v j
private theorem mass_nonnegative {F : Type} [Fintype F] (v : F × Qubit → ℂ) (j : Qubit) :
    0 ≤ columnMass v j := Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _)
private theorem amplitude_square {F : Type} [Fintype F] (v : F × Qubit → ℂ) (j : Qubit) :
    Complex.normSq (amplitude v j) = columnMass v j := by
  simp [amplitude, Complex.normSq_ofReal, Real.mul_self_sqrt (mass_nonnegative v j)]
private theorem zero_column {F : Type} [Fintype F] (v : F × Qubit → ℂ) (j : Qubit)
    (h : columnMass v j = 0) (f : F) : v (f,j) = 0 := by
  have hz : Complex.normSq (v (f,j)) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Complex.normSq_nonneg _)).mp h f (Finset.mem_univ f)
  exact Complex.normSq_eq_zero.mp hz
private theorem column_factor {F : Type} [Fintype F] [DecidableEq F] [Nonempty F]
    (v : F × Qubit → ℂ) (j : Qubit) (f : F) :
    amplitude v j * normalizedColumn v j f = v (f,j) := by
  by_cases hz : columnMass v j = 0
  · simp [normalizedColumn, amplitude, hz, zero_column v j hz f]
  · have hc : amplitude v j ≠ 0 := by
      intro hc
      exact hz ((amplitude_square v j).symm.trans (by rw [hc]; simp))
    simp [normalizedColumn, hz, hc, mul_div_cancel₀]
private theorem column_normalized {F : Type} [Fintype F] [DecidableEq F] [Nonempty F]
    (v : F × Qubit → ℂ) (j : Qubit) :
    ∑ f, Complex.normSq (normalizedColumn v j f) = 1 := by
  by_cases hz : columnMass v j = 0
  · simp [normalizedColumn, hz]
  · simp only [normalizedColumn, if_neg hz, Complex.normSq_div]
    rw [← Finset.sum_div, amplitude_square]
    exact div_self hz
private theorem amplitudes_normalized {F : Type} [Fintype F]
    (v : F × Qubit → ℂ) (hv : star v ⬝ᵥ v = 1) :
    ∑ j, Complex.normSq (amplitude v j) = 1 := by
  have hh := congrArg Complex.re hv
  simp only [dotProduct, Pi.star_apply, Complex.star_def,
    ← Complex.normSq_eq_conj_mul_self, Complex.re_sum, Complex.ofReal_re,
    Complex.one_re] at hh
  simp_rw [amplitude_square]
  simpa [columnMass, Fintype.sum_prod_type, Finset.sum_comm] using hh
private def controlledColumns {F : Type} [Fintype F] [DecidableEq F] [Nonempty F]
    (v : F × Qubit → ℂ) : Matrix (F × Output) Output ℂ :=
  fun p t => if p.2.2.1 = t.1 ∧ p.2.1 = t.2.1 ∧ p.2.2.2 = t.2.2 then
    normalizedColumn v t.1 p.1 else 0
private theorem controlled_isometry {F : Type} [Fintype F] [DecidableEq F] [Nonempty F]
    (v : F × Qubit → ℂ) : (controlledColumns v)ᴴ * controlledColumns v = 1 := by
  have hn (j : Qubit) : (∑ f, (Complex.normSq (normalizedColumn v j f) : ℂ)) = 1 := by
    exact_mod_cast column_normalized v j
  ext ⟨j,m,a⟩ ⟨k,n,b⟩
  fin_cases j <;> fin_cases m <;> fin_cases a <;>
    fin_cases k <;> fin_cases n <;> fin_cases b <;>
    simp [controlledColumns, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two,
      ← Complex.normSq_eq_conj_mul_self, Complex.star_def, hn]

private def liftBranch {F : Type} (v : F × Qubit → ℂ) (j k : Qubit) :
    Matrix (F × Output) Local ℂ :=
  fun p t => if p.2.1 = t.1 ∧ p.2.2.1 = k ∧ p.2.2.2 = t.2 then v (p.1,j) else 0
private theorem lift_branch_entry {F : Type} [Fintype F] [DecidableEq F]
    (v : F × Qubit → ℂ) (j k : Qubit) (X : Matrix Local Local ℂ)
    (f g : F) (m n l o a b : Qubit) :
    (liftBranch v j k * X * (liftBranch v j k)ᴴ) (f,(m,(l,a))) (g,(n,(o,b))) =
      if l = k ∧ o = k then (v (f,j) * star (v (g,j))) * X (m,a) (n,b) else 0 := by
  fin_cases m <;> fin_cases n <;> fin_cases l <;> fin_cases o <;>
    fin_cases a <;> fin_cases b <;> fin_cases k <;>
    simp [liftBranch, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, mul_assoc, mul_left_comm, mul_comm]
private theorem controlled_conjugation_entry {F : Type} [Fintype F] [DecidableEq F] [Nonempty F]
    (v : F × Qubit → ℂ) (C : Matrix Output Output ℂ)
    (f g : F) (m n k l a b : Qubit) :
    (controlledColumns v * C * (controlledColumns v)ᴴ) (f,(m,(k,a))) (g,(n,(l,b))) =
      (normalizedColumn v k f * star (normalizedColumn v l g)) * C (k,(m,a)) (l,(n,b)) := by
  fin_cases m <;> fin_cases n <;> fin_cases k <;> fin_cases l <;>
    fin_cases a <;> fin_cases b <;>
    simp [controlledColumns, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, mul_assoc, mul_left_comm, mul_comm]

private theorem spectral_domination {n m : Type} [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m]
    (A : Matrix n n ℂ) (hA : A.IsHermitian) (C : Matrix m m ℂ) (hC : C.IsHermitian)
    (W : Matrix n m ℂ) (hW : Wᴴ * W = 1)
    (hQ : (W * C * Wᴴ - A).PosSemidef)
    (E lambda : ℝ) (hE : E ∈ Set.range hA.eigenvalues)
    (hlambda : IsGreatest (Set.range hC.eigenvalues) lambda) (hlambda0 : 0 ≤ lambda) :
    E ≤ lambda := by
  have hCbound : C ≤ algebraMap ℝ (Matrix m m ℂ) lambda := by
    apply (le_algebraMap_iff_spectrum_le hC.isSelfAdjoint).mpr
    rw [hC.spectrum_real_eq_range_eigenvalues]
    exact hlambda.2
  have hCp : (algebraMap ℝ (Matrix m m ℂ) lambda - C).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hCbound)
  have hWp := hCp.mul_mul_conjTranspose_same W
  let P := W * Wᴴ
  have hP : P * P = P := by
    change W * Wᴴ * (W * Wᴴ) = W * Wᴴ
    calc
      _ = W * (Wᴴ * W) * Wᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hW, Matrix.mul_one]
  have hPH : Pᴴ = P := by simp [P]
  have hproj : (1 - P).PosSemidef := by
    have hp := Matrix.posSemidef_self_mul_conjTranspose (1 - P)
    have heq : (1 - P) * (1 - P)ᴴ = 1 - P := by
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hPH,
        Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul,
        Matrix.one_mul, Matrix.mul_one, hP]
      simp only [Matrix.one_mul]
      abel
    rwa [heq] at hp
  have hscalar : 0 ≤ lambda • (1 - P) := smul_nonneg hlambda0 hproj.nonneg
  have hsplit : algebraMap ℝ (Matrix n n ℂ) lambda - A =
      W * (algebraMap ℝ (Matrix m m ℂ) lambda - C) * Wᴴ +
        lambda • (1 - P) + (W * C * Wᴴ - A) := by
    simp only [Algebra.algebraMap_eq_smul_one, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, smul_sub]
    change lambda • (1 : Matrix n n ℂ) - A =
      (lambda • P - W * C * Wᴴ) + (lambda • 1 - lambda • P) + (W * C * Wᴴ - A)
    abel
  have hAbound : A ≤ algebraMap ℝ (Matrix n n ℂ) lambda := by
    apply sub_nonneg.mp
    rw [hsplit]
    exact add_nonneg (add_nonneg hWp.nonneg hscalar) hQ.nonneg
  have hh := (le_algebraMap_iff_spectrum_le hA.isSelfAdjoint).mp hAbound
  apply hh
  rwa [hA.spectrum_real_eq_range_eigenvalues]

/-- Canonical diagonal-edge amplitudes for the weight in the closed unit interval. -/
def weightInput (q : ℝ) : Qubit → ℂ :=
  fun j => if j = 0 then (Real.sqrt q : ℂ) else (Real.sqrt (1-q) : ℂ)
private theorem weight_norm (q : ℝ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    ∑ j, Complex.normSq (weightInput q j) = 1 := by
  simp [weightInput, Fin.sum_univ_two, Complex.normSq_ofReal,
    Real.mul_self_sqrt h0, Real.mul_self_sqrt (sub_nonneg.mpr h1)]
/-- The lawful pure reference test, including both endpoints. -/
def weightState (q : ℝ) (h0 : 0 ≤ q) (h1 : q ≤ 1) : DensityState (Qubit × Qubit) :=
  pureState (diagonalInput (weightInput q)) (diagonal_input_norm _ (weight_norm q h0 h1))

open scoped Matrix.Norms.L2Operator in
private theorem trace_norm_continuous {n : Type} [Fintype n] [DecidableEq n] :
    Continuous (traceNorm : Matrix n n ℂ → ℝ) := by
  have hgram : Continuous (fun A : Matrix n n ℂ => Aᴴ * A) := by fun_prop
  have hsqrt : Continuous (fun A : Matrix n n ℂ => CFC.sqrt (Aᴴ * A)) :=
    CFC.continuousOn_sqrt.comp_continuous hgram
      (fun A => (Matrix.posSemidef_conjTranspose_mul_self A).nonneg)
  unfold traceNorm
  change Continuous (fun A : Matrix n n ℂ => (CFC.sqrt (Aᴴ * A)).trace.re)
  have hentry (i : n) : Continuous (fun A : Matrix n n ℂ => CFC.sqrt (Aᴴ * A) i i) := by
    exact (continuous_apply i).comp ((continuous_apply i).comp hsqrt)
  unfold Matrix.trace
  fun_prop

section Actual
variable (ell beta gamma : ℝ) (w : Qubit → ℝ)
    (hl : 0 ≤ ell) (hu : ell ≤ 1) (hb : 0 < beta)
    (hw : ∀ j, 0 ≤ w j) (hmax : ∀ j, w j ≤ beta / (beta ^ 2 + gamma ^ 2))
    (Γ : Instrument)

private def decoded : QuantumChannel Qubit Output :=
  (receiverChannel (M := Qubit) (instrumentRealization Γ)).comp
    (sourceChannel ell beta gamma w hl hu hb hw hmax)

/-- The physical output branch for one input and one receiver output label. -/
def branchState (j k : Qubit) : Matrix Local Local ℂ :=
  (CStarMatrix.ofMatrix.symm (referenceState
    (decoded ell beta gamma w hl hu hb hw hmax Γ)
    (pureState (basisInput j) (basis_norm j))).1).submatrix
      (fun p => ((),(p.1,(k,p.2)))) (fun p => ((),(p.1,(k,p.2))))

private theorem branch_positive (j k : Qubit) :
    (branchState ell beta gamma w hl hu hb hw hmax Γ j k).PosSemidef := by
  let rho := referenceState (decoded ell beta gamma w hl hu hb hw hmax Γ)
    (pureState (basisInput j) (basis_norm j))
  have h : (CStarMatrix.ofMatrix.symm rho.1).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm rho.2.1)
  exact h.submatrix _

private theorem branch_entry (j k m n a b : Qubit) :
    branchState ell beta gamma w hl hu hb hw hmax Γ j k (m,a) (n,b) =
      ∑ s, Γ.operation k s (CStarMatrix.ofMatrix fun r t =>
        omega ell beta gamma (w j) (m,(s,r)) (n,(s,t))) a b := by
  change referenceAction (decoded ell beta gamma w hl hu hb hw hmax Γ)
    (pureState (basisInput j) (basis_norm j)).1 ((),(m,(k,a))) ((),(n,(k,b))) = _
  change referenceAction (receiverChannel (M := Qubit) (instrumentRealization Γ))
    (referenceAction (sourceChannel ell beta gamma w hl hu hb hw hmax)
      (pureState (basisInput j) (basis_norm j)).1) ((),(m,(k,a))) ((),(n,(k,b))) = _
  rw [PhaseBoundarySourceModel.receiver_reference, realization_entry, if_pos rfl]
  apply Finset.sum_congr rfl
  intro s _
  apply congrArg (fun X : CStarMatrix Qubit Qubit ℂ => Γ.operation k s X a b)
  ext r t
  simp only [CStarMatrix.ofMatrix_apply]
  rw [source_reference]
  simp [basisInput, pureState, Matrix.vecMulVec_apply, Pi.star_apply]

private theorem decoded_pure_entry {F : Type} [Fintype F] [DecidableEq F]
    (v : F × Qubit → ℂ) (hv : star v ⬝ᵥ v = 1)
    (f g : F) (m n k l a b : Qubit) :
    referenceAction (decoded ell beta gamma w hl hu hb hw hmax Γ)
      (pureState v hv).1 (f,(m,(k,a))) (g,(n,(l,b))) =
      if k = l then ∑ j, (v (f,j) * star (v (g,j))) *
        branchState ell beta gamma w hl hu hb hw hmax Γ j k (m,a) (n,b) else 0 := by
  change referenceAction (receiverChannel (M := Qubit) (instrumentRealization Γ))
    (referenceAction (sourceChannel ell beta gamma w hl hu hb hw hmax)
      (pureState v hv).1) (f,(m,(k,a))) (g,(n,(l,b))) = _
  rw [PhaseBoundarySourceModel.receiver_reference, realization_entry]
  split_ifs with hkl
  · have hBlock (s : Qubit) :
        (CStarMatrix.ofMatrix fun r t => referenceAction
          (sourceChannel ell beta gamma w hl hu hb hw hmax) (pureState v hv).1
          (f,(m,(s,r))) (g,(n,(s,t)))) =
        ∑ j, (v (f,j) * star (v (g,j))) •
          CStarMatrix.ofMatrix (fun r t => omega ell beta gamma (w j) (m,(s,r)) (n,(s,t))) := by
      ext r t
      simp only [CStarMatrix.ofMatrix_apply]
      rw [source_reference]
      simp [pureState, Matrix.vecMulVec_apply, Pi.star_apply, Matrix.sum_apply,
        CStarMatrix.smul_apply]
    simp only [CStarMatrix.ofMatrix_apply, hBlock, map_sum, map_smul, Matrix.sum_apply, CStarMatrix.smul_apply, smul_eq_mul]
    change (∑ s, ∑ j, (v (f,j) * star (v (g,j))) *
      Γ.operation k s (CStarMatrix.ofMatrix fun r t =>
        omega ell beta gamma (w j) (m,(s,r)) (n,(s,t))) a b) = _
    rw [Finset.sum_comm]
    simp_rw [branch_entry, Finset.mul_sum]
  · rfl

private theorem matched_entry (c : Qubit → ℂ) (hc : ∑ j, Complex.normSq (c j) = 1)
    (j k m n a b : Qubit) :
    matchedBlock ell beta gamma w hl hu hb hw hmax Γ c hc (j,(m,a)) (k,(n,b)) =
      (c j * star (c k)) * (xi ell (m,a) * star (xi ell (n,b))) -
      if j = k then (Complex.normSq (c j) : ℂ) *
        branchState ell beta gamma w hl hu hb hw hmax Γ j j (m,a) (n,b) else 0 := by
  change referenceAction (targetChannel ell hl hu)
    (pureState (diagonalInput c) (diagonal_input_norm c hc)).1
      (j,(m,(j,a))) (k,(n,(k,b))) -
    referenceAction (decoded ell beta gamma w hl hu hb hw hmax Γ)
    (pureState (diagonalInput c) (diagonal_input_norm c hc)).1
      (j,(m,(j,a))) (k,(n,(k,b))) = _
  rw [target_reference, decoded_pure_entry]
  by_cases hjk : j = k
  · subst k
    simp [pureState, Matrix.vecMulVec_apply, Pi.star_apply, diagonalInput,
      Complex.normSq_eq_conj_mul_self, Complex.star_def, mul_comm, mul_left_comm, mul_assoc]
  · simp [pureState, Matrix.vecMulVec_apply, Pi.star_apply, diagonalInput, hjk]
    ring

private theorem correct_label_order {F : Type} [Fintype F] [DecidableEq F] [Nonempty F]
    (v : F × Qubit → ℂ) (hv : star v ⬝ᵥ v = 1) :
    (controlledColumns v *
      matchedBlock ell beta gamma w hl hu hb hw hmax Γ (amplitude v) (amplitudes_normalized v hv) *
        (controlledColumns v)ᴴ -
      recoveryDifference ell beta gamma w hl hu hb hw hmax (instrumentRealization Γ)
        (pureState v hv)).PosSemidef := by
  let Q : Matrix (F × Output) (F × Output) ℂ := ∑ j, ∑ k,
    if j ≠ k then liftBranch v j k *
      branchState ell beta gamma w hl hu hb hw hmax Γ j k * (liftBranch v j k)ᴴ else 0
  have hQ : Q.PosSemidef := by
    apply Matrix.nonneg_iff_posSemidef.mp
    apply Finset.sum_nonneg
    intro j _
    apply Finset.sum_nonneg
    intro k _
    split_ifs
    · exact ((branch_positive ell beta gamma w hl hu hb hw hmax Γ j k).mul_mul_conjTranspose_same
        (liftBranch v j k)).nonneg
    · exact le_rfl
  have heq : controlledColumns v *
      matchedBlock ell beta gamma w hl hu hb hw hmax Γ (amplitude v) (amplitudes_normalized v hv) *
        (controlledColumns v)ᴴ -
      recoveryDifference ell beta gamma w hl hu hb hw hmax (instrumentRealization Γ)
        (pureState v hv) = Q := by
    ext ⟨f,m,k,a⟩ ⟨g,n,l,b⟩
    rw [Matrix.sub_apply, controlled_conjugation_entry, matched_entry]
    change _ - (referenceAction (targetChannel ell hl hu) (pureState v hv).1
      (f,(m,(k,a))) (g,(n,(l,b))) -
      referenceAction (decoded ell beta gamma w hl hu hb hw hmax Γ) (pureState v hv).1
      (f,(m,(k,a))) (g,(n,(l,b)))) = Q (f,(m,(k,a))) (g,(n,(l,b)))
    rw [target_reference, decoded_pure_entry]
    simp only [pureState, CStarMatrix.ofMatrix_apply, Matrix.vecMulVec_apply, Pi.star_apply]
    have hf (j : Qubit) : amplitude v j * normalizedColumn v j f = v (f,j) := column_factor v j f
    have hg (j : Qubit) : star (amplitude v j) * star (normalizedColumn v j g) = star (v (g,j)) :=
      by simpa only [star_mul, mul_comm] using congrArg star (column_factor v j g)
    have hc (j : Qubit) : (Complex.normSq (amplitude v j) : ℂ) =
        amplitude v j * star (amplitude v j) := by
      rw [Complex.normSq_eq_conj_mul_self, Complex.star_def, mul_comm]
    have ht : (normalizedColumn v k f * star (normalizedColumn v l g)) *
        ((amplitude v k * star (amplitude v l)) *
          (xi ell (m,a) * star (xi ell (n,b)))) =
        v (f,k) * star (v (g,l)) * xi ell (m,a) * star (xi ell (n,b)) := by
      calc
        _ = (amplitude v k * normalizedColumn v k f) *
          (star (amplitude v l) * star (normalizedColumn v l g)) *
          xi ell (m,a) * star (xi ell (n,b)) := by ring
        _ = _ := by rw [hf, hg]
    have hd (j : Qubit) (z : ℂ) :
        (normalizedColumn v j f * star (normalizedColumn v j g)) *
          ((amplitude v j * star (amplitude v j)) * z) =
        (v (f,j) * star (v (g,j))) * z := by
      calc
        _ = (amplitude v j * normalizedColumn v j f) *
          (star (amplitude v j) * star (normalizedColumn v j g)) * z := by ring
        _ = _ := by rw [hf, hg]
    simp only [mul_sub, ht]
    dsimp only [Q]
    simp only [Fin.sum_univ_two, Fin.isValue, ne_eq, Fin.reduceEq,
      if_true, if_false, not_true_eq_false, not_false_eq_true,
      Matrix.add_apply, Matrix.zero_apply, zero_add, add_zero]
    simp_rw [lift_branch_entry]
    fin_cases k <;> fin_cases l <;> simp [Fin.sum_univ_two, hc]
    all_goals simp only [starRingEnd_apply]
    all_goals first
      | linear_combination -(hd 0 (branchState ell beta gamma w hl hu hb hw hmax Γ 0 0 (m,a) (n,b)))
      | linear_combination -(hd 1 (branchState ell beta gamma w hl hu hb hw hmax Γ 1 1 (m,a) (n,b)))

  rwa [← heq] at hQ

/-- For one actual common instrument, every pure joint-reference input is
bounded by the canonical diagonal-edge test with the same input-label weights.
The controlled column map is used only in the spectral comparison. -/
theorem reference_error_diagonal_dominates {F : Type} [Fintype F] [DecidableEq F]
    (v : F × Qubit → ℂ) (hv : star v ⬝ᵥ v = 1) :
    ∃ (q : ℝ) (h0 : 0 ≤ q) (h1 : q ≤ 1),
      referenceError (targetChannel ell hl hu)
        (decoded ell beta gamma w hl hu hb hw hmax Γ) (pureState v hv) ≤
      referenceError (targetChannel ell hl hu)
        (decoded ell beta gamma w hl hu hb hw hmax Γ) (weightState q h0 h1) := by
  classical
  haveI : Nonempty F := by
    by_contra hn
    haveI : IsEmpty F := not_nonempty_iff.mp hn
    simpa [dotProduct] using hv
  let q := columnMass v 0
  have hsum : columnMass v 0 + columnMass v 1 = 1 := by
    have hh := amplitudes_normalized v hv
    simpa only [Fin.sum_univ_two, amplitude_square] using hh
  have h0 : 0 ≤ q := mass_nonnegative v 0
  have h1 : q ≤ 1 := by
    have hpos := mass_nonnegative v 1
    dsimp [q]
    linarith
  have hc : amplitude v = weightInput q := by
    funext j
    fin_cases j
    · rfl
    · simp only [weightInput, Fin.isValue, Fin.reduceEq, if_false, amplitude]
      congr 2
      dsimp [q]
      linarith
  let A := recoveryDifference ell beta gamma w hl hu hb hw hmax (instrumentRealization Γ)
    (pureState v hv)
  obtain ⟨hA,hE⟩ := pure_reference_error_eq_top_eigenvalue
    ell beta gamma w hl hu hb hw hmax (instrumentRealization Γ) v hv
  let C := matchedBlock ell beta gamma w hl hu hb hw hmax Γ
    (amplitude v) (amplitudes_normalized v hv)
  obtain ⟨hC,hL⟩ := matched_label_error_eq_top_eigenvalue
    ell beta gamma w hl hu hb hw hmax Γ (amplitude v) (amplitudes_normalized v hv)
  have hL0 : 0 ≤ referenceError (targetChannel ell hl hu)
      (decoded ell beta gamma w hl hu hb hw hmax Γ)
      (pureState (diagonalInput (amplitude v))
        (diagonal_input_norm (amplitude v) (amplitudes_normalized v hv))) / 2 :=
    div_nonneg (traceNorm_nonneg _) (by norm_num)
  have hle := spectral_domination A hA C hC (controlledColumns v) (controlled_isometry v)
    (correct_label_order ell beta gamma w hl hu hb hw hmax Γ v hv)
    _ _ hE.1 hL hL0
  change referenceError (targetChannel ell hl hu)
      (decoded ell beta gamma w hl hu hb hw hmax Γ) (pureState v hv) / 2 ≤
    referenceError (targetChannel ell hl hu)
      (decoded ell beta gamma w hl hu hb hw hmax Γ)
      (pureState (diagonalInput (amplitude v))
        (diagonal_input_norm (amplitude v) (amplitudes_normalized v hv))) / 2 at hle
  refine ⟨q,h0,h1,?_⟩
  have hh : referenceError (targetChannel ell hl hu)
      (decoded ell beta gamma w hl hu hb hw hmax Γ) (pureState v hv) ≤
    referenceError (targetChannel ell hl hu)
      (decoded ell beta gamma w hl hu hb hw hmax Γ)
      (pureState (diagonalInput (amplitude v))
        (diagonal_input_norm (amplitude v) (amplitudes_normalized v hv))) := by
    linarith
  simpa only [hc, weightState] using hh

/-- Complete-reference half diamond error is the supremum of the lawful
binary diagonal-edge tests for the same common instrument. -/
theorem diamond_eq_weight_sup :
    diamondDistance (targetChannel ell hl hu)
      (decoded ell beta gamma w hl hu hb hw hmax Γ) / 2 =
    sSup {x : ℝ | ∃ (q : ℝ) (h0 : 0 ≤ q) (h1 : q ≤ 1),
      x = referenceError (targetChannel ell hl hu)
        (decoded ell beta gamma w hl hu hb hw hmax Γ) (weightState q h0 h1) / 2} := by
  classical
  let T := targetChannel ell hl hu
  let D := decoded ell beta gamma w hl hu hb hw hmax Γ
  let S : Set ℝ := {x | ∃ (q : ℝ) (h0 : 0 ≤ q) (h1 : q ≤ 1),
    x = referenceError T D (weightState q h0 h1) / 2}
  have herr {F : Type} [Fintype F] [DecidableEq F] (rho : DensityState (F × Qubit)) :
      referenceError T D rho ≤ 2 := by
    have hh := traceDistance_le_one (referenceState T rho) (referenceState D rho)
    change referenceError T D rho / 2 ≤ 1 at hh
    linarith
  have hnonneg {F : Type} [Fintype F] [DecidableEq F] (rho : DensityState (F × Qubit)) :
      0 ≤ referenceError T D rho := traceNorm_nonneg _
  have hSbdd : BddAbove S := by
    refine ⟨1,?_⟩
    rintro x ⟨q,h0,h1,rfl⟩
    have hh := herr (weightState q h0 h1)
    linarith
  have hSmem : referenceError T D (weightState 0 (by norm_num) (by norm_num)) / 2 ∈ S :=
    ⟨0,by norm_num,by norm_num,rfl⟩
  have hSne : S.Nonempty := ⟨_,hSmem⟩
  have hSup0 : 0 ≤ sSup S :=
    (div_nonneg (hnonneg _) (by norm_num)).trans (le_csSup hSbdd hSmem)
  have hAllBdd : BddAbove ({0} ∪ {x : ℝ | ∃ n, ∃ rho : DensityState (Fin n × Qubit),
      x = referenceError T D rho}) := by
    refine ⟨2,?_⟩
    rintro x (hx | ⟨n,rho,rfl⟩)
    · have hx0 : x = 0 := hx
      rw [hx0]
      norm_num
    · exact herr rho
  have hUpper : diamondDistance T D ≤ 2 * sSup S := by
    apply csSup_le
    · exact ⟨0,Or.inl (Set.mem_singleton 0)⟩
    rintro x (hx | ⟨n,rho,rfl⟩)
    · have hx0 : x = 0 := hx
      rw [hx0]
      exact mul_nonneg (by norm_num) hSup0
    · obtain ⟨tau,⟨v,hv⟩,htau⟩ := (D5.S3.Quantum.Foundation.FiniteDiamondDistance.result T D).1 rho
      have hvnorm : star v ⬝ᵥ v = 1 := by
        have hh := tau.2.2
        rw [hv] at hh
        change (Matrix.vecMulVec v (star v)).trace = 1 at hh
        rwa [Matrix.trace_vecMulVec, dotProduct_comm] at hh
      have htaueq : tau = pureState v hvnorm := Subtype.ext hv
      obtain ⟨q,h0,h1,hq⟩ := reference_error_diagonal_dominates
        ell beta gamma w hl hu hb hw hmax Γ v hvnorm
      have hs := le_csSup hSbdd (show referenceError T D (weightState q h0 h1) / 2 ∈ S
        from ⟨q,h0,h1,rfl⟩)
      rw [htaueq] at htau
      change referenceError T D (pureState v hvnorm) ≤ referenceError T D (weightState q h0 h1) at hq
      linarith
  have hLower : sSup S ≤ diamondDistance T D / 2 := by
    apply csSup_le hSne
    rintro x ⟨q,h0,h1,rfl⟩
    have hh : referenceError T D (weightState q h0 h1) ≤ diamondDistance T D :=
      le_csSup hAllBdd (Or.inr ⟨2,weightState q h0 h1,rfl⟩)
    linarith
  change diamondDistance T D / 2 = sSup S
  apply le_antisymm _ hLower
  linarith

private theorem weight_error_continuous :
    Continuous (fun q : Set.Icc (0 : ℝ) 1 =>
      referenceError (targetChannel ell hl hu)
        (decoded ell beta gamma w hl hu hb hw hmax Γ)
        (weightState q.1 q.2.1 q.2.2) / 2) := by
  have hentry (p t : Qubit × Output) : Continuous (fun q : Set.Icc (0 : ℝ) 1 =>
      recoveryDifference ell beta gamma w hl hu hb hw hmax (instrumentRealization Γ)
        (weightState q.1 q.2.1 q.2.2) p t) := by
    rcases p with ⟨f,m,k,a⟩
    rcases t with ⟨g,n,l,b⟩
    change Continuous (fun q : Set.Icc (0 : ℝ) 1 =>
      referenceAction (targetChannel ell hl hu) (weightState q.1 q.2.1 q.2.2).1
        (f,(m,(k,a))) (g,(n,(l,b))) -
      referenceAction (decoded ell beta gamma w hl hu hb hw hmax Γ)
        (weightState q.1 q.2.1 q.2.2).1 (f,(m,(k,a))) (g,(n,(l,b))))
    simp only [weightState]
    simp_rw [target_reference, decoded_pure_entry]
    fin_cases f <;> fin_cases g <;> fin_cases k <;> fin_cases l <;>
      simp [pureState, CStarMatrix.ofMatrix_apply, Matrix.vecMulVec_apply, Pi.star_apply,
        diagonalInput, weightInput, Fin.sum_univ_two] <;> fun_prop
  have hmatrix := continuous_pi (fun p => continuous_pi (fun t => hentry p t))
  exact (trace_norm_continuous.comp hmatrix).div_const 2

/-- The binary weight supremum is attained, with no excluded endpoint. -/
theorem diamond_eq_weight_max :
    diamondDistance (targetChannel ell hl hu)
      (decoded ell beta gamma w hl hu hb hw hmax Γ) / 2 ∈
    {x : ℝ | ∃ (q : ℝ) (h0 : 0 ≤ q) (h1 : q ≤ 1),
      x = referenceError (targetChannel ell hl hu)
        (decoded ell beta gamma w hl hu hb hw hmax Γ) (weightState q h0 h1) / 2} := by
  let f : Set.Icc (0 : ℝ) 1 → ℝ := fun q => referenceError (targetChannel ell hl hu)
    (decoded ell beta gamma w hl hu hb hw hmax Γ) (weightState q.1 q.2.1 q.2.2) / 2
  have hf : Continuous f := weight_error_continuous ell beta gamma w hl hu hb hw hmax Γ
  have hcompact : IsCompact (Set.range f) := isCompact_range hf
  have hne : (Set.range f).Nonempty := ⟨f ⟨0,by norm_num,by norm_num⟩,
    ⟨⟨0,by norm_num,by norm_num⟩,rfl⟩⟩
  have hset : Set.range f = {x : ℝ | ∃ (q : ℝ) (h0 : 0 ≤ q) (h1 : q ≤ 1),
      x = referenceError (targetChannel ell hl hu)
        (decoded ell beta gamma w hl hu hb hw hmax Γ) (weightState q h0 h1) / 2} := by
    ext x
    constructor
    · rintro ⟨q,rfl⟩
      exact ⟨q.1,q.2.1,q.2.2,rfl⟩
    · rintro ⟨q,h0,h1,rfl⟩
      exact ⟨⟨q,h0,h1⟩,rfl⟩
  rw [diamond_eq_weight_sup, ← hset]
  exact hcompact.sSup_mem hne

/-- The full arbitrary-reference error is the maximum, over the lawful
binary weights, of the largest eigenvalue of the actual matched-label block. -/
theorem diamond_eq_matched_spectral_max :
    ∃ (q : ℝ) (h0 : 0 ≤ q) (h1 : q ≤ 1),
      ∃ hC : (matchedBlock ell beta gamma w hl hu hb hw hmax Γ
        (weightInput q) (weight_norm q h0 h1)).IsHermitian,
      IsGreatest (Set.range hC.eigenvalues)
        (diamondDistance (targetChannel ell hl hu)
          (decoded ell beta gamma w hl hu hb hw hmax Γ) / 2) ∧
      ∀ (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1),
        ∃ hT : (matchedBlock ell beta gamma w hl hu hb hw hmax Γ
          (weightInput t) (weight_norm t ht0 ht1)).IsHermitian,
        ∀ i, hT.eigenvalues i ≤ diamondDistance (targetChannel ell hl hu)
          (decoded ell beta gamma w hl hu hb hw hmax Γ) / 2 := by
  obtain ⟨q,h0,h1,heq⟩ := diamond_eq_weight_max ell beta gamma w hl hu hb hw hmax Γ
  obtain ⟨hC,hg⟩ := matched_label_error_eq_top_eigenvalue
    ell beta gamma w hl hu hb hw hmax Γ (weightInput q) (weight_norm q h0 h1)
  change IsGreatest (Set.range hC.eigenvalues)
    (referenceError (targetChannel ell hl hu)
      (decoded ell beta gamma w hl hu hb hw hmax Γ) (weightState q h0 h1) / 2) at hg
  refine ⟨q,h0,h1,hC,heq.symm ▸ hg,?_⟩
  intro t ht0 ht1
  obtain ⟨hT,hgT⟩ := matched_label_error_eq_top_eigenvalue
    ell beta gamma w hl hu hb hw hmax Γ (weightInput t) (weight_norm t ht0 ht1)
  refine ⟨hT,fun i => ?_⟩
  have hh := hgT.2 (show hT.eigenvalues i ∈ Set.range hT.eigenvalues from ⟨i,rfl⟩)
  change hT.eigenvalues i ≤ referenceError (targetChannel ell hl hu)
    (decoded ell beta gamma w hl hu hb hw hmax Γ) (weightState t ht0 ht1) / 2 at hh
  have hbd : BddAbove ({0} ∪ {x : ℝ | ∃ n, ∃ rho : DensityState (Fin n × Qubit),
      x = referenceError (targetChannel ell hl hu) (decoded ell beta gamma w hl hu hb hw hmax Γ) rho}) := by
    refine ⟨2,?_⟩
    rintro x (hx | ⟨n,rho,rfl⟩)
    · have hx0 : x = 0 := hx
      rw [hx0]
      norm_num
    · have h := traceDistance_le_one (referenceState (targetChannel ell hl hu) rho)
        (referenceState (decoded ell beta gamma w hl hu hb hw hmax Γ) rho)
      change referenceError (targetChannel ell hl hu) (decoded ell beta gamma w hl hu hb hw hmax Γ) rho / 2 ≤ 1 at h
      linarith
  have hscore : referenceError (targetChannel ell hl hu)
      (decoded ell beta gamma w hl hu hb hw hmax Γ) (weightState t ht0 ht1) ≤
      diamondDistance (targetChannel ell hl hu) (decoded ell beta gamma w hl hu hb hw hmax Γ) :=
    le_csSup hbd (Or.inr ⟨2,weightState t ht0 ht1,rfl⟩)
  linarith

end Actual
end D5.S3.Quantum.Recovery.PhaseBoundaryDiagonalReferenceReduction
