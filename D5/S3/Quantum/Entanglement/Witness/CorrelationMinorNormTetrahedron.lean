/- GID: D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormTetrahedron
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/Witness/CorrelationMinorNormTetrahedron
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual tetrahedral separable states and their full-order correlation minors. -/

import D5.S3.Quantum.Entanglement.Witness.CorrelationMinorNormGeometry

/-! Tetrahedral states from the Peled return note by Haobo Ma (Chrono AI,
Singapore) and Wenlin Zhang (NUS and Chrono AI, Singapore), CC BY 4.0.
The violations concern the extensions without FNF, not the original FNF theorems.
No existence theorem for arbitrary coherent pure designs is asserted. -/

set_option autoImplicit false
set_option linter.style.longLine false
noncomputable section
open Matrix Module
open scoped BigOperators ComplexOrder Kronecker MatrixOrder Matrix.Norms.L2Operator InnerProductSpace
open D5.S3.Quantum.Entanglement.Witness.CorrelationMinorNormFNFRefutation
open D5.S3.Quantum.Entanglement.Witness.CorrelationMinorNormGeometry
open D5.S3.Quantum.Information.ActualPureQubitCostInfimum
open D5.S3.Quantum.Information.SLDSpectralEnergy (IsDensity)
open D5.S3.Quantum.QuantumChannels.IptPptSquaredEquivalence (IsSeparable)
open D5.S3.Quantum.Information.PartialTraceMutualInformation

namespace D5.S3.Quantum.Entanglement.Witness.CorrelationMinorNormTetrahedron

/-- The four actual unit Bloch vectors (+++), (+--), (-+-), (--+). -/
def tetraVector (j : Fin 4) : EuclideanSpace ℝ (Fin 3) :=
  (Real.sqrt 3)⁻¹ • WithLp.toLp 2
    ((![![1,1,1], ![1,-1,-1], ![-1,1,-1], ![-1,-1,1]] : Fin 4 → Fin 3 → ℝ) j)

/-- Actual complex qubit projectors, using the existing Bloch reconstruction. -/
def tetraProjector (j : Fin 4) : Matrix (Fin 2) (Fin 2) ℂ :=
  blochMatrix 1 (tetraVector j)

private lemma sqrt_three_sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
private lemma sqrt_three_ne : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))

private lemma tetra_hermitian (j : Fin 4) : (tetraProjector j).IsHermitian := by
  change (tetraProjector j)ᴴ = tetraProjector j
  ext i k
  fin_cases j <;> fin_cases i <;> fin_cases k <;>
    simp [tetraProjector, blochMatrix, tetraVector, Matrix.conjTranspose_apply,
      star_div₀, star_sub, star_add, star_mul, Complex.star_def]
  all_goals ring

private lemma tetra_idempotent (j : Fin 4) :
    tetraProjector j * tetraProjector j = tetraProjector j := by
  ext i k
  fin_cases j <;> fin_cases i <;> fin_cases k <;> apply Complex.ext <;>
    simp [tetraProjector, blochMatrix, tetraVector, Matrix.mul_apply, Fin.sum_univ_two,
      Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]
  all_goals field_simp
  all_goals nlinarith [sqrt_three_sq]

/-- Each tetrahedral local object is a PSD trace-one idempotent. -/
theorem tetra_projector (j : Fin 4) :
    IsDensity (tetraProjector j) ∧ tetraProjector j * tetraProjector j = tetraProjector j := by
  refine ⟨⟨?_, ?_⟩, tetra_idempotent j⟩
  · have hp := Matrix.posSemidef_conjTranspose_mul_self (tetraProjector j)
    rwa [(tetra_hermitian j).eq, tetra_idempotent] at hp
  · exact blochMatrix_trace 1 (tetraVector j)

theorem tetra_sum : ∑ j, tetraProjector j = (2 : ℂ) • 1 := by
  ext i k
  fin_cases i <;> fin_cases k <;>
    simp [tetraProjector, blochMatrix, tetraVector, Fin.sum_univ_succ]
  all_goals ring

/-- The D-dimensional orthogonal flags used by the actual state. -/
def tetraFlag (D : ℕ) (hD : 4 ≤ D) (j : Fin 4) : Matrix (Fin D) (Fin D) ℂ :=
  single (j.castLE hD) (j.castLE hD) 1

/-- Four paired product states with white noise in the entire ambient space. -/
def omega (D : ℕ) (hD : 4 ≤ D) (t : ℝ) :
    Matrix (Fin 2 × Fin D) (Fin 2 × Fin D) ℂ :=
  (((1-t)/4 : ℝ) : ℂ) • (∑ j, tetraProjector j ⊗ₖ tetraFlag D hD j) +
    ((t/(2*D) : ℝ) : ℂ) • 1

private lemma flag_density (D : ℕ) (hD : 4 ≤ D) (j : Fin 4) :
    IsDensity (tetraFlag D hD j) := by
  refine ⟨?_, by simp [tetraFlag]⟩
  simpa only [tetraFlag, ← Pi.single_star, star_one,
    ← Matrix.single_eq_single_vecMulVec_single] using
    posSemidef_vecMulVec_self_star (Pi.single (j.castLE hD) (1 : ℂ))

private lemma mixed_density (n : ℕ) (hn : 0 < n) :
    IsDensity ((1/n : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) := by
  haveI : NeZero n := ⟨ne_of_gt hn⟩
  simpa [Matrix.trace_one] using D5.S3.Quantum.CotfasDVGS.normalization_isDensity
    (1 : Matrix (Fin n) (Fin n) ℂ) PosSemidef.one (by simp [NeZero.ne n])

/-- Separability uses precisely the finite normalized density decomposition. -/
theorem omega_separable (D : ℕ) (hD : 4 ≤ D) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    IsSeparable (omega D hD t) := by
  classical
  refine ⟨5, ![(1-t)/4, (1-t)/4, (1-t)/4, (1-t)/4, t],
    ![tetraProjector 0, tetraProjector 1, tetraProjector 2, tetraProjector 3, (1/2 : ℂ) • 1],
    ![tetraFlag D hD 0, tetraFlag D hD 1, tetraFlag D hD 2, tetraFlag D hD 3,
      (1/D : ℂ) • 1], ?_, ?_, ?_, ?_⟩
  · intro j
    fin_cases j <;> dsimp <;> positivity
  · simp only [Fin.sum_univ_succ, Fin.isValue, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero]
    ring
  · intro j
    fin_cases j
    · exact ⟨(tetra_projector 0).1, flag_density D hD 0⟩
    · exact ⟨(tetra_projector 1).1, flag_density D hD 1⟩
    · exact ⟨(tetra_projector 2).1, flag_density D hD 2⟩
    · exact ⟨(tetra_projector 3).1, flag_density D hD 3⟩
    · exact ⟨mixed_density 2 (by decide), mixed_density D (by omega)⟩
  · simp only [omega, Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Fin.sum_univ_zero, add_zero, smul_kronecker, kronecker_smul,
      one_kronecker_one, smul_smul, smul_add]
    push_cast
    module


private lemma alice_hermitian (i : Fin 4) : (alice i).IsHermitian :=
  (rational_noisy_family 0 (by norm_num) (by norm_num)).2.2.1.1 i

/-- Actual Bob operators whose real Hermitian coordinates are the correlation rows. -/
def rowSlice (D : ℕ) (hD : 4 ≤ D) (t : ℝ) (i : Fin 4) : Matrix (Fin D) (Fin D) ℂ :=
  (∑ j, ((((1-t)/4 * coordinates alice (tetraProjector j) i : ℝ) : ℂ)) • tetraFlag D hD j) +
    (((t/(2*D) * (alice i).trace.re : ℝ) : ℂ)) • 1

private lemma rowSlice_hermitian (D : ℕ) (hD : 4 ≤ D) (t : ℝ) (i : Fin 4) :
    (rowSlice D hD t i).IsHermitian := by
  change (rowSlice D hD t i)ᴴ = rowSlice D hD t i
  simp only [rowSlice, Matrix.conjTranspose_add, Matrix.conjTranspose_sum,
    Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal,
    Matrix.conjTranspose_one, (flag_density D hD _).1.isHermitian.eq]

/-- The row correspondence works in every complete normalized Bob basis. -/
theorem omega_correlation_rows (D : ℕ) (hD : 4 ≤ D) (t : ℝ)
    (b : Fin (D^2) → Matrix (Fin D) (Fin D) ℂ) (hb : IsHermBasis b)
    (i : Fin 4) (k : Fin (D^2)) :
    corr (omega D hD t) alice b i k = coordinates b (rowSlice D hD t i) k := by
  have hq (j : Fin 4) := hermitian_pair_real (tetraProjector j) (alice i)
    (tetra_projector j).1.1.isHermitian (alice_hermitian i)
  have hqi (j : Fin 4) : (tetraProjector j * alice i).trace.im = 0 := by
    have hh := congrArg Complex.im (hq j)
    simpa using hh.symm
  have ha := hermitian_pair_real (1 : Matrix (Fin 2) (Fin 2) ℂ) (alice i)
    Matrix.isHermitian_one (alice_hermitian i)
  have hai : (alice i).trace.im = 0 := by
    have hh := congrArg Complex.im ha
    simpa only [Matrix.one_mul, Complex.ofReal_im] using hh.symm
  simp only [corr, omega, coordinates, WithLp.ofLp_toLp, rowSlice,
    Matrix.add_mul, Matrix.smul_mul, Matrix.sum_mul, Matrix.trace_add,
    Matrix.trace_smul, Matrix.trace_sum, ← Matrix.mul_kronecker_mul,
    Matrix.trace_kronecker, Matrix.one_mul, smul_eq_mul,
    Complex.re_sum, Complex.add_re,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hqi, hai,
    zero_mul, mul_zero, sub_zero]
  congr 1
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  · ring

/-- The row Gram is basis independent because it is an actual Hermitian Parseval pairing. -/
theorem omega_gram_entry (D : ℕ) (hD : 4 ≤ D) (t : ℝ)
    (b : Fin (D^2) → Matrix (Fin D) (Fin D) ℂ) (hb : IsHermBasis b) (i k : Fin 4) :
    (corr (omega D hD t) alice b * (corr (omega D hD t) alice b).transpose) i k =
      (rowSlice D hD t i * rowSlice D hD t k).trace.re := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, omega_correlation_rows D hD t b hb]
  have hh := coordinates_inner b hb (rowSlice D hD t i) (rowSlice D hD t k)
    (rowSlice_hermitian D hD t i) (rowSlice_hermitian D hD t k)
  rw [EuclideanSpace.inner_eq_star_dotProduct] at hh
  simpa only [star_trivial, dotProduct, mul_comm] using hh

private lemma flag_pair (D : ℕ) (hD : 4 ≤ D) (j k : Fin 4) :
    (tetraFlag D hD j * tetraFlag D hD k).trace = if j = k then 1 else 0 := by
  simp [tetraFlag, Matrix.trace_single_mul, Matrix.single_apply, eq_comm]


private def coordSigns : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1,1,1,1; 1,-1,-1,1; 1,1,-1,-1; 1,-1,1,-1]

private lemma tetra_coordinate (j i : Fin 4) :
    coordinates alice (tetraProjector j) i =
      coordSigns i j / (Real.sqrt 2 * (if i = 0 then 1 else Real.sqrt 3)) := by
  fin_cases i <;> fin_cases j <;>
    simp [coordinates, alice, tetraProjector, blochMatrix, tetraVector, coordSigns,
      D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.pauliMatrix,
      D5.S3.Quantum.FiniteDimensional.qubitX, D5.S3.Quantum.FiniteDimensional.qubitZ,
      Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two, Complex.mul_re, Complex.mul_im]
  all_goals field_simp
  all_goals ring_nf
  all_goals simp only [sqrt_three_sq, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  all_goals ring

private lemma alice_trace (i : Fin 4) : (alice i).trace =
    if i = 0 then 2 / (Real.sqrt 2 : ℂ) else 0 := by
  fin_cases i <;>
    simp [alice, Matrix.trace_smul,
      D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.pauliMatrix,
      D5.S3.Quantum.FiniteDimensional.qubitX, D5.S3.Quantum.FiniteDimensional.qubitZ,
      Matrix.trace, Fin.sum_univ_two]
  ring


private lemma alice_trace_real (i : Fin 4) : (alice i).trace.re =
    if i = 0 then 2 / Real.sqrt 2 else 0 := by
  rw [alice_trace]
  split_ifs <;> simp [← Complex.ofReal_div]

private lemma flag_sum_trace (D : ℕ) (hD : 4 ≤ D)
    (f g : Fin 4 → ℝ) (u v : ℝ) :
    (((∑ j, (f j : ℂ) • tetraFlag D hD j) + (u : ℂ) • 1) *
      ((∑ j, (g j : ℂ) • tetraFlag D hD j) + (v : ℂ) • 1)).trace.re =
      (∑ j, f j * g j) + v * (∑ j, f j) + u * (∑ j, g j) + (D : ℝ)*u*v := by
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sum_mul,
    Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
    Matrix.trace_add, Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul,
    flag_pair, (flag_density D hD _).2, Matrix.trace_one, Fintype.card_fin]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    ← Complex.ofReal_natCast, ← Complex.ofReal_mul, ← Complex.ofReal_add,
    ← Complex.ofReal_sum, Complex.ofReal_re]
  simp only [Fin.sum_univ_succ]
  ring

/-- The identity-row Gram coefficient. -/
def q0 (D : ℕ) (t : ℝ) : ℝ := (1-t)^2/8 + (2*t-t^2)/(2*D)
/-- The three equal traceless-row Gram coefficients. -/
def q1 (t : ℝ) : ℝ := (1-t)^2/24

/-- The exact row Gram in normalized Pauli / arbitrary normalized Bob coordinates. -/
theorem omega_gram (D : ℕ) (hD : 4 ≤ D) (t : ℝ)
    (b : Fin (D^2) → Matrix (Fin D) (Fin D) ℂ) (hb : IsHermBasis b) :
    corr (omega D hD t) alice b * (corr (omega D hD t) alice b).transpose =
      Matrix.diagonal (![q0 D t, q1 t, q1 t, q1 t] : Fin 4 → ℝ) := by
  have hD0 : (D : ℝ) ≠ 0 := by exact_mod_cast (by omega : D ≠ 0)
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs24 : Real.sqrt 2 ^ 4 = 4 := by
    calc
      _ = (Real.sqrt 2 ^ 2)^2 := by ring
      _ = 4 := by rw [hs2]; norm_num
  ext i k
  rw [omega_gram_entry D hD t b hb]
  unfold rowSlice
  rw [flag_sum_trace]
  simp only [tetra_coordinate, alice_trace_real]
  fin_cases i <;> fin_cases k <;>
    simp [coordSigns, Fin.sum_univ_succ, Matrix.diagonal_apply, q0, q1,
      Complex.mul_re, Complex.mul_im]
  all_goals field_simp
  all_goals ring_nf
  all_goals simp only [hs2, hs24, sqrt_three_sq]
  all_goals ring

/-- These are actual density matrices for the entire convex noise interval. -/
theorem omega_density (D : ℕ) (hD : 4 ≤ D) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    IsDensity (omega D hD t) :=
  separable_density _ (omega_separable D hD t ht0 ht1)

/-- White noise gives the PSD lower bound and positive definiteness away from zero. -/
theorem omega_noise (D : ℕ) (hD : 4 ≤ D) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (omega D hD t - ((t/(2*D) : ℝ) : ℂ) • 1).PosSemidef ∧
    (0 < t → (omega D hD t).PosDef) := by
  have heq : omega D hD t - ((t/(2*D) : ℝ) : ℂ) • 1 =
      ((1-t : ℝ) : ℂ) • omega D hD 0 := by
    simp [omega, smul_smul]
    module
  have hl : (omega D hD t - ((t/(2*D) : ℝ) : ℂ) • 1).PosSemidef := by
    rw [heq]
    exact (omega_density D hD 0 (by norm_num) (by norm_num)).1.smul
      (Complex.zero_le_real.mpr (sub_nonneg.mpr ht1))
  refine ⟨hl, ?_⟩
  intro ht
  have hDp : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  have hp : ((((t/(2*D) : ℝ) : ℂ)) •
      (1 : Matrix (Fin 2 × Fin D) (Fin 2 × Fin D) ℂ)).PosDef :=
    Matrix.PosDef.one.smul (Complex.zero_lt_real.mpr (by positivity))
  convert hp.posSemidef_add hl using 1 <;> abel

private lemma partial_left_linear {da db v : ℕ} (w : Fin v → ℂ)
    (M : Fin v → Matrix (Fin da × Fin db) (Fin da × Fin db) ℂ) :
    partialTraceLeft (∑ j, w j • M j) = ∑ j, w j • partialTraceLeft (M j) := by
  ext i k
  simp only [partialTraceLeft, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  simp [Finset.mul_sum]

private lemma partial_right_linear {da db v : ℕ} (w : Fin v → ℂ)
    (M : Fin v → Matrix (Fin da × Fin db) (Fin da × Fin db) ℂ) :
    partialTraceRight (∑ j, w j • M j) = ∑ j, w j • partialTraceRight (M j) := by
  ext i k
  simp only [partialTraceRight, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  simp [Finset.mul_sum]

private lemma partial_left_smul {da db : ℕ} (w : ℂ)
    (M : Matrix (Fin da × Fin db) (Fin da × Fin db) ℂ) :
    partialTraceLeft (w • M) = w • partialTraceLeft M := by
  ext i k
  simp [partialTraceLeft, Finset.mul_sum]

private lemma partial_right_smul {da db : ℕ} (w : ℂ)
    (M : Matrix (Fin da × Fin db) (Fin da × Fin db) ℂ) :
    partialTraceRight (w • M) = w • partialTraceRight M := by
  ext i k
  simp [partialTraceRight, Finset.mul_sum]

private lemma partial_left_tensor {da db : ℕ}
    (A : Matrix (Fin da) (Fin da) ℂ) (B : Matrix (Fin db) (Fin db) ℂ) :
    partialTraceLeft (A ⊗ₖ B) = A.trace • B := partialTraceLeft_kronecker A B

private lemma partial_right_tensor {da db : ℕ}
    (A : Matrix (Fin da) (Fin da) ℂ) (B : Matrix (Fin db) (Fin db) ℂ) :
    partialTraceRight (A ⊗ₖ B) = B.trace • A := partialTraceRight_kronecker A B

/-- Exact marginals; Left retains Bob and Right retains Alice. -/
theorem omega_marginals (D : ℕ) (hD : 4 ≤ D) (t : ℝ) :
    partialTraceRight (omega D hD t) = (1/2 : ℂ) • 1 ∧
    partialTraceLeft (omega D hD t) =
      (((1-t)/4 : ℝ) : ℂ) • (∑ j, tetraFlag D hD j) + ((t/D : ℝ) : ℂ) • 1 := by
  have hD0 : (D : ℂ) ≠ 0 := by exact_mod_cast (by omega : D ≠ 0)
  have hl1 : partialTraceLeft (1 : Matrix (Fin 2 × Fin D) (Fin 2 × Fin D) ℂ) = (2 : ℂ) • 1 := by
    rw [← Matrix.one_kronecker_one, partial_left_tensor]
    simp
  have hr1 : partialTraceRight (1 : Matrix (Fin 2 × Fin D) (Fin 2 × Fin D) ℂ) = (D : ℂ) • 1 := by
    rw [← Matrix.one_kronecker_one, partial_right_tensor]
    simp
  have hl : partialTraceLeft (∑ j, tetraProjector j ⊗ₖ tetraFlag D hD j) =
      ∑ j, tetraFlag D hD j := by
    rw [show (∑ j, tetraProjector j ⊗ₖ tetraFlag D hD j) =
      ∑ j, (1:ℂ) • (tetraProjector j ⊗ₖ tetraFlag D hD j) by simp,
      partial_left_linear]
    simp only [partial_left_tensor, (tetra_projector _).1.2, one_smul]
  have hr : partialTraceRight (∑ j, tetraProjector j ⊗ₖ tetraFlag D hD j) =
      (2:ℂ) • 1 := by
    rw [show (∑ j, tetraProjector j ⊗ₖ tetraFlag D hD j) =
      ∑ j, (1:ℂ) • (tetraProjector j ⊗ₖ tetraFlag D hD j) by simp,
      partial_right_linear]
    simp only [partial_right_tensor, (flag_density D hD _).2, one_smul, tetra_sum]
  constructor
  · rw [omega, partialTraceRight_add, partial_right_smul, partial_right_smul, hr, hr1,
      smul_smul, smul_smul, ← add_smul]
    congr 1
    push_cast
    field_simp
    ring
  · rw [omega, partialTraceLeft_add, partial_left_smul, partial_left_smul, hl, hl1, smul_smul]
    congr 2
    push_cast
    field_simp

/-- At D>4 a flag outside the occupied four positions excludes FNF whenever t<1. -/
theorem omega_not_fnf (D : ℕ) (hD : 5 ≤ D) (t : ℝ) (ht : t < 1) :
    partialTraceLeft (omega D (by omega) t) ≠ (1/D : ℂ) • 1 := by
  intro he
  let k : Fin D := ⟨4, by omega⟩
  have hx := congrArg (fun M : Matrix (Fin D) (Fin D) ℂ => (M k k).re) he
  rw [(omega_marginals D (by omega) t).2] at hx
  have hne (j : Fin 4) : j.castLE (by omega : 4 ≤ D) ≠ k := by
    intro hh
    have hh' := congrArg Fin.val hh
    have hj := j.isLt
    dsimp [k] at hh'
    omega
  have hflag : (∑ j, tetraFlag D (by omega) j) k k = 0 := by
    simp only [Matrix.sum_apply, tetraFlag, Matrix.single_apply]
    exact Finset.sum_eq_zero (fun j _ => if_neg (fun h => hne j h.1))
  simp only [Matrix.add_apply, Matrix.smul_apply, hflag, Matrix.one_apply_eq,
    smul_eq_mul, mul_zero, add_zero, mul_one] at hx
  have hDp : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  have hx' : t / (D:ℝ) = 1 / (D:ℝ) := by simpa [← Complex.ofReal_div, ← Complex.ofReal_natCast] using hx
  have : t = 1 := (div_left_inj' (ne_of_gt hDp)).mp hx'
  linarith

/-- Every Schatten norm of the actual full-order increasing compound is the
same row-Gram determinant, in arbitrary complete normalized local bases. -/
theorem omega_full_norms (D : ℕ) (hD : 4 ≤ D) (t : ℝ)
    (a : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ) (ha : IsHermBasis a)
    (b : Fin (D^2) → Matrix (Fin D) (Fin D) ℂ) (hb : IsHermBasis b) :
    cmnInf 4 (corr (omega D hD t) a b) = Real.sqrt (q0 D t * q1 t ^ 3) ∧
    ∀ p : ℝ, 1 ≤ p → cmnP p 4 (corr (omega D hD t) a b) =
      Real.sqrt (q0 D t * q1 t ^ 3) := by
  have halice : IsHermBasis alice :=
    (rational_noisy_family 0 (by norm_num) (by norm_num)).2.2.1
  have hi := full_order_basisChange_left (omega D hD t) alice a b halice ha
  norm_num only [Nat.reducePow] at hi
  have hd : (corr (omega D hD t) alice b *
      (corr (omega D hD t) alice b).transpose).det = q0 D t * q1 t ^ 3 := by
    rw [omega_gram D hD t b hb, Matrix.det_diagonal]
    simp [Fin.prod_univ_succ, pow_succ, mul_assoc]
  constructor
  · rw [hi.1, (full_order_norms (corr (omega D hD t) alice b)).1, hd]
  · intro p hp
    rw [hi.2 p hp, (full_order_norms (corr (omega D hD t) alice b)).2 p hp, hd]

/-- The common squared fourth-order proposed endpoint threshold. -/
def fourthThresholdSquared (D : ℕ) : ℝ := ((D:ℝ)-1)^3 / (11664*(D:ℝ)^4)

/-- Original normalized alpha and beta give the same fourth-order endpoint. -/
def fourthThreshold (D : ℕ) : ℝ :=
  1 / Real.sqrt (2*D) * (Real.sqrt (((D:ℝ)-1)/(18*D)))^3

lemma fourthThreshold_sq (D : ℕ) (hD : 2 ≤ D) :
    fourthThreshold D ^ 2 = fourthThresholdSquared D := by
  have hd : (0:ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  have hd2 : (2:ℝ) ≤ D := by exact_mod_cast hD
  have hpos : 0 ≤ ((D:ℝ)-1)/(18*D) := div_nonneg (by linarith) (by positivity)
  rw [fourthThreshold, mul_pow, div_pow, one_pow,
    Real.sq_sqrt (by positivity : (0:ℝ) ≤ 2*D),
    show (Real.sqrt (((D:ℝ)-1)/(18*D))^3)^2 =
      (Real.sqrt (((D:ℝ)-1)/(18*D))^2)^3 by ring,
    Real.sq_sqrt hpos]
  unfold fourthThresholdSquared
  field_simp
  ring

lemma tetra_energy_lower (D : ℕ) (hD : 4 ≤ D) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1-t)^8/110592 ≤ q0 D t * q1 t ^ 3 := by
  have hd : (0:ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  have htail : 0 ≤ (2*t-t^2)/(2*D) := by
    apply div_nonneg _ (by positivity)
    nlinarith
  have hq : (1-t)^2/8 ≤ q0 D t := by unfold q0; linarith
  have hm := mul_le_mul_of_nonneg_right hq (show 0 ≤ q1 t ^ 3 by unfold q1; positivity)
  calc
    _ = ((1-t)^2/8) * q1 t ^ 3 := by unfold q1; ring
    _ ≤ _ := hm

/-- Uniform strictness on the entire real noise interval and every admissible
integer dimension. The finite dimension split does not discretize noise. -/
theorem tetra_uniform_violation (D : ℕ) (hD5 : 5 ≤ D) (hD8 : D ≤ 8)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1/1000) :
    0 < q0 D t * q1 t ^ 3 ∧
    fourthThresholdSquared D < q0 D t * q1 t ^ 3 := by
  have hl := tetra_energy_lower D (by omega) t ht0 (by linarith)
  have hp : (999/1000:ℝ)^8 ≤ (1-t)^8 :=
    pow_le_pow_left₀ (by norm_num) (by linarith) 8
  have hb : fourthThresholdSquared D < (999/1000:ℝ)^8/110592 := by
    interval_cases D <;> norm_num [fourthThresholdSquared]
  have hpos : (0:ℝ) < (999/1000:ℝ)^8/110592 := by norm_num
  constructor <;> linarith

/-- The source's original Theorem 3 fourth-order expression equals alpha beta³,
which is also Theorem 1's full qubit-side elementary symmetric polynomial. -/
theorem fourthThreshold_eq_bound (D : ℕ) (hD : 2 ≤ D) :
    fourthThreshold D = bound 2 D 4 := by
  have hd : (0:ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  have hd2 : (2:ℝ) ≤ D := by exact_mod_cast hD
  have hp : 0 ≤ ((D:ℝ)-1)/(18*D) := div_nonneg (by linarith) (by positivity)
  have he : ((D:ℝ)-1)/((D:ℝ)*3) * (1/6:ℝ) = ((D:ℝ)-1)/(18*D) := by
    field_simp; ring
  unfold bound fourthThreshold
  simp only [max_eq_right hd2, min_eq_left hd2, Nat.cast_ofNat]
  norm_num only [Nat.cast_ofNat, show (4:ℝ)-1=3 by norm_num]
  rw [he, Real.rpow_div_two_eq_sqrt 3 hp]
  simp only [Real.rpow_ofNat, mul_comm (D:ℝ) 2]

private lemma positive_rank_of_trace_ne_zero (P : Matrix (Fin 2) (Fin 2) ℂ)
    (hP : P.trace ≠ 0) : 0 < P.rank := by
  by_contra hn
  have hz : Module.finrank ℂ P.mulVecLin.range = 0 := Nat.eq_zero_of_not_pos hn
  have hr : P.mulVecLin.range = ⊥ := Submodule.finrank_eq_zero.mp hz
  have hm : P.mulVecLin = 0 := LinearMap.range_eq_bot.mp hr
  have hp : P = 0 := by
    ext i j
    have hh := LinearMap.congr_fun hm (Pi.single j 1)
    have hhi := congrFun hh i
    simpa [Matrix.mulVecLin_apply, Matrix.mulVec_single_one] using hhi
  exact hP (by rw [hp, Matrix.trace_zero])

private lemma fourthThreshold_eq_primary_p1 (D : ℕ) (hD : 2 ≤ D) :
    (∑ S ∈ (Finset.univ : Finset (Fin 4)).powersetCard 4,
      ∏ i ∈ S, if i = 0 then (1/Real.sqrt (2*D : ℝ))
        else Real.sqrt ((((D:ℝ)-1)/D)*(1/2:ℝ))/3) = fourthThreshold D := by
  have hd : (0:ℝ) < D := by exact_mod_cast (by omega : 0<D)
  have hd2 : (2:ℝ) ≤ D := by exact_mod_cast hD
  have hn : 0 ≤ (D:ℝ)-1 := by linarith
  have ha : 0 ≤ (((D:ℝ)-1)/D)*(1/2:ℝ) :=
    mul_nonneg (div_nonneg hn hd.le) (by norm_num)
  have hb : 0 ≤ ((D:ℝ)-1)/(18*D) := div_nonneg hn (by positivity)
  have he : Real.sqrt ((((D:ℝ)-1)/D)*(1/2:ℝ))/3 =
      Real.sqrt (((D:ℝ)-1)/(18*D)) := by
    have hsA := Real.sq_sqrt ha
    have hsB := Real.sq_sqrt hb
    have hq : ((((D:ℝ)-1)/D)*(1/2:ℝ))/9 = ((D:ℝ)-1)/(18*D) := by field_simp; ring
    nlinarith [Real.sqrt_nonneg ((((D:ℝ)-1)/D)*(1/2:ℝ)),
      Real.sqrt_nonneg (((D:ℝ)-1)/(18*D))]
  have hp : (Finset.univ : Finset (Fin 4)).powersetCard 4 = {Finset.univ} := by decide
  simp only [hp,Finset.sum_singleton]
  simp_rw [he]
  simp [Fin.prod_univ_succ,fourthThreshold,pow_succ,mul_assoc]
  left
  ring

private lemma tetra_uniform_margin (D : ℕ) (hD5 : 5 ≤ D) (hD8 : D ≤ 8)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1/1000) :
    (4185/4096:ℝ)*fourthThresholdSquared D ≤ q0 D t * q1 t ^ 3 := by
  have hl := tetra_energy_lower D (by omega) t ht0 (by linarith)
  have hp : (999/1000:ℝ)^8 ≤ (1-t)^8 :=
    pow_le_pow_left₀ (by norm_num) (by linarith) 8
  have hb : (4185/4096:ℝ)*fourthThresholdSquared D ≤ (999/1000:ℝ)^8/110592 := by
    interval_cases D <;> norm_num [fourthThresholdSquared]
  linarith

/-- Actual noisy states violate the common fourth-order endpoint in every
Schatten norm. Both original dimension ranges hold; FNF is absent. -/
theorem tetrahedral_family (D : ℕ) (hD5 : 5 ≤ D) (hD8 : D ≤ 8)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1/1000)
    (a : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ) (ha : IsHermBasis a)
    (b : Fin (D^2) → Matrix (Fin D) (Fin D) ℂ) (hb : IsHermBasis b) :
    IsSeparable (omega D (by omega) t) ∧ IsDensity (omega D (by omega) t) ∧
    partialTraceLeft (omega D (by omega) t) ≠ (1/D : ℂ) • 1 ∧
    2*D ≤ 4^2 ∧ D ≤ 2^3 ∧
    fourthThreshold D < cmnInf 4 (corr (omega D (by omega) t) a b) ∧
    (∀ p : ℝ, 1 ≤ p → fourthThreshold D < cmnP p 4 (corr (omega D (by omega) t) a b)) ∧
    bound 2 D 4 < cmnInf 4 (corr (omega D (by omega) t) a b) ∧
    (∑ S ∈ (Finset.univ : Finset (Fin 4)).powersetCard 4,
      ∏ i ∈ S, if i = 0 then (1/Real.sqrt (2*D : ℝ))
        else Real.sqrt ((((D:ℝ)-1)/D)*(1/2:ℝ))/3) <
      cmnP 1 4 (corr (omega D (by omega) t) a b) ∧
    (4185/4096:ℝ)*fourthThresholdSquared D ≤
      cmnInf 4 (corr (omega D (by omega) t) a b)^2 ∧
    ∀ p : ℝ, 1 ≤ p → (4185/4096:ℝ)*fourthThresholdSquared D ≤
      cmnP p 4 (corr (omega D (by omega) t) a b)^2 := by
  have hn := omega_full_norms D (by omega) t a ha b hb
  have hv := tetra_uniform_violation D hD5 hD8 t ht0 ht1
  have hs := Real.sq_sqrt (le_of_lt hv.1)
  have hb0 : 0 ≤ fourthThreshold D := by unfold fourthThreshold; positivity
  have hstrict : fourthThreshold D < Real.sqrt (q0 D t * q1 t ^ 3) := by
    have he := fourthThreshold_sq D (by omega)
    nlinarith [Real.sqrt_nonneg (q0 D t * q1 t ^ 3)]
  refine ⟨omega_separable D (by omega) t ht0 (by linarith),
    omega_density D (by omega) t ht0 (by linarith),
    omega_not_fnf D hD5 t (by linarith), by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hn.1]; exact hstrict
  · intro p hp; rw [hn.2 p hp]; exact hstrict
  · rw [← fourthThreshold_eq_bound D (by omega),hn.1]; exact hstrict
  · rw [fourthThreshold_eq_primary_p1 D (by omega),hn.2 1 le_rfl]; exact hstrict
  · rw [hn.1,hs]; exact tetra_uniform_margin D hD5 hD8 t ht0 ht1
  · intro p hp
    rw [hn.2 p hp,hs]; exact tetra_uniform_margin D hD5 hD8 t ht0 ht1

/-- Every D≥4 realizes the unrestricted fourth-order constant at zero noise. -/
theorem tetra_attainment (D : ℕ) (hD : 4 ≤ D)
    (a : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ) (ha : IsHermBasis a)
    (b : Fin (D^2) → Matrix (Fin D) (Fin D) ℂ) (hb : IsHermBasis b) :
    cmnInf 4 (corr (omega D hD 0) a b) = 1/(192*Real.sqrt 3) ∧
    ∀ p : ℝ, 1 ≤ p → cmnP p 4 (corr (omega D hD 0) a b) = 1/(192*Real.sqrt 3) := by
  have hn := omega_full_norms D hD 0 a ha b hb
  have he : Real.sqrt (q0 D 0 * q1 0 ^ 3) = 1/(192*Real.sqrt 3) := by
    have hqe : q0 D 0 * q1 0 ^ 3 = (1/110592:ℝ) := by norm_num [q0, q1]
    rw [hqe]
    have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 1/110592)
    have hb : (1/(192*Real.sqrt 3))^2 = (1/110592:ℝ) := by
      norm_num [div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
    nlinarith [Real.sqrt_nonneg (1/110592:ℝ),
      show 0 < 1/(192*Real.sqrt 3) by positivity]
  simpa only [he] using hn


/-- The actual four tetrahedral local density projectors have rank one. -/
theorem tetra_rank_one (j : Fin 4) : (tetraProjector j).rank = 1 := by
  have ht := (tetra_projector j).1.2
  have hp : 0 < (tetraProjector j).rank := positive_rank_of_trace_ne_zero _ (by rw [ht]; norm_num)
  have hq : 0 < (1-tetraProjector j).rank := positive_rank_of_trace_ne_zero _ (by
    rw [Matrix.trace_sub, Matrix.trace_one, ht]
    norm_num)
  have hz : tetraProjector j * (1-tetraProjector j) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, tetra_idempotent, sub_self]
  have hh := Matrix.rank_add_rank_le_card_of_mul_eq_zero hz
  norm_num only [Fintype.card_fin] at hh
  omega

end D5.S3.Quantum.Entanglement.Witness.CorrelationMinorNormTetrahedron
