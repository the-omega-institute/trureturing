/- GID: D5/S3/Quantum/Information/GeometricDiscordMutualCorrelationBound
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/GeometricDiscordMutualCorrelationBound
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Maximal mutual correlation bounds the square root of normalized geometric discord. -/

import D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH
import D5.S3.Quantum.Tomography.RankOneContextCommutator

/-! The normalized Hilbert–Schmidt discord is bounded by connected local correlations. -/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Kronecker ComplexOrder Matrix.Norms.L2Operator
open D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction
  (pauli blochA blochB corr vlen trace_mul_kron_one)
open D5.S3.QuantumChannels.PauliThreeWeightBayesianInverseUniqueness (sigma spin)
open D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH
  (normalized_unit vlen_sq trace_pauli_kronecker_eq_corr)
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.FiniteDimensional (qubitX qubitZ)
open D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence (pauliMatrix)
open D5.S3.Quantum.Tomography.RankOneContextCommutator (hilbertSchmidtSquare)
open D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics (unitaryEvolution)
open D5.S3.Observer.Conditioning (unreadState)

namespace D5.S3.Quantum.Information.GeometricDiscordMutualCorrelationBound

local notation "Qubit" => Matrix (Fin 2) (Fin 2) ℂ
local notation "TwoQubit" => Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ

/-- The nonselective rank-one projective measurement of the first qubit in the columns of U. -/
def measuredState (U : Qubit) (ρ : TwoQubit) : TwoQubit :=
  unreadState (fun k : Fin 2 => (U * Matrix.single k k 1 * Uᴴ) ⊗ₖ (1 : Qubit)) ρ

/-- Normalized geometric discord, with projective measurements on A and normalization two. -/
def geometricDiscord (ρ : TwoQubit) : ℝ :=
  2 * sInf ((fun U => hilbertSchmidtSquare (ρ - measuredState U ρ)) ''
    (Matrix.unitaryGroup (Fin 2) ℂ : Set Qubit))

/-- The covariance of elements from the two commuting local algebras. -/
def localCovariance (ρ : TwoQubit) (a b : Qubit) : ℂ :=
  trace (ρ * (a ⊗ₖ b)) -
    trace (ρ * (a ⊗ₖ (1 : Qubit))) * trace (ρ * ((1 : Qubit) ⊗ₖ b))

/-- Maximal mutual correlation over the unit spheres of the two local operator algebras. -/
def maximalMutualCorrelation (ρ : TwoQubit) : ℝ :=
  sSup {r | ∃ a b : Qubit, ‖a‖ = 1 ∧ ‖b‖ = 1 ∧
    r = ‖localCovariance ρ a b‖}

/-- The connected Pauli correlation matrix. -/
def connectedCorrelation (ρ : TwoQubit) (i j : Fin 3) : ℝ :=
  corr ρ i j - blochA ρ i * blochB ρ j

/-- The first inequality in Eq. (II.23) of Gwóźdź–Jakóbczyk, for all two-qubit states. -/
def claim : Prop :=
  ∀ ρ : TwoQubit, ρ.PosSemidef → trace ρ = 1 →
    Real.sqrt (geometricDiscord ρ) ≤ maximalMutualCorrelation ρ

private lemma density_expectation_bound {n : Type*} [Fintype n] [DecidableEq n]
    (ρ X : Matrix n n ℂ) (hρ : ρ.PosSemidef) (ht : trace ρ = 1) :
    ‖trace (ρ * X)‖ ≤ ‖X‖ := by
  let U := hρ.isHermitian.eigenvectorUnitary
  let Y := (U : Matrix n n ℂ)ᴴ * X * U
  have hy : ‖Y‖ = ‖X‖ := by
    change ‖((star U : Matrix.unitaryGroup n ℂ) : Matrix n n ℂ) * X *
      (U : Matrix n n ℂ)‖ = ‖X‖
    rw [CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul]
  have he : trace (ρ * X) = ∑ i, (hρ.isHermitian.eigenvalues i : ℂ) * Y i i := by
    conv_lhs => rw [hρ.isHermitian.spectral_theorem]
    simp only [Unitary.conjStarAlgAut_apply]
    rw [Matrix.mul_assoc, trace_mul_comm, ← Matrix.mul_assoc,
      trace_mul_cycle]
    simp only [Y, U, Matrix.mul_assoc, Matrix.trace, Matrix.diag, Matrix.diagonal_mul,
      Function.comp_apply, RCLike.ofReal_eq_complex_ofReal, ← Matrix.star_eq_conjTranspose]
  have hs : ∑ i, hρ.isHermitian.eigenvalues i = 1 := by
    have hh := congrArg Complex.re hρ.isHermitian.trace_eq_sum_eigenvalues
    rw [ht] at hh
    simpa only [Complex.re_sum, RCLike.ofReal_eq_complex_ofReal,
      Complex.ofReal_re, Complex.one_re] using hh.symm
  rw [he]
  calc
    _ ≤ ∑ i, ‖(hρ.isHermitian.eigenvalues i : ℂ) * Y i i‖ := norm_sum_le _ _
    _ ≤ ∑ i, hρ.isHermitian.eigenvalues i * ‖X‖ := by
      apply Finset.sum_le_sum; intro i _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hρ.eigenvalues_nonneg i)]
      have hi := CStarMatrix.norm_entry_le_norm
        (M := CStarMatrix.ofMatrixStarAlgEquiv Y) (i := i) (j := i)
      change ‖Y i i‖ ≤ ‖CStarMatrix.ofMatrixStarAlgEquiv Y‖ at hi
      rw [StarAlgEquiv.norm_map] at hi
      exact mul_le_mul_of_nonneg_left (hi.trans_eq hy) (hρ.eigenvalues_nonneg i)
    _ = ‖X‖ := by rw [← Finset.sum_mul, hs, one_mul]

private lemma spin_unit_norm (c : Fin 3 → ℝ) (hc : vlen c = 1) : ‖spin c‖ = 1 := by
  have hc' : c 0 ^ 2 + c 1 ^ 2 + c 2 ^ 2 = 1 := by
    have h := vlen_sq c
    rw [hc] at h
    simpa only [dotProduct, Fin.sum_univ_three, one_pow, pow_two, one_mul] using h.symm
  have hm : (spin c)ᴴ * spin c = 1 := by
    have hcc : (c 0 : ℂ) ^ 2 + (c 1 : ℂ) ^ 2 + (c 2 : ℂ) ^ 2 = 1 := by
      exact_mod_cast hc'
    ext i j; fin_cases i <;> fin_cases j
    all_goals simp [spin, sigma, pauliMatrix, qubitX, qubitZ,
      Fin.sum_univ_three, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose_apply]
    all_goals ring_nf
    all_goals simp only [Complex.I_sq]
    all_goals linear_combination hcc
  have h := Matrix.l2_opNorm_conjTranspose_mul_self (spin c)
  rw [hm, norm_one] at h
  nlinarith [norm_nonneg (spin c)]

private lemma spin_covariance (ρ : TwoQubit) (hρ : ρ.IsHermitian)
    (c d : Fin 3 → ℝ) :
    localCovariance ρ (spin c) (spin d) =
      ((c ⬝ᵥ (connectedCorrelation ρ *ᵥ d) : ℝ) : ℂ) := by
  have hs (i : Fin 3) : sigma i.succ = pauli i := by
    fin_cases i <;> rfl
  have hA (i : Fin 3) : trace (ρ * (pauli i ⊗ₖ (1 : Qubit))) = (blochA ρ i : ℂ) := by
    refine Complex.ext (by rfl) ?_
    exact D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow.trace_hermitian_product_real
      ρ _ hρ (isHermitian_kronecker
        (D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings.pauli_hermitian i)
        (Matrix.isHermitian_one))
  have hB (i : Fin 3) : trace (ρ * ((1 : Qubit) ⊗ₖ pauli i)) = (blochB ρ i : ℂ) := by
    refine Complex.ext (by rfl) ?_
    exact D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow.trace_hermitian_product_real
      ρ _ hρ (isHermitian_kronecker (Matrix.isHermitian_one)
        (D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings.pauli_hermitian i))
  simp only [localCovariance, spin, hs, Fin.sum_univ_three, add_kronecker,
    kronecker_add, smul_kronecker, kronecker_smul, Matrix.mul_add, Matrix.mul_smul,
    trace_add, trace_smul, smul_eq_mul, hA, hB, trace_pauli_kronecker_eq_corr ρ hρ,
    dotProduct, Matrix.mulVec, connectedCorrelation, Complex.ofReal_add,
    Complex.ofReal_mul, Complex.ofReal_sub]
  ring

private lemma discord_nonneg (ρ : TwoQubit) : 0 ≤ geometricDiscord ρ := by
  unfold geometricDiscord
  apply mul_nonneg (by norm_num)
  apply le_csInf
  · exact ⟨_, 1, (1 : Matrix.unitaryGroup (Fin 2) ℂ).property, rfl⟩
  · rintro _ ⟨U, hU, rfl⟩
    exact (RCLike.nonneg_iff.mp
      (Matrix.posSemidef_conjTranspose_mul_self (ρ - measuredState U ρ)).trace_nonneg).1

private lemma discord_le_measurement (ρ : TwoQubit) (U : Matrix.unitaryGroup (Fin 2) ℂ) :
    geometricDiscord ρ ≤ 2 * hilbertSchmidtSquare (ρ - measuredState U ρ) := by
  unfold geometricDiscord
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro _ ⟨V, hV, rfl⟩
    exact (RCLike.nonneg_iff.mp
      (Matrix.posSemidef_conjTranspose_mul_self (ρ - measuredState V ρ)).trace_nonneg).1
  · exact ⟨U, U.property, rfl⟩

private lemma correlation_bdd (ρ : TwoQubit) (hρ : ρ.PosSemidef) (ht : trace ρ = 1) :
    BddAbove {r | ∃ a b : Qubit, ‖a‖ = 1 ∧ ‖b‖ = 1 ∧
      r = ‖localCovariance ρ a b‖} := by
  have hc : Continuous (fun p : Qubit × Qubit => ‖p.1 ⊗ₖ p.2‖) := by
    apply Continuous.norm
    apply continuous_matrix; intro i j
    change Continuous (fun p : Qubit × Qubit => p.1 i.1 j.1 * p.2 i.2 j.2)
    fun_prop
  obtain ⟨K, hK⟩ := ((isCompact_sphere (0 : Qubit) 1).prod
    (isCompact_sphere (0 : Qubit) 1)).bddAbove_image hc.continuousOn
  have hk (a b : Qubit) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) : ‖a ⊗ₖ b‖ ≤ K := by
    apply hK
    exact ⟨(a, b), ⟨by simpa only [Metric.mem_sphere, dist_zero_right] using ha,
      by simpa only [Metric.mem_sphere, dist_zero_right] using hb⟩, rfl⟩
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hk 1 1 norm_one norm_one)
  refine ⟨K + K * K, ?_⟩
  rintro r ⟨a, b, ha, hb, rfl⟩
  unfold localCovariance
  calc
    _ ≤ ‖trace (ρ * (a ⊗ₖ b))‖ +
      ‖trace (ρ * (a ⊗ₖ (1 : Qubit))) * trace (ρ * ((1 : Qubit) ⊗ₖ b))‖ := norm_sub_le _ _
    _ ≤ K + K * K := by
      rw [norm_mul]
      exact add_le_add ((density_expectation_bound ρ _ hρ ht).trans (hk a b ha hb))
        (mul_le_mul ((density_expectation_bound ρ _ hρ ht).trans (hk a 1 ha norm_one))
          ((density_expectation_bound ρ _ hρ ht).trans (hk 1 b norm_one hb))
          (norm_nonneg _) hK0)

private lemma witness_le (ρ : TwoQubit) (hρ : ρ.PosSemidef) (ht : trace ρ = 1)
    (a b : Qubit) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    ‖localCovariance ρ a b‖ ≤
        maximalMutualCorrelation ρ :=
  le_csSup (correlation_bdd ρ hρ ht) ⟨a, b, ha, hb, rfl⟩

private lemma correlation_nonneg (ρ : TwoQubit) (hρ : ρ.PosSemidef) (ht : trace ρ = 1) :
    0 ≤ maximalMutualCorrelation ρ :=
  (norm_nonneg _).trans (witness_le ρ hρ ht 1 1 (norm_one) (norm_one))

private def rotateState (U : Qubit) (ρ : TwoQubit) : TwoQubit :=
  unitaryEvolution (U ⊗ₖ (1 : Qubit))ᴴ ρ

private lemma rotation_covariance (ρ : TwoQubit) (U : Matrix.unitaryGroup (Fin 2) ℂ)
    (a b : Qubit) :
    localCovariance (rotateState U ρ) a b =
      localCovariance ρ ((U : Qubit) * a * (U : Qubit)ᴴ) b := by
  let V := (U : Qubit) ⊗ₖ (1 : Qubit)
  have hcyc (Z : TwoQubit) : trace (rotateState U ρ * Z) =
      trace (ρ * (V * Z * Vᴴ)) := by
    rw [rotateState, unitaryEvolution, Matrix.star_eq_conjTranspose,
      conjTranspose_conjTranspose]
    change trace (Vᴴ * ρ * V * Z) = _
    calc
      _ = trace (Vᴴ * (ρ * V * Z)) := by congr 1; noncomm_ring
      _ = trace ((ρ * V * Z) * Vᴴ) := trace_mul_comm _ _
      _ = _ := by congr 1; noncomm_ring
  have hk (a b : Qubit) : V * (a ⊗ₖ b) * Vᴴ =
      ((U : Qubit) * a * (U : Qubit)ᴴ) ⊗ₖ b := by
    dsimp only [V]
    rw [conjTranspose_kronecker, conjTranspose_one,
      ← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]
  unfold localCovariance
  rw [hcyc, hcyc, hcyc, hk, hk, hk]
  have hU : (U : Qubit) * (U : Qubit)ᴴ = 1 := by
    exact Matrix.mem_unitaryGroup_iff.mp U.property
  simp only [Matrix.mul_one, hU]


private lemma rotated_spin_witness (ρ : TwoQubit) (hρ : ρ.PosSemidef) (ht : trace ρ = 1)
    (U : Matrix.unitaryGroup (Fin 2) ℂ) (c d : Fin 3 → ℝ)
    (hc : vlen c = 1) (hd : vlen d = 1) :
    |c ⬝ᵥ (connectedCorrelation (rotateState U ρ) *ᵥ d)| ≤
      maximalMutualCorrelation ρ := by
  have hr : (rotateState U ρ).PosSemidef := by
    rw [rotateState, unitaryEvolution, Matrix.star_eq_conjTranspose,
      conjTranspose_conjTranspose]
    exact hρ.conjTranspose_mul_mul_same _
  have h := witness_le ρ hρ ht ((U : Qubit) * spin c * (U : Qubit)ᴴ) (spin d)
    (by
      change ‖(U : Qubit) * spin c * ((star U : Matrix.unitaryGroup (Fin 2) ℂ) : Qubit)‖ = 1
      rw [CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul,
        spin_unit_norm c hc]) (spin_unit_norm d hd)
  rw [← rotation_covariance, spin_covariance _ hr.isHermitian,
    Complex.norm_real, Real.norm_eq_abs] at h
  exact h

private lemma row_bound (ρ : TwoQubit) (hρ : ρ.PosSemidef) (ht : trace ρ = 1)
    (U : Matrix.unitaryGroup (Fin 2) ℂ) (i : Fin 3) :
    vlen (connectedCorrelation (rotateState U ρ) i) ≤ maximalMutualCorrelation ρ := by
  let r := connectedCorrelation (rotateState U ρ) i
  by_cases hr : r = 0
  · rw [show connectedCorrelation (rotateState U ρ) i = 0 from hr]
    simpa [vlen] using correlation_nonneg ρ hρ ht
  · obtain ⟨hd, hrd⟩ := normalized_unit r hr
    have he : vlen (Pi.single i (1 : ℝ)) = 1 := by
      rw [D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.vlen_eq_norm]
      change ‖(EuclideanSpace.single i (1 : ℝ) : EuclideanSpace ℝ (Fin 3))‖ = 1
      simp only [PiLp.norm_single, norm_one]
    have h := rotated_spin_witness ρ hρ ht U (Pi.single i 1) ((vlen r)⁻¹ • r) he hd
    have hn : r ⬝ᵥ ((vlen r)⁻¹ • r) = vlen r := by
      rw [dotProduct_smul, ← vlen_sq, smul_eq_mul]
      have hh : vlen r ≠ 0 := by
        intro hh
        rw [hh, zero_smul] at hrd
        exact hr hrd.symm
      field_simp [hh]
    simp only [single_dotProduct, one_mul] at h
    change |r ⬝ᵥ ((vlen r)⁻¹ • r)| ≤ maximalMutualCorrelation ρ at h
    have hv : 0 ≤ vlen r := by
      unfold vlen
      exact Real.sqrt_nonneg _
    rw [hn, abs_of_nonneg hv] at h
    simpa [r] using h

private lemma disturbance_coordinates (R : TwoQubit) (hR : R.IsHermitian)
    (h0 : blochA R 0 = 0) (h1 : blochA R 1 = 0) :
    hilbertSchmidtSquare (R - measuredState 1 R) =
      (vlen (connectedCorrelation R 0) ^ 2 + vlen (connectedCorrelation R 1) ^ 2) / 4 := by
  have hp0 : pauli 0 = !![0, 1; 1, 0] := by
    simp [pauli.eq_def, pauliMatrix, qubitX]
  have hp1 : pauli 1 = !![0, -Complex.I; Complex.I, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [pauli.eq_def, pauliMatrix, qubitX, qubitZ]
  have hp2 : pauli 2 = !![1, 0; 0, -1] := by
    simp [pauli.eq_def, pauliMatrix, qubitZ]
  have hid : 4 * trace ((R - measuredState 1 R) * (R - measuredState 1 R)) =
      trace (R * (pauli 0 ⊗ₖ (1 : Qubit))) ^ 2 +
      trace (R * (pauli 1 ⊗ₖ (1 : Qubit))) ^ 2 +
      ∑ j : Fin 3, (trace (R * (pauli 0 ⊗ₖ pauli j)) ^ 2 +
        trace (R * (pauli 1 ⊗ₖ pauli j)) ^ 2) := by
    simp [measuredState, unreadState, Matrix.trace, Matrix.diag, Matrix.mul_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three,
      Matrix.single_apply, Matrix.one_apply, hp0, hp1, hp2]
    ring_nf
    simp only [Complex.I_sq]
    ring
  have hm : (measuredState 1 R)ᴴ = measuredState 1 R := by
    simp only [measuredState, unreadState, conjTranspose_sum, conjTranspose_mul,
      conjTranspose_kronecker, conjTranspose_one, conjTranspose_single, star_one, hR.eq]
    simp only [Matrix.mul_assoc]
  have hδ : (R - measuredState 1 R)ᴴ = R - measuredState 1 R := by
    rw [conjTranspose_sub, hR.eq, hm]
  have hA (i : Fin 3) : trace (R * (pauli i ⊗ₖ (1 : Qubit))) = (blochA R i : ℂ) := by
    refine Complex.ext (by rfl) ?_
    exact D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow.trace_hermitian_product_real
      R _ hR (isHermitian_kronecker
        (D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings.pauli_hermitian i)
        (Matrix.isHermitian_one))
  simp only [hA, h0, h1, Complex.ofReal_zero, zero_pow (by norm_num : 2 ≠ 0),
    zero_add, trace_pauli_kronecker_eq_corr R hR] at hid
  have hh := congrArg Complex.re hid
  norm_num [← Complex.ofReal_pow, Complex.mul_re] at hh
  rw [hilbertSchmidtSquare, hδ]
  rw [vlen_sq, vlen_sq]
  simp only [dotProduct, connectedCorrelation, h0, h1, zero_mul, sub_zero]
  simp only [Fin.sum_univ_three] at hh ⊢
  nlinarith

private lemma disturbance_rotation (ρ : TwoQubit) (U : Matrix.unitaryGroup (Fin 2) ℂ) :
    hilbertSchmidtSquare (ρ - measuredState U ρ) =
      hilbertSchmidtSquare (rotateState U ρ - measuredState 1 (rotateState U ρ)) := by
  let V := (U : Qubit) ⊗ₖ (1 : Qubit)
  have hv : Vᴴ * V = 1 := by
    dsimp only [V]
    rw [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul,
      ← Matrix.star_eq_conjTranspose, Unitary.coe_star_mul_self,
      Matrix.one_mul, one_kronecker_one]
  have hv' : V * Vᴴ = 1 := by
    have hU : (U : Qubit) * (U : Qubit)ᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp U.property
    dsimp only [V]
    rw [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul,
      hU, Matrix.one_mul, one_kronecker_one]
  have hk (k : Fin 2) : (((U : Qubit) * Matrix.single k k 1 * (U : Qubit)ᴴ) ⊗ₖ
      (1 : Qubit)) = V * ((Matrix.single k k 1 : Qubit) ⊗ₖ (1 : Qubit)) * Vᴴ := by
    dsimp only [V]
    rw [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul,
      ← mul_kronecker_mul, Matrix.one_mul, Matrix.one_mul]
  have hmeas : measuredState U ρ =
      V * measuredState 1 (rotateState U ρ) * Vᴴ := by
    simp only [measuredState, unreadState, Fin.sum_univ_two, conjTranspose_one,
      Matrix.one_mul, Matrix.mul_one, rotateState, unitaryEvolution,
      Matrix.star_eq_conjTranspose, conjTranspose_conjTranspose]
    rw [hk 0, hk 1]
    change _ = V * (_ * (Vᴴ * ρ * V) * _ + _ * (Vᴴ * ρ * V) * _) * Vᴴ
    noncomm_ring
  have hback : V * rotateState U ρ * Vᴴ = ρ := by
    rw [rotateState, unitaryEvolution, Matrix.star_eq_conjTranspose,
      conjTranspose_conjTranspose]
    change V * (Vᴴ * ρ * V) * Vᴴ = ρ
    calc
      _ = (V * Vᴴ) * ρ * (V * Vᴴ) := by noncomm_ring
      _ = ρ := by rw [hv', Matrix.one_mul, Matrix.mul_one]
  have hd : ρ - measuredState U ρ =
      V * (rotateState U ρ - measuredState 1 (rotateState U ρ)) * Vᴴ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, hback, hmeas]
  rw [hd]
  set D := rotateState U ρ - measuredState 1 (rotateState U ρ)
  unfold hilbertSchmidtSquare
  congr 1
  have hp : (V * D * Vᴴ)ᴴ * (V * D * Vᴴ) = V * (Dᴴ * D) * Vᴴ := by
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose]
    calc
      _ = V * (Dᴴ * (Vᴴ * V) * D) * Vᴴ := by noncomm_ring
      _ = _ := by rw [hv, Matrix.mul_one]
  rw [hp, trace_mul_cycle, hv, Matrix.one_mul]

private lemma marginal_basis (ρ : TwoQubit) (hρ : ρ.PosSemidef) :
    ∃ U : Matrix.unitaryGroup (Fin 2) ℂ,
      blochA (rotateState U ρ) 0 = 0 ∧ blochA (rotateState U ρ) 1 = 0 := by
  have hp0 : pauli 0 = !![0, 1; 1, 0] := by
    simp [pauli.eq_def, pauliMatrix, qubitX]
  have hp1 : pauli 1 = !![0, -Complex.I; Complex.I, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [pauli.eq_def, pauliMatrix, qubitX, qubitZ]
  let h := (partialTraceRight_posSemidef hρ).isHermitian
  let U := h.eigenvectorUnitary
  refine ⟨U, ?_⟩
  have hp : partialTraceRight (rotateState U ρ) =
      (U : Qubit)ᴴ * partialTraceRight ρ * (U : Qubit) := by
    simpa only [rotateState, unitaryEvolution, Matrix.star_eq_conjTranspose,
      conjTranspose_kronecker, conjTranspose_one, conjTranspose_conjTranspose] using
      D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings.ptrace2_left
        ((U : Qubit)ᴴ) ρ
  have hh : (U : Qubit)ᴴ * partialTraceRight ρ * (U : Qubit) =
      diagonal (RCLike.ofReal ∘ h.eigenvalues) := by
    simpa only [U, Unitary.conjStarAlgAut_star_apply, Unitary.coe_star,
      Matrix.star_eq_conjTranspose] using h.conjStarAlgAut_star_eigenvectorUnitary
  have hm := hp.trans hh
  constructor
  all_goals simp only [blochA, trace_mul_kron_one, hm]
  · simp [hp0, Matrix.trace, Matrix.diag, Matrix.diagonal_mul, Fin.sum_univ_two]
  · simp [hp1, Matrix.trace, Matrix.diag, Matrix.diagonal_mul, Fin.sum_univ_two]

private lemma discord_sq_bound (ρ : TwoQubit) (hρ : ρ.PosSemidef) (ht : trace ρ = 1) :
    geometricDiscord ρ ≤ maximalMutualCorrelation ρ ^ 2 := by
  obtain ⟨U, h0, h1⟩ := marginal_basis ρ hρ
  have hr : (rotateState U ρ).PosSemidef := by
    rw [rotateState, unitaryEvolution, Matrix.star_eq_conjTranspose,
      conjTranspose_conjTranspose]
    exact hρ.conjTranspose_mul_mul_same _
  have hd := discord_le_measurement ρ U
  rw [disturbance_rotation, disturbance_coordinates _ hr.isHermitian h0 h1] at hd
  have hC := correlation_nonneg ρ hρ ht
  have hr0 : vlen (connectedCorrelation (rotateState U ρ) 0) ^ 2 ≤
      maximalMutualCorrelation ρ ^ 2 :=
    (sq_le_sq₀ (Real.sqrt_nonneg _) hC).mpr (row_bound ρ hρ ht U 0)
  have hr1 : vlen (connectedCorrelation (rotateState U ρ) 1) ^ 2 ≤
      maximalMutualCorrelation ρ ^ 2 :=
    (sq_le_sq₀ (Real.sqrt_nonneg _) hC).mpr (row_bound ρ hρ ht U 1)
  linarith


/-- Maximal mutual correlation dominates the square root of normalized geometric discord. -/
theorem result : claim := by
  intro ρ hρ ht
  have hC := correlation_nonneg ρ hρ ht
  have hD := discord_sq_bound ρ hρ ht
  nlinarith [Real.sq_sqrt (discord_nonneg ρ), Real.sqrt_nonneg (geometricDiscord ρ)]

end D5.S3.Quantum.Information.GeometricDiscordMutualCorrelationBound
