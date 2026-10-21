/- GID: D5/S3/Quantum/Information/TraceNormDiscordMutualCorrelationBound
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/TraceNormDiscordMutualCorrelationBound
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Trace-norm geometric discord is bounded by maximal mutual correlation. -/

import D5.S3.Quantum.Information.GeometricDiscordMutualCorrelationBound
import D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability

/-! The trace-norm discord of two qubits is bounded by their maximal mutual correlation. -/

set_option autoImplicit false
noncomputable section

open Matrix
open D5.S3.Quantum.Information.PartialTraceMutualInformation (isHermitian_kronecker)
open scoped Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open D5.S3.Quantum.Information.GeometricDiscordMutualCorrelationBound
  (measuredState localCovariance maximalMutualCorrelation connectedCorrelation
    rotateState rotated_spin_witness marginal_basis)
open D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm traceNorm_nonneg)
open D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability (traceNorm_isometry)
open D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction
  (pauli pauli_zero pauli_one pauli_two blochA blochB corr vlen vlen_nonneg)
open D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH (vlen_sq normalized_unit sigma_succ)
open D5.S3.QuantumChannels.PauliThreeWeightBayesianInverseUniqueness (spin sigma)
open D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence (pauliMatrix)
open D5.S3.Quantum.FiniteDimensional (qubitX qubitZ)

namespace D5.S3.Quantum.Information.TraceNormDiscordMutualCorrelationBound

local notation "Qubit" => Matrix (Fin 2) (Fin 2) ℂ
local notation "TwoQubit" => Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ

/-- One-sided geometric discord for the trace norm, measured on the first qubit. -/
def traceNormDiscord (ρ : TwoQubit) : ℝ :=
  sInf ((fun U => traceNorm (ρ - measuredState U ρ)) ''
    (Matrix.unitaryGroup (Fin 2) ℂ : Set Qubit))

/-- The trace-norm discord-correlation bound for all two-qubit density matrices. -/
def claim : Prop :=
  ∀ ρ : TwoQubit, ρ.PosSemidef → trace ρ = 1 →
    traceNormDiscord ρ ≤ maximalMutualCorrelation ρ

private lemma trace_discord_le_measurement (ρ : TwoQubit)
    (U : Matrix.unitaryGroup (Fin 2) ℂ) :
    traceNormDiscord ρ ≤ traceNorm (ρ - measuredState U ρ) := by
  apply csInf_le
  · exact ⟨0, by rintro _ ⟨V, hV, rfl⟩; exact traceNorm_nonneg _⟩
  · exact ⟨U, U.property, rfl⟩

private lemma commuting_square_root {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ) (a b : ℝ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hAA : A * A = (a ^ 2 : ℂ) • 1) (hBB : B * B = (b ^ 2 : ℂ) • 1)
    (hAB : A * B = B * A) (ha : 0 < a) (hb : 0 ≤ b) (hba : b ≤ a) :
    CFC.sqrt (((1 / 4 : ℂ) • (A + B))ᴴ * ((1 / 4 : ℂ) • (A + B))) =
      (1 / 4 : ℂ) • ((a : ℂ) • 1 + (a⁻¹ : ℂ) • (A * B)) := by
  let H := (1 / 4 : ℂ) • ((a : ℂ) • (1 : Matrix n n ℂ) + (a⁻¹ : ℂ) • (A * B))
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ha
  have hH : H = (1 / (8 * a) : ℝ) •
      ((A + B)ᴴ * (A + B) + (a ^ 2 - b ^ 2 : ℝ) • 1) := by
    rw [conjTranspose_add, hA.eq, hB.eq]
    simp only [Matrix.add_mul, Matrix.mul_add, hAA, hBB, ← hAB]
    ext i j
    simp only [H, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul,
      Complex.real_smul, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_sub,
      Complex.ofReal_pow, Complex.ofReal_inv, Complex.ofReal_ofNat, Complex.ofReal_one]
    field_simp [ha0]
    <;> ring
  have hpos : 0 ≤ H := by
    rw [hH]
    apply Matrix.PosSemidef.nonneg
    apply Matrix.PosSemidef.smul
    · exact (Matrix.posSemidef_conjTranspose_mul_self (A + B)).add
        (Matrix.PosSemidef.one.smul (by nlinarith : 0 ≤ a ^ 2 - b ^ 2))
    · positivity
  apply CFC.sqrt_unique _ hpos
  rw [conjTranspose_smul, conjTranspose_add, hA.eq, hB.eq]
  have hABAB : A * B * (A * B) = (a ^ 2 * b ^ 2 : ℂ) • 1 := by
    calc
      _ = (A * A) * (B * B) := by
        calc
          _ = A * (B * A) * B := by simp only [Matrix.mul_assoc]
          _ = _ := by rw [← hAB]; simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [hAA, hBB]
        simp only [smul_mul_assoc, mul_smul_comm, Matrix.one_mul, smul_smul]
        congr 1
        ring
  dsimp only [H]
  simp only [Matrix.add_mul, Matrix.mul_add, smul_mul_assoc, mul_smul_comm,
    Matrix.one_mul, Matrix.mul_one, smul_smul, hABAB, hAA, hBB, ← hAB]
  ext i j
  simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, star_div, star_one,
    star_ofNat, Complex.ofReal_inv]
  norm_num only [star_div₀, star_one, star_ofNat, Complex.ofReal_one]
  field_simp [ha0]
  <;> ring

private def planeVector (O : Matrix (Fin 2) (Fin 2) ℝ) (i : Fin 2) : Fin 3 → ℝ :=
  ![O 0 i, O 1 i, 0]

private def planeRow (Q : Matrix (Fin 3) (Fin 3) ℝ)
    (O : Matrix (Fin 2) (Fin 2) ℝ) (i : Fin 2) : Fin 3 → ℝ :=
  (planeVector O i) ᵥ* Q

private lemma plane_diagonalization (Q : Matrix (Fin 3) (Fin 3) ℝ) :
    ∃ O : Matrix.unitaryGroup (Fin 2) ℝ, planeRow Q O 0 ⬝ᵥ planeRow Q O 1 = 0 := by
  let G : Matrix (Fin 2) (Fin 2) ℝ :=
    !![Q 0 ⬝ᵥ Q 0, Q 0 ⬝ᵥ Q 1; Q 1 ⬝ᵥ Q 0, Q 1 ⬝ᵥ Q 1]
  have hG : G.IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [G, dotProduct_comm]
  let O := hG.eigenvectorUnitary
  refine ⟨O, ?_⟩
  have hd : (O : Matrix (Fin 2) (Fin 2) ℝ)ᴴ * G * O = diagonal hG.eigenvalues := by
    exact hG.conjStarAlgAut_star_eigenvectorUnitary
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) hd
  rw [Matrix.diagonal_apply_ne _ (by decide : (0 : Fin 2) ≠ 1)] at h01
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, star_trivial,
    Fin.sum_univ_two] at h01
  simp [G, dotProduct, Fin.sum_univ_three] at h01
  simp only [planeRow, planeVector, Matrix.vecMul, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, zero_mul, add_zero]
  linear_combination h01

private lemma plane_frame (O : Matrix.unitaryGroup (Fin 2) ℝ) :
    vlen (planeVector O 0) = 1 ∧ vlen (planeVector O 1) = 1 ∧
      planeVector O 0 ⬝ᵥ planeVector O 1 = 0 := by
  have ho : (O : Matrix (Fin 2) (Fin 2) ℝ)ᴴ * O = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp O.property
  have he (i j : Fin 2) := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M i j) ho
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, star_trivial,
    Fin.sum_univ_two] at he
  have hn (i : Fin 2) : vlen (planeVector O i) = 1 := by
    have hs : vlen (planeVector O i) ^ 2 = 1 := by
      rw [vlen_sq]
      simpa [planeVector, dotProduct, Fin.sum_univ_three] using he i i
    nlinarith [vlen_nonneg (planeVector O i)]
  refine ⟨hn 0, hn 1, ?_⟩
  have hh := he 0 1
  simp only [Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1)] at hh
  simpa only [planeVector, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, zero_mul,
    add_zero] using hh

private lemma spin_hermitian (c : Fin 3 → ℝ) : (spin c).IsHermitian := by
  change (spin c)ᴴ = spin c
  simp only [spin, sigma_succ, conjTranspose_sum, conjTranspose_smul,
    Complex.star_def, Complex.conj_ofReal,
    (D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings.pauli_hermitian _).eq]

private lemma spin_anticommutator (c d : Fin 3 → ℝ) :
    spin c * spin d + spin d * spin c = (2 * (c ⬝ᵥ d) : ℝ) • (1 : Qubit) := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [spin, sigma, pauliMatrix, qubitX, qubitZ, Fin.sum_univ_three,
    Matrix.mul_apply, Fin.sum_univ_two, dotProduct, Complex.ofReal_add,
    Complex.ofReal_mul, Complex.real_smul]
  all_goals ring_nf
  all_goals simp only [Complex.I_sq]
  all_goals ring

private lemma spin_square (c : Fin 3 → ℝ) :
    spin c * spin c = (vlen c ^ 2 : ℝ) • (1 : Qubit) := by
  have hh := spin_anticommutator c c
  rw [← vlen_sq] at hh
  ext i j
  have h := congrArg (fun M : Qubit => M i j) hh
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Complex.real_smul,
    Complex.ofReal_mul, Complex.ofReal_ofNat] at h ⊢
  linear_combination h / 2

private lemma tensor_terms (c d a b : Fin 3 → ℝ)
    (hc : vlen c = 1) (hd : vlen d = 1)
    (hcd : c ⬝ᵥ d = 0) (hab : a ⬝ᵥ b = 0) :
    let A := spin c ⊗ₖ spin a
    let B := spin d ⊗ₖ spin b
    A.IsHermitian ∧ B.IsHermitian ∧
    A * A = (vlen a ^ 2 : ℝ) • 1 ∧ B * B = (vlen b ^ 2 : ℝ) • 1 ∧
    A * B = B * A ∧ trace (A * B) = 0 := by
  dsimp only
  have hanti (u v : Fin 3 → ℝ) (huv : u ⬝ᵥ v = 0) :
      spin u * spin v = -(spin v * spin u) := by
    have h := spin_anticommutator u v
    rw [huv, mul_zero, zero_smul] at h
    exact eq_neg_of_add_eq_zero_left h
  refine ⟨isHermitian_kronecker (spin_hermitian c) (spin_hermitian a),
    isHermitian_kronecker (spin_hermitian d) (spin_hermitian b), ?_, ?_, ?_, ?_⟩
  · rw [← mul_kronecker_mul, spin_square, spin_square, hc]
    simp only [one_pow, one_smul, kronecker_smul, one_kronecker_one]
  · rw [← mul_kronecker_mul, spin_square, spin_square, hd]
    simp only [one_pow, one_smul, kronecker_smul, one_kronecker_one]
  · rw [← mul_kronecker_mul, ← mul_kronecker_mul, hanti c d hcd, hanti a b hab,
      show (-((spin d) * spin c)) ⊗ₖ (-((spin b) * spin a)) =
        (spin d * spin c) ⊗ₖ (spin b * spin a) from by ext i j; simp]
  · rw [← mul_kronecker_mul, trace_kronecker]
    have hz : trace (spin c * spin d) = 0 := by
      have h := congrArg Matrix.trace (spin_anticommutator c d)
      rw [hcd, mul_zero, zero_smul, trace_zero, trace_add, trace_mul_comm (spin d)] at h
      linear_combination h / 2
    rw [hz, zero_mul]

private lemma ordered_trace_norm (A B : TwoQubit) (a b : ℝ)
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hAA : A * A = (a ^ 2 : ℝ) • 1) (hBB : B * B = (b ^ 2 : ℝ) • 1)
    (hAB : A * B = B * A) (ht : trace (A * B) = 0)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hba : b ≤ a) :
    traceNorm ((1 / 4 : ℂ) • (A + B)) = a := by
  by_cases ha0 : a = 0
  · have hb0 : b = 0 := by linarith
    have hAz : Aᴴ * A = 0 := by rw [hA.eq, hAA, ha0]; simp
    have hBz : Bᴴ * B = 0 := by rw [hB.eq, hBB, hb0]; simp
    have hzA : A = 0 := Matrix.conjTranspose_mul_self_eq_zero.mp hAz
    have hzB : B = 0 := Matrix.conjTranspose_mul_self_eq_zero.mp hBz
    rw [hzA, hzB, ha0]
    simp [traceNorm]
  · have hroot := commuting_square_root A B a b hA hB
      (by simpa only [← Complex.ofReal_pow, Complex.coe_smul] using hAA)
      (by simpa only [← Complex.ofReal_pow, Complex.coe_smul] using hBB) hAB
      (lt_of_le_of_ne ha (Ne.symm ha0)) hb hba
    unfold traceNorm
    rw [hroot, trace_smul, trace_add, trace_smul, trace_smul, ht]
    norm_num [Fintype.card_prod, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    <;> ring

set_option maxHeartbeats 800000 in
-- The sixteen complex entry identities require more simplifier reductions.
private lemma disturbance_tensor (R : TwoQubit) (hR : R.IsHermitian)
    (h0 : blochA R 0 = 0) (h1 : blochA R 1 = 0) :
    R - measuredState 1 R = (1 / 4 : ℂ) •
      (pauli 0 ⊗ₖ spin (connectedCorrelation R 0) +
        pauli 1 ⊗ₖ spin (connectedCorrelation R 1)) := by
  have hre (i j : Fin 2 × Fin 2) : (R j i).re = (R i j).re := by
    simpa only [map_star, Complex.star_def, Complex.conj_re] using
      congrArg Complex.re (hR.apply i j)
  have him (i j : Fin 2 × Fin 2) : -(R j i).im = (R i j).im := by
    simpa only [Complex.star_def, Complex.conj_im] using
      congrArg Complex.im (hR.apply i j)
  simp only [spin, connectedCorrelation, h0, h1, zero_mul, sub_zero]
  simp [blochA, pauli_zero, pauli_one, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
    Complex.mul_re, Complex.mul_im] at h0 h1
  ext ⟨i, k⟩ ⟨j, l⟩
  fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l
  all_goals apply Complex.ext
  all_goals simp [measuredState, D5.S3.Observer.Conditioning.unreadState, corr, spin,
    sigma_succ, pauli_zero, pauli_one, pauli_two, Matrix.single_apply,
    Matrix.one_apply, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three,
    Complex.mul_re, Complex.mul_im]
  all_goals linarith [hre (0, 0) (1, 0), hre (0, 1) (1, 1),
                      hre (0, 0) (1, 1), hre (0, 1) (1, 0),
                      him (0, 0) (1, 0), him (0, 1) (1, 1),
                      him (0, 0) (1, 1), him (0, 1) (1, 0)]

set_option maxHeartbeats 800000 in
-- Expanding the sixteen tensor entries requires more simplifier reductions.
private lemma plane_reconstruction (Q : Matrix (Fin 3) (Fin 3) ℝ)
    (O : Matrix.unitaryGroup (Fin 2) ℝ) :
    spin (planeVector O 0) ⊗ₖ spin (planeRow Q O 0) +
      spin (planeVector O 1) ⊗ₖ spin (planeRow Q O 1) =
      pauli 0 ⊗ₖ spin (Q 0) + pauli 1 ⊗ₖ spin (Q 1) := by
  have ho : (O : Matrix (Fin 2) (Fin 2) ℝ) * (O : Matrix (Fin 2) (Fin 2) ℝ)ᴴ = 1 :=
    Matrix.mem_unitaryGroup_iff.mp O.property
  have he (i j : Fin 2) := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M i j) ho
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, star_trivial,
    Fin.sum_univ_two] at he
  have h00 := he 0 0
  have h11 := he 1 1
  have h01 := he 0 1
  norm_num only [Matrix.one_apply_eq, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1)]
    at h00 h11 h01
  have hr0 (j : Fin 3) :
      O 0 0 * (O 0 0 * Q 0 j + O 1 0 * Q 1 j) +
        O 0 1 * (O 0 1 * Q 0 j + O 1 1 * Q 1 j) = Q 0 j := by
    linear_combination h00 * Q 0 j + h01 * Q 1 j
  have hr1 (j : Fin 3) :
      O 1 0 * (O 0 0 * Q 0 j + O 1 0 * Q 1 j) +
        O 1 1 * (O 0 1 * Q 0 j + O 1 1 * Q 1 j) = Q 1 j := by
    linear_combination h01 * Q 0 j + h11 * Q 1 j
  ext ⟨i, k⟩ ⟨j, l⟩
  fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l
  all_goals apply Complex.ext
  all_goals simp [spin, planeVector, planeRow, Matrix.vecMul, dotProduct, sigma_succ,
    pauli_zero, pauli_one, pauli_two, Fin.sum_univ_two, Fin.sum_univ_three,
    Complex.mul_re, Complex.mul_im]
  all_goals linarith [hr0 0, hr0 1, hr0 2, hr1 0, hr1 1, hr1 2]

private lemma plane_trace_norm (c d a b : Fin 3 → ℝ)
    (hc : vlen c = 1) (hd : vlen d = 1)
    (hcd : c ⬝ᵥ d = 0) (hab : a ⬝ᵥ b = 0) :
    traceNorm ((1 / 4 : ℂ) • (spin c ⊗ₖ spin a + spin d ⊗ₖ spin b)) =
      max (vlen a) (vlen b) := by
  obtain ⟨hA, hB, hAA, hBB, hAB, ht⟩ := tensor_terms c d a b hc hd hcd hab
  by_cases hba : vlen b ≤ vlen a
  · rw [max_eq_left hba]
    exact ordered_trace_norm _ _ _ _ hA hB hAA hBB hAB ht
      (vlen_nonneg a) (vlen_nonneg b) hba
  · rw [max_eq_right (le_of_not_ge hba)]
    rw [add_comm]
    apply ordered_trace_norm _ _ _ _ hB hA hBB hAA hAB.symm
      (by rw [← hAB]; exact ht) (vlen_nonneg b) (vlen_nonneg a) (le_of_not_ge hba)

private lemma rotated_direction_bound (ρ : TwoQubit) (hρ : ρ.PosSemidef)
    (ht : trace ρ = 1) (U : Matrix.unitaryGroup (Fin 2) ℂ)
    (c : Fin 3 → ℝ) (hc : vlen c = 1) :
    vlen (c ᵥ* connectedCorrelation (rotateState U ρ)) ≤ maximalMutualCorrelation ρ := by
  let r := c ᵥ* connectedCorrelation (rotateState U ρ)
  have hC : 0 ≤ maximalMutualCorrelation ρ :=
    (abs_nonneg _).trans (rotated_spin_witness ρ hρ ht U c ![1, 0, 0] hc
      (by norm_num [vlen, Fin.sum_univ_three]))
  by_cases hr : r = 0
  · change vlen r ≤ _
    rw [hr]
    simpa only [vlen, Pi.zero_apply, zero_pow (by decide : 2 ≠ 0),
      Finset.sum_const_zero, Real.sqrt_zero] using hC
  · obtain ⟨hd, hrd⟩ := normalized_unit r hr
    have hh : vlen r ≠ 0 := by
      intro hz
      rw [hz, zero_smul] at hrd
      exact hr hrd.symm
    have h := rotated_spin_witness ρ hρ ht U c ((vlen r)⁻¹ • r) hc hd
    rw [Matrix.dotProduct_mulVec c (connectedCorrelation (rotateState U ρ))
      ((vlen r)⁻¹ • r)] at h
    change |r ⬝ᵥ ((vlen r)⁻¹ • r)| ≤ _ at h
    rw [dotProduct_smul, ← vlen_sq, smul_eq_mul] at h
    change |(vlen r)⁻¹ * vlen r ^ 2| ≤ _ at h
    have he : (vlen r)⁻¹ * vlen r ^ 2 = vlen r := by field_simp [hh]
    rw [he, abs_of_nonneg (vlen_nonneg r)] at h
    exact h

private lemma trace_disturbance_rotation (ρ : TwoQubit)
    (U : Matrix.unitaryGroup (Fin 2) ℂ) :
    traceNorm (ρ - measuredState U ρ) =
      traceNorm (rotateState U ρ - measuredState 1 (rotateState U ρ)) := by
  let V := (U : Qubit) ⊗ₖ (1 : Qubit)
  have hv : Vᴴ * V = 1 := by
    dsimp only [V]
    rw [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul,
      ← Matrix.star_eq_conjTranspose, Unitary.coe_star_mul_self,
      Matrix.one_mul, one_kronecker_one]
  have hv' : V * Vᴴ = 1 := by
    dsimp only [V]
    rw [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul,
      show (U : Qubit) * (U : Qubit)ᴴ = 1 from
        Matrix.mem_unitaryGroup_iff.mp U.property, Matrix.one_mul, one_kronecker_one]
  have hk (k : Fin 2) : (((U : Qubit) * Matrix.single k k 1 * (U : Qubit)ᴴ) ⊗ₖ
      (1 : Qubit)) = V * ((Matrix.single k k 1 : Qubit) ⊗ₖ (1 : Qubit)) * Vᴴ := by
    dsimp only [V]
    rw [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul,
      ← mul_kronecker_mul, Matrix.one_mul, Matrix.one_mul]
  have hmeas : measuredState U ρ = V * measuredState 1 (rotateState U ρ) * Vᴴ := by
    simp only [measuredState, D5.S3.Observer.Conditioning.unreadState, Fin.sum_univ_two,
      conjTranspose_one, Matrix.one_mul, Matrix.mul_one, rotateState,
      D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics.unitaryEvolution,
      Matrix.star_eq_conjTranspose, conjTranspose_conjTranspose]
    rw [hk 0, hk 1]
    change _ = V * (_ * (Vᴴ * ρ * V) * _ + _ * (Vᴴ * ρ * V) * _) * Vᴴ
    noncomm_ring
  have hback : V * rotateState U ρ * Vᴴ = ρ := by
    rw [rotateState, D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics.unitaryEvolution,
      Matrix.star_eq_conjTranspose, conjTranspose_conjTranspose]
    change V * (Vᴴ * ρ * V) * Vᴴ = ρ
    calc
      _ = (V * Vᴴ) * ρ * (V * Vᴴ) := by noncomm_ring
      _ = ρ := by rw [hv', Matrix.one_mul, Matrix.mul_one]
  have hd : ρ - measuredState U ρ =
      V * (rotateState U ρ - measuredState 1 (rotateState U ρ)) * Vᴴ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, hback, hmeas]
  rw [hd, traceNorm_isometry V hv]

/-- Maximal mutual correlation bounds one-sided trace-norm geometric discord. -/
theorem result : claim := by
  intro ρ hρ ht
  obtain ⟨U, h0, h1⟩ := marginal_basis ρ hρ
  have hr : (rotateState U ρ).PosSemidef := by
    rw [rotateState, D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics.unitaryEvolution,
      Matrix.star_eq_conjTranspose, conjTranspose_conjTranspose]
    exact hρ.conjTranspose_mul_mul_same _
  obtain ⟨O, ho⟩ := plane_diagonalization (connectedCorrelation (rotateState U ρ))
  obtain ⟨hc, hd, hcd⟩ := plane_frame O
  have he := disturbance_tensor (rotateState U ρ) hr.isHermitian h0 h1
  rw [← plane_reconstruction (connectedCorrelation (rotateState U ρ)) O] at he
  have hn := plane_trace_norm _ _ _ _ hc hd hcd ho
  have hbound := max_le
    (rotated_direction_bound ρ hρ ht U _ hc)
    (rotated_direction_bound ρ hρ ht U _ hd)
  calc
    traceNormDiscord ρ ≤ traceNorm (ρ - measuredState U ρ) :=
      trace_discord_le_measurement ρ U
    _ = traceNorm (rotateState U ρ - measuredState 1 (rotateState U ρ)) :=
      trace_disturbance_rotation ρ U
    _ = max (vlen (planeRow (connectedCorrelation (rotateState U ρ)) O 0))
        (vlen (planeRow (connectedCorrelation (rotateState U ρ)) O 1)) := by rw [he]; exact hn
    _ ≤ maximalMutualCorrelation ρ := hbound

end D5.S3.Quantum.Information.TraceNormDiscordMutualCorrelationBound
