/- GID: D5/S3/QuantumChannels/PauliThreeWeightBayesianInverseUniqueness
   generality: I
   mirror-B: D5/B/S3/QuantumChannels/PauliThreeWeightBayesianInverseUniqueness
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: A Pauli channel with exactly three nonzero weights has a Bayesian inverse only at the maximally mixed state. -/

/-
proof_shape: result: bind-only. Every private theorem is bind-only and lies on the proof path of
  result (CLAUDE.md §3.2, consumed helpers): sigma_properties, channel_self_adjoint,
  channel_unital, channel_cptp, mixed_inverse, density_coordinates, choi, choi_psd, choi_bayes,
  scaled_sylvester, channel_bloch, witness_strict, support_zero, witness_numerator,
  inverse_only_mixed.
escape_witness: none.
admission_basis: open-problem-resolution (#13585; Proved)
Direct frozen dependencies: D5/S3/QuantumChannels/CoPRelativeQuantumnessRefutation,
  D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.
-/

import D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation
import D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation (IsDensity IsCPTP)
open D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence (Pauli pauliMatrix)
open D5.S3.Quantum.FiniteDimensional (qubitX qubitZ qubit_weyl_star)

noncomputable section
namespace D5.S3.QuantumChannels.PauliThreeWeightBayesianInverseUniqueness

def sigma : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![pauliMatrix .I, pauliMatrix .X, pauliMatrix .Y, pauliMatrix .Z]

def pauliChannel (p : Fin 4 → ℝ) : MatrixMap (Fin 2) (Fin 2) ℂ where
  toFun A := ∑ μ, (p μ : ℂ) • (sigma μ * A * sigma μ)
  map_add' A B := by simp [Matrix.mul_add, Matrix.add_mul, smul_add, Finset.sum_add_distrib]
  map_smul' c A := by
    simp only [RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul, smul_smul,
      Finset.smul_sum, mul_comm]

def jam (N : MatrixMap (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  ∑ i, ∑ j, Matrix.kronecker (Matrix.single i j 1) (N (Matrix.single j i 1))

def IsBayesianInverse (E Eadj F : MatrixMap (Fin 2) (Fin 2) ℂ)
    (ρ : Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  IsCPTP F ∧
    (Matrix.kronecker (E ρ) 1 * jam F + jam F * Matrix.kronecker (E ρ) 1 =
      Matrix.kronecker 1 ρ * jam Eadj + jam Eadj * Matrix.kronecker 1 ρ)

def claim : Prop := ∀ p : Fin 4 → ℝ, (∀ μ, 0 ≤ p μ) → ∑ μ, p μ = 1 →
  (Finset.univ.filter fun μ => p μ ≠ 0).card = 3 →
    (∀ A B : Matrix (Fin 2) (Fin 2) ℂ,
      Matrix.trace (Aᴴ * pauliChannel p B) = Matrix.trace ((pauliChannel p A)ᴴ * B)) ∧
    ∀ ρ : Matrix (Fin 2) (Fin 2) ℂ, IsDensity ρ →
      ((∃ F, IsBayesianInverse (pauliChannel p) (pauliChannel p) F ρ) ↔
        ρ = (1 / 2 : ℂ) • 1)

private theorem sigma_properties (μ : Fin 4) : (sigma μ)ᴴ = sigma μ ∧ sigma μ * sigma μ = 1 := by
  obtain ⟨hanti, hX, hZ, hXX, hZZ⟩ := qubit_weyl_star
  change qubitXᴴ = qubitX at hX
  change qubitZᴴ = qubitZ at hZ
  rw [pow_two] at hXX hZZ
  have hXZ : qubitX * qubitZ * (qubitX * qubitZ) = -1 := by
    calc
      _ = qubitX * (qubitZ * qubitX) * qubitZ := by noncomm_ring
      _ = -(qubitX * qubitX * (qubitZ * qubitZ)) := by rw [hanti]; noncomm_ring
      _ = -1 := by rw [hXX, hZZ, mul_one]
  fin_cases μ
  · change (1 : Matrix (Fin 2) (Fin 2) ℂ)ᴴ = 1 ∧ 1 * 1 = 1
    simp
  · exact ⟨hX, hXX⟩
  · change (Complex.I • (qubitX * qubitZ))ᴴ = Complex.I • (qubitX * qubitZ) ∧
      (Complex.I • (qubitX * qubitZ)) * (Complex.I • (qubitX * qubitZ)) = 1
    constructor
    · simp [Matrix.conjTranspose_smul, hX, hZ, hanti]
    · rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Complex.I_mul_I, hXZ]
      simp
  · exact ⟨hZ, hZZ⟩

private theorem channel_self_adjoint (p : Fin 4 → ℝ)
    (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix.trace (Aᴴ * pauliChannel p B) = Matrix.trace ((pauliChannel p A)ᴴ * B) := by
  change Matrix.trace (Aᴴ * ∑ μ, (p μ : ℂ) • (sigma μ * B * sigma μ)) =
    Matrix.trace ((∑ μ, (p μ : ℂ) • (sigma μ * A * sigma μ))ᴴ * B)
  simp only [Matrix.mul_sum, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_mul, Complex.star_def, Complex.conj_ofReal, Matrix.sum_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.trace_sum, Matrix.trace_smul]
  apply Finset.sum_congr rfl
  intro μ _
  rw [(sigma_properties μ).1]
  congr 1
  calc
    _ = Matrix.trace ((Aᴴ * sigma μ) * B * sigma μ) := by congr 1; noncomm_ring
    _ = Matrix.trace (sigma μ * (Aᴴ * sigma μ) * B) := Matrix.trace_mul_cycle _ _ _

private theorem channel_unital (p : Fin 4 → ℝ) (hs : ∑ μ, p μ = 1) :
    pauliChannel p 1 = 1 := by
  change (∑ μ, (p μ : ℂ) • (sigma μ * 1 * sigma μ)) = 1
  simp only [mul_one]
  simp_rw [(sigma_properties _).2]
  rw [← Finset.sum_smul, ← Complex.ofReal_sum, hs]
  simp

private theorem channel_cptp (p : Fin 4 → ℝ) (hp : ∀ μ, 0 ≤ p μ)
    (hs : ∑ μ, p μ = 1) : IsCPTP (pauliChannel p) := by
  let K : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ := fun μ => (Real.sqrt (p μ) : ℂ) • sigma μ
  have hK : pauliChannel p = MatrixMap.of_kraus K K := by
    apply LinearMap.ext
    intro A
    change (∑ μ, (p μ : ℂ) • (sigma μ * A * sigma μ)) = MatrixMap.of_kraus K K A
    simp only [MatrixMap.of_kraus, LinearMap.sum_apply, LinearMap.coe_mk, AddHom.coe_mk]
    apply Finset.sum_congr rfl
    intro μ _
    dsimp only [K]
    rw [Matrix.conjTranspose_smul, (sigma_properties μ).1]
    simp only [Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, ← Complex.ofReal_mul, Real.mul_self_sqrt (hp μ)]
  refine ⟨hK.symm ▸ MatrixMap.of_kraus_isCompletelyPositive K, ?_⟩
  intro A
  simpa only [Matrix.conjTranspose_one, one_mul, channel_unital p hs] using
    channel_self_adjoint p 1 A

private theorem mixed_inverse (p : Fin 4 → ℝ) (hp : ∀ μ, 0 ≤ p μ)
    (hs : ∑ μ, p μ = 1) :
    IsBayesianInverse (pauliChannel p) (pauliChannel p) (pauliChannel p)
      ((1 / 2 : ℂ) • 1) := by
  refine ⟨channel_cptp p hp hs, ?_⟩
  have hh : Matrix.kronecker ((1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))
      (1 : Matrix (Fin 2) (Fin 2) ℂ) =
      Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) ((1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
    simp only [Matrix.kronecker]
    rw [Matrix.smul_kronecker, Matrix.kronecker_smul]
  rw [map_smul, channel_unital p hs, hh]


private def spin (r : Fin 3 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ∑ i, (r i : ℂ) • sigma i.succ
private def state (r : Fin 3 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 2 : ℂ) • (1 + spin r)
private theorem density_coordinates (ρ : Matrix (Fin 2) (Fin 2) ℂ) (hρ : IsDensity ρ) :
    ∃ r : Fin 3 → ℝ, ρ = state r ∧ ∑ i, (r i) ^ 2 ≤ 1 := by
  let r : Fin 3 → ℝ := ![2 * (ρ 0 1).re, -2 * (ρ 0 1).im, (ρ 0 0).re - (ρ 1 1).re]
  have h00 := congrArg Complex.im (hρ.1.isHermitian.apply 0 0)
  have h11 := congrArg Complex.im (hρ.1.isHermitian.apply 1 1)
  have h10 := hρ.1.isHermitian.apply 0 1
  have h10r := congrArg Complex.re h10
  have h10i := congrArg Complex.im h10
  simp only [Complex.star_def, Complex.conj_re] at h10r
  simp only [Complex.star_def, Complex.conj_im] at h10i
  have htr := congrArg Complex.re hρ.2
  simp only [Complex.star_def, Complex.conj_im] at h00 h11
  simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_two, Complex.add_re,
    Complex.one_re] at htr
  have heq : ρ = state r := by
    ext i j
    fin_cases i <;> fin_cases j <;> apply Complex.ext
    all_goals simp [state, spin, r, sigma, pauliMatrix, qubitX, qubitZ,
      Fin.sum_univ_three, Complex.mul_re,
      Complex.mul_im]
    all_goals linarith
  refine ⟨r, heq, ?_⟩
  have hd : 0 ≤ (Matrix.det (state r)).re := by
    rw [← heq]
    exact (Complex.nonneg_iff.mp hρ.1.det_nonneg).1
  simp [state, spin, sigma, pauliMatrix, qubitX, qubitZ,
    Matrix.det_fin_two, Fin.sum_univ_three, Complex.mul_re,
    Complex.mul_im] at hd
  simp only [Fin.sum_univ_three]
  nlinarith

private def choi (M : MatrixMap (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun (j₁, i₁) (j₂, i₂) => M (Matrix.single i₁ i₂ 1) j₁ j₂

private theorem choi_psd (M : MatrixMap (Fin 2) (Fin 2) ℂ)
    (hM : M.IsCompletelyPositive) : (choi M).PosSemidef := by
  have h_choi :
      MatrixMap.kron M (LinearMap.id : MatrixMap (Fin 2) (Fin 2) ℂ)
          (Matrix.vecMulVec (fun (x : Fin 2 × Fin 2) => if x.1 = x.2 then 1 else 0)
            (fun (x : Fin 2 × Fin 2) => star (if x.1 = x.2 then 1 else 0))) = choi M := by
    ext ⟨b₁, d₁⟩ ⟨b₂, d₂⟩
    fin_cases d₁ <;> fin_cases d₂ <;>
      simp [MatrixMap.kron_def, choi, Matrix.single, Matrix.vecMulVec]
  rw [← h_choi]
  exact hM 2 (Matrix.posSemidef_vecMulVec_self_star _)

private theorem choi_bayes (E Eadj F : MatrixMap (Fin 2) (Fin 2) ℂ)
    (ρ : Matrix (Fin 2) (Fin 2) ℂ) (h : IsBayesianInverse E Eadj F ρ) :
    Matrix.kronecker 1 (E ρ)ᵀ * choi F +
      choi F * Matrix.kronecker 1 (E ρ)ᵀ =
    Matrix.kronecker ρ 1 * choi Eadj +
      choi Eadj * Matrix.kronecker ρ 1 := by
  have hjam (N : MatrixMap (Fin 2) (Fin 2) ℂ) (i j a b : Fin 2) :
      jam N (i, a) (j, b) = N (Matrix.single j i 1) a b := by
    fin_cases i <;> fin_cases j <;> simp [jam, Matrix.single, Matrix.sum_apply]
  ext ⟨a, i⟩ ⟨b, j⟩
  have he := congrArg (fun M => M (j, a) (i, b)) h.2
  simp only [Matrix.add_apply, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.kronecker, Matrix.kronecker_apply, Matrix.one_apply, hjam] at he
  simp only [Matrix.add_apply, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.kronecker, Matrix.kronecker_apply, Matrix.one_apply, choi,
    Matrix.transpose_apply]
  simpa [mul_comm, add_comm, mul_ite, ite_mul] using he

private theorem scaled_sylvester (V C R : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (q : ℂ) (hsq : V * V = q • 1)
    (he : C + (1 / 2 : ℂ) • (V * C + C * V) = R) :
    (1 - q) • C = (1 - q / 2) • R - (1 / 2 : ℂ) • (V * R + R * V) +
      (1 / 2 : ℂ) • (V * R * V) := by
  have hleft : V * (V * C) = q • C := by
    rw [← mul_assoc, hsq, Matrix.smul_mul, one_mul]
  have hright : C * V * V = q • C := by
    rw [mul_assoc, hsq, Matrix.mul_smul, mul_one]
  have hright3 : V * C * V * V = q • (V * C) := by
    rw [mul_assoc (V * C) V V, hsq, Matrix.mul_smul, mul_one]
  simp only [← he]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  simp only [hleft, hright, ← mul_assoc V C V, Matrix.smul_mul, hright3]
  module

private def eigenvalues (p : Fin 4 → ℝ) : Fin 3 → ℝ :=
  ![p 0 + p 1 - p 2 - p 3, p 0 - p 1 + p 2 - p 3, p 0 - p 1 - p 2 + p 3]
private def outputVector (p : Fin 4 → ℝ) (r : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun i => eigenvalues p i * r i
private def ampl (s : Fin 3 → ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) (spin s)ᵀ
private def rhs (p : Fin 4 → ℝ) (r : Fin 3 → ℝ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.kronecker (state r) 1 * choi (pauliChannel p) +
    choi (pauliChannel p) * Matrix.kronecker (state r) 1
private def scaledCandidate (p : Fin 4 → ℝ) (r : Fin 3 → ℝ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  let s := outputVector p r
  let q : ℂ := (∑ i, (s i) ^ 2 : ℝ)
  (1 - q / 2) • rhs p r - (1 / 2 : ℂ) • (ampl s * rhs p r + rhs p r * ampl s) +
    (1 / 2 : ℂ) • (ampl s * rhs p r * ampl s)
private def shift : Fin 4 → Fin 4 → Fin 4 :=
  ![![0, 1, 2, 3], ![1, 0, 3, 2], ![2, 3, 0, 1], ![3, 2, 1, 0]]
private def activeWeights (k : Fin 4) (p : Fin 4 → ℝ) : Fin 3 → ℝ :=
  fun i => p (shift k i.succ)
private def witness (k : Fin 4) (p : Fin 4 → ℝ) (r : Fin 3 → ℝ) : Fin 2 × Fin 2 → ℂ :=
  fun x => ((1 - spin (fun i => (1 - activeWeights k p i) * r i)) * sigma k) x.1 x.2
private def numerator (p r : Fin 3 → ℝ) : ℝ :=
  (1 - ∑ i, ((1 - p i) * r i) ^ 2) * (∑ i, (p i) ^ 2 * (1 - p i) * (r i) ^ 2) +
    (∑ i, (p i) ^ 2 * (r i) ^ 2) * (∑ i, p i * ((1 - p i) * r i) ^ 2)

set_option maxHeartbeats 2000000 in
-- Entrywise Pauli products and complex projections require finite polynomial normalization.
private theorem channel_bloch (p : Fin 4 → ℝ) (r : Fin 3 → ℝ)
    (hp : ∀ μ, 0 ≤ p μ) (hs : ∑ μ, p μ = 1) (hr : ∑ i, (r i) ^ 2 ≤ 1) :
    pauliChannel p (state r) = state (outputVector p r) ∧
    ampl (outputVector p r) * ampl (outputVector p r) =
      ((∑ i, (outputVector p r i) ^ 2 : ℝ) : ℂ) • 1 ∧
    (∑ i, (outputVector p r i) ^ 2) ≤ 1 := by
  have hsum : p 0 + p 1 + p 2 + p 3 = 1 := by simpa [Fin.sum_univ_succ, add_assoc] using hs
  have hlast : p 3 = 1 - p 0 - p 1 - p 2 := by linarith
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> apply Complex.ext
    all_goals simp [pauliChannel, state, spin, outputVector, eigenvalues, sigma, pauliMatrix,
      qubitX, qubitZ, Matrix.mul_apply, -Matrix.cons_mul, Fin.sum_univ_succ, Complex.mul_re,
      Complex.mul_im, hlast] <;> ring
  · have hsq (s : Fin 3 → ℝ) : ampl s * ampl s =
        ((∑ i, (s i) ^ 2 : ℝ) : ℂ) • 1 := by
      ext ⟨a, i⟩ ⟨b, j⟩
      fin_cases a <;> fin_cases i <;> fin_cases b <;> fin_cases j <;> apply Complex.ext
      all_goals simp [ampl, spin, sigma, pauliMatrix, qubitX, qubitZ, Matrix.mul_apply, -Matrix.cons_mul,
        Fintype.sum_prod_type, Fin.sum_univ_succ, Matrix.one_apply, pow_two,
        Complex.mul_re, Complex.mul_im] <;> ring
    exact hsq _
  · have hlam (i : Fin 3) : (eigenvalues p i) ^ 2 ≤ 1 := by
      have hlo : -1 ≤ eigenvalues p i := by
        fin_cases i <;> simp [eigenvalues] <;> linarith [hp 0, hp 1, hp 2, hp 3]
      have hhi : eigenvalues p i ≤ 1 := by
        fin_cases i <;> simp [eigenvalues] <;> linarith [hp 0, hp 1, hp 2, hp 3]
      nlinarith [mul_nonneg (sub_nonneg.mpr hhi) (by linarith : 0 ≤ 1 + eigenvalues p i)]
    apply le_trans (Finset.sum_le_sum fun i _ => ?_) hr
    simpa only [outputVector, mul_pow, one_mul] using
      mul_le_mul_of_nonneg_right (hlam i) (sq_nonneg (r i))

private theorem witness_strict (p r : Fin 3 → ℝ) (hp : ∀ i, 0 < p i)
    (hs : ∑ i, p i = 1) (hr : ∑ i, (r i) ^ 2 ≤ 1) (hne : r ≠ 0) :
    0 < (1 - ∑ i, ((1 - p i) * r i) ^ 2) *
        (∑ i, (p i) ^ 2 * (1 - p i) * (r i) ^ 2) +
      (∑ i, (p i) ^ 2 * (r i) ^ 2) * (∑ i, p i * ((1 - p i) * r i) ^ 2) := by
  have hlt (i : Fin 3) : p i < 1 := by
    have h0 := hp 0
    have h1 := hp 1
    have h2 := hp 2
    simp only [Fin.sum_univ_three] at hs
    fin_cases i
    · change p 0 < 1; linarith
    · change p 1 < 1; linarith
    · change p 2 < 1; linarith
  obtain ⟨j, hj⟩ : ∃ j, r j ≠ 0 := by
    by_contra h
    exact hne (funext fun j => by simpa using not_exists.mp h j)
  have hj2 : 0 < (r j) ^ 2 := sq_pos_of_ne_zero hj
  have ha : 0 ≤ ∑ i, p i * ((1 - p i) * r i) ^ 2 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hp i).le (sq_nonneg _)
  have hk : 0 ≤ ∑ i, (p i) ^ 2 * (r i) ^ 2 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hb : 0 < ∑ i, (p i) ^ 2 * (1 - p i) * (r i) ^ 2 := by
    apply Finset.sum_pos'
    · intro i _
      exact mul_nonneg (mul_nonneg (sq_nonneg _) (sub_nonneg.mpr (hlt i).le)) (sq_nonneg _)
    · exact ⟨j, Finset.mem_univ _, mul_pos (mul_pos (sq_pos_of_pos (hp j))
        (sub_pos.mpr (hlt j))) hj2⟩
  have hh : (∑ i, ((1 - p i) * r i) ^ 2) < ∑ i, (r i) ^ 2 := by
    apply Finset.sum_lt_sum
    · intro i _
      rw [mul_pow]
      have hc : (1 - p i) ^ 2 ≤ 1 := by
        nlinarith [mul_nonneg (hp i).le (sub_nonneg.mpr (hlt i).le)]
      simpa using mul_le_mul_of_nonneg_right hc (sq_nonneg (r i))
    · refine ⟨j, Finset.mem_univ _, ?_⟩
      rw [mul_pow]
      have hc : (1 - p j) ^ 2 < 1 := by
        nlinarith [mul_pos (hp j) (by linarith [hlt j] : 0 < 2 - p j)]
      simpa using mul_lt_mul_of_pos_right hc hj2
  exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr (hh.trans_le hr)) hb)
    (mul_nonneg hk ha)
private theorem support_zero (p : Fin 4 → ℝ) (hp : ∀ μ, 0 ≤ p μ)
    (hc : (Finset.univ.filter fun μ => p μ ≠ 0).card = 3) :
    ∃ k, p k = 0 ∧ ∀ μ, μ ≠ k → 0 < p μ := by
  classical
  obtain ⟨k, hk⟩ : ∃ k, p k = 0 := by
    by_contra h
    have hall : ∀ k, p k ≠ 0 := fun k hk => h ⟨k, hk⟩
    have he : (Finset.univ.filter fun μ => p μ ≠ 0) = Finset.univ := by
      ext μ
      simp [hall]
    rw [he] at hc
    norm_num at hc
  refine ⟨k, hk, ?_⟩
  have he : (Finset.univ.filter fun μ => p μ ≠ 0) = Finset.univ.erase k := by
    apply Finset.eq_of_subset_of_card_le
    · intro μ hμ
      have hne := (Finset.mem_filter.mp hμ).2
      exact Finset.mem_erase.mpr ⟨fun h => hne (h.symm ▸ hk), Finset.mem_univ _⟩
    · simp [hc]
  intro μ hμ
  have hm : μ ∈ Finset.univ.filter fun μ => p μ ≠ 0 := by
    rw [he]
    exact Finset.mem_erase.mpr ⟨hμ, Finset.mem_univ _⟩
  exact lt_of_le_of_ne (hp μ) (Finset.mem_filter.mp hm).2.symm


set_option maxHeartbeats 2000000 in
-- The four zero-weight positions require finite polynomial normalization of a Choi quadratic form.
set_option maxRecDepth 4096 in
private theorem witness_numerator (p : Fin 4 → ℝ) (r : Fin 3 → ℝ) (k : Fin 4)
    (hs : ∑ μ, p μ = 1) (hk : p k = 0) :
    (star (witness k p r) ⬝ᵥ (scaledCandidate p r *ᵥ witness k p r)).re =
      -4 * numerator (activeWeights k p) r := by
  simp [Fin.sum_univ_succ] at hs
  fin_cases k
  · change p 0 = 0 at hk
    have hlast : p 3 = 1 - p 0 - p 1 - p 2 := by linarith
    simp [witness, scaledCandidate, rhs, ampl, outputVector, eigenvalues, state, spin,
      activeWeights, shift, numerator, pauliChannel, choi,
      sigma, pauliMatrix, qubitX, qubitZ, dotProduct, Matrix.mulVec, Matrix.mul_apply, -Matrix.cons_mul,
      Fintype.sum_prod_type, Fin.sum_univ_succ, Matrix.single,
      Matrix.one_apply, pow_two, Complex.mul_re, Complex.mul_im, hk, hlast]
    ring
  · change p 1 = 0 at hk
    have hlast : p 2 = 1 - p 0 - p 1 - p 3 := by linarith
    simp [witness, scaledCandidate, rhs, ampl, outputVector, eigenvalues, state, spin,
      activeWeights, shift, numerator, pauliChannel, choi,
      sigma, pauliMatrix, qubitX, qubitZ, dotProduct, Matrix.mulVec, Matrix.mul_apply, -Matrix.cons_mul,
      Fintype.sum_prod_type, Fin.sum_univ_succ, Matrix.single,
      Matrix.one_apply, pow_two, Complex.mul_re, Complex.mul_im, hk, hlast]
    ring
  · change p 2 = 0 at hk
    have hlast : p 1 = 1 - p 0 - p 2 - p 3 := by linarith
    simp [witness, scaledCandidate, rhs, ampl, outputVector, eigenvalues, state, spin,
      activeWeights, shift, numerator, pauliChannel, choi,
      sigma, pauliMatrix, qubitX, qubitZ, dotProduct, Matrix.mulVec, Matrix.mul_apply, -Matrix.cons_mul,
      Fintype.sum_prod_type, Fin.sum_univ_succ, Matrix.single,
      Matrix.one_apply, pow_two, Complex.mul_re, Complex.mul_im, hk, hlast]
    ring
  · change p 3 = 0 at hk
    have hlast : p 0 = 1 - p 1 - p 2 - p 3 := by linarith
    simp [witness, scaledCandidate, rhs, ampl, outputVector, eigenvalues, state, spin,
      activeWeights, shift, numerator, pauliChannel, choi,
      sigma, pauliMatrix, qubitX, qubitZ, dotProduct, Matrix.mulVec, Matrix.mul_apply, -Matrix.cons_mul,
      Fintype.sum_prod_type, Fin.sum_univ_succ, Matrix.single,
      Matrix.one_apply, pow_two, Complex.mul_re, Complex.mul_im, hk, hlast]
    ring

private theorem inverse_only_mixed (p : Fin 4 → ℝ) (hp : ∀ μ, 0 ≤ p μ)
    (hs : ∑ μ, p μ = 1) (hc : (Finset.univ.filter fun μ => p μ ≠ 0).card = 3)
    (ρ : Matrix (Fin 2) (Fin 2) ℂ) (hρ : IsDensity ρ)
    (F : MatrixMap (Fin 2) (Fin 2) ℂ)
    (hF : IsBayesianInverse (pauliChannel p) (pauliChannel p) F ρ) :
    ρ = (1 / 2 : ℂ) • 1 := by
  obtain ⟨r, hstate, hr⟩ := density_coordinates ρ hρ
  subst ρ
  by_contra hmix
  have hne : r ≠ 0 := by
    intro hz
    subst r
    simp [state, spin] at hmix
  obtain ⟨k, hk, hpos⟩ := support_zero p hp hc
  have hq (i : Fin 3) : 0 < activeWeights k p i := by
    apply hpos
    fin_cases k <;> fin_cases i <;> decide
  have hqs : ∑ i, activeWeights k p i = 1 := by
    have hsum : p 0 + p 1 + p 2 + p 3 = 1 := by simpa [Fin.sum_univ_succ, add_assoc] using hs
    fin_cases k
    · change p 0 = 0 at hk
      simp [activeWeights, shift, Fin.sum_univ_succ]
      linarith
    · change p 1 = 0 at hk
      simp [activeWeights, shift, Fin.sum_univ_succ]
      linarith
    · change p 2 = 0 at hk
      simp [activeWeights, shift, Fin.sum_univ_succ]
      linarith
    · change p 3 = 0 at hk
      simp [activeWeights, shift, Fin.sum_univ_succ]
      linarith
  have hnum : 0 < numerator (activeWeights k p) r :=
    witness_strict (activeWeights k p) r hq hqs hr hne
  obtain ⟨he, hvsq, hnorm⟩ := channel_bloch p r hp hs hr
  let s := outputVector p r
  have hL : Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) (state s)ᵀ =
      (1 / 2 : ℂ) • (1 + ampl s) := by
    simp only [state, ampl, Matrix.kronecker, Matrix.transpose_smul,
      Matrix.transpose_add, Matrix.transpose_one]
    rw [Matrix.kronecker_smul, Matrix.kronecker_add, Matrix.one_kronecker_one]
  have hEq : choi F + (1 / 2 : ℂ) •
      (ampl s * choi F + choi F * ampl s) = rhs p r := by
    have hb := choi_bayes (pauliChannel p) (pauliChannel p) F (state r) hF
    rw [he, hL] at hb
    calc
      _ = ((1 / 2 : ℂ) • (1 + ampl s)) * choi F +
          choi F * ((1 / 2 : ℂ) • (1 + ampl s)) := by
        simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add,
          one_mul, mul_one]
        module
      _ = rhs p r := hb
  have hscaled := scaled_sylvester (ampl s) (choi F) (rhs p r)
    ((∑ i, (s i) ^ 2 : ℝ) : ℂ) hvsq hEq
  have hsc : scaledCandidate p r =
      (1 - ((∑ i, (s i) ^ 2 : ℝ) : ℂ)) • choi F := hscaled.symm
  have hcoef : 0 ≤ (1 - ((∑ i, (s i) ^ 2 : ℝ) : ℂ)) := by
    apply Complex.nonneg_iff.mpr
    constructor
    · change 0 ≤ 1 - ∑ i, (outputVector p r i) ^ 2
      exact sub_nonneg.mpr hnorm
    · simp [pow_two, Complex.mul_im]
  have hC : (choi F).PosSemidef := choi_psd F hF.1.1
  have hscC : (scaledCandidate p r).PosSemidef := by
    rw [hsc]
    exact hC.smul hcoef
  have heval := (Complex.nonneg_iff.mp
    (hscC.dotProduct_mulVec_nonneg (witness k p r))).1
  rw [witness_numerator p r k hs hk] at heval
  linarith

theorem result : claim := by
  intro p hp hs hc
  refine ⟨channel_self_adjoint p, ?_⟩
  intro ρ hρ
  constructor
  · rintro ⟨F, hF⟩
    exact inverse_only_mixed p hp hs hc ρ hρ F hF
  · rintro rfl
    exact ⟨pauliChannel p, mixed_inverse p hp hs⟩


end D5.S3.QuantumChannels.PauliThreeWeightBayesianInverseUniqueness
