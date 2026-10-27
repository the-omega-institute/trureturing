/- GID: D5/S3/Quantum/Recovery/BurriReverseSource
   generality: I
   mirror-B: D5/B/S3/Quantum/Recovery/BurriReverseSource
   mirror-E: none(waiver:unfinished-source-identification)
   anchors: []
   utility: none
   digest: Literal complementary state and padded source polar construction. -/

import D5.S3.Quantum.Recovery.BurriReversePetz

/-! The complementary state is computed from the physical purified isometry. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Kronecker
open Matrix
open D5.S3.Quantum.Recovery.BurriReverseDecoder
open D5.S3.Quantum.Recovery.BurriReversePolar
open D5.S3.Quantum.Recovery.BurriReversePetz
open D5.S3.Quantum.Information.PartialTraceMutualInformation

namespace D5.S3.Quantum.Recovery.BurriReverseSource

def lift (Z : Matrix B B ℂ) : Matrix P P ℂ := inject * Z * injectᴴ
def pad (Z : Matrix B B ℂ) : Matrix P P ℂ := lift Z + (1 - lift 1)

theorem inject_mul {n : Type*} [Fintype n] (Z : Matrix B n ℂ) (p : P) (b : n) :
    (inject * Z) p b = if active p.2 then Z (p.1, p.2.2.2) b else 0 := by
  by_cases hp : active p.2 <;>
    simp [Matrix.mul_apply, inject, hp]

theorem mul_inject_adjoint {n : Type*} [Fintype n] (Z : Matrix n B ℂ) (b : n) (p : P) :
    (Z * injectᴴ) b p = if active p.2 then Z b (p.1, p.2.2.2) else 0 := by
  by_cases hp : active p.2 <;>
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, inject, hp]

theorem injection_isometry : injectᴴ * inject = 1 := by
  ext ⟨i, a⟩ ⟨j, b⟩
  fin_cases i <;> fin_cases a <;> fin_cases j <;> fin_cases b <;>
    norm_num [inject, active, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three]

theorem lift_apply (Z : Matrix B B ℂ) (p q : P) :
    lift Z p q = if active p.2 ∧ active q.2 then
      Z (p.1, p.2.2.2) (q.1, q.2.2.2) else 0 := by
  unfold lift
  rw [mul_inject_adjoint, inject_mul]
  by_cases hp : active p.2 <;> by_cases hq : active q.2 <;> simp [hp, hq]

theorem lift_mul (Z T : Matrix B B ℂ) : lift Z * lift T = lift (Z * T) := by
  simp only [lift, Matrix.mul_assoc, ← Matrix.mul_assoc injectᴴ inject,
    injection_isometry, Matrix.one_mul]

theorem lift_adjoint (Z : Matrix B B ℂ) : (lift Z)ᴴ = lift Zᴴ := by
  simp only [lift, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_assoc]

theorem lift_add (Z T : Matrix B B ℂ) : lift (Z + T) = lift Z + lift T := by
  simp only [lift, Matrix.mul_add, Matrix.add_mul]

theorem lift_smul (c : ℂ) (Z : Matrix B B ℂ) : lift (c • Z) = c • lift Z := by
  simp only [lift, Matrix.mul_smul, Matrix.smul_mul]

theorem pad_mul (Z T : Matrix B B ℂ) : pad Z * pad T = pad (Z * T) := by
  have hZ : lift Z * lift 1 = lift Z := by rw [lift_mul, Matrix.mul_one]
  have hT : lift 1 * lift T = lift T := by rw [lift_mul, Matrix.one_mul]
  have hQ : lift 1 * lift 1 = lift 1 := by rw [lift_mul, Matrix.one_mul]
  unfold pad
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.one_mul, Matrix.mul_one, lift_mul, Matrix.mul_one, Matrix.one_mul]
  abel

theorem pad_adjoint (Z : Matrix B B ℂ) : (pad Z)ᴴ = pad Zᴴ := by
  simp only [pad, Matrix.conjTranspose_add, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_one, lift_adjoint]

theorem pad_one : pad (1 : Matrix B B ℂ) = 1 := by unfold pad; abel

theorem pad_unitary (Z : Matrix B B ℂ) (hZ : Zᴴ * Z = 1 ∧ Z * Zᴴ = 1) :
    (pad Z)ᴴ * pad Z = 1 ∧ pad Z * (pad Z)ᴴ = 1 := by
  simp only [pad_adjoint, pad_mul, hZ.1, hZ.2, pad_one, and_self]

theorem source_unitary_identification :
    sourceU (cosine 4) (cosine 2) (sine 4) (sine 2) = pad U := by
  ext ⟨i, j, k, a⟩ ⟨l, m, n, b⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases a <;>
    fin_cases l <;> fin_cases m <;> fin_cases n <;> fin_cases b <;>
    simp [sourceU, pad, lift_apply, U, active, Matrix.one_apply]

/-- The actual canonical reference purification followed by the physical isometry. -/
def purifiedAmplitude : Matrix P B ℂ := fun p b =>
  V (b, p.2) p.1 / (Real.sqrt 2 : ℂ)
def physicalState : Matrix (B × P) (B × P) ℂ :=
  Matrix.vecMulVec (fun p => purifiedAmplitude p.2 p.1)
    (star (fun p => purifiedAmplitude p.2 p.1))
def X : Matrix P P ℂ := partialTraceLeft physicalState
def sigmaE : Matrix E E ℂ := Matrix.diagonal fun e =>
  if active e then (if e.2.2 = 0 then (11 : ℂ) else 10) / 31 else 0

theorem radical_product : (Real.sqrt 2 : ℂ) * (Real.sqrt 31 : ℂ) = Real.sqrt 62 := by
  have h : Real.sqrt 2 * Real.sqrt 31 = Real.sqrt 62 := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  exact_mod_cast h

theorem purified_amplitude : purifiedAmplitude =
    (1 / (Real.sqrt 62 : ℂ)) • (inject * Y) := by
  ext p b
  rw [Matrix.smul_apply, inject_mul]
  unfold purifiedAmplitude V
  by_cases hp : active p.2
  · simp only [hp, ↓reduceIte]
    rw [div_div, mul_comm (Real.sqrt 31 : ℂ), radical_product]
    simp [div_eq_mul_inv, mul_comm]
  · simp [hp]

theorem complementary_state : X = lift output := by
  have hx : X = purifiedAmplitude * purifiedAmplitudeᴴ := by
    ext p q
    simp only [X, partialTraceLeft, physicalState, Matrix.vecMulVec_apply,
      Pi.star_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [hx, purified_amplitude, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_mul, amplitude_adjoint, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul]
  have hs : (Real.sqrt 62 : ℂ) * (Real.sqrt 62 : ℂ) = 62 := by
    exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 62)
  simp only [star_div₀, star_one, Complex.star_def, map_ofReal, one_div_mul_one_div, hs]
  simp only [output, lift, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]

set_option maxHeartbeats 4000000 in
theorem physical_marginals : partialTraceRight X = rho ∧ partialTraceLeft X = sigmaE := by
  rw [complementary_state]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [partialTraceRight, lift_apply, output, active, rho, Y, amplitude, sign,
        Matrix.mul_apply, Matrix.one_apply, Fintype.sum_prod_type,
        Fin.sum_univ_two, Fin.sum_univ_three]
  · ext ⟨i, j, a⟩ ⟨k, l, b⟩
    fin_cases i <;> fin_cases j <;> fin_cases a <;>
      fin_cases k <;> fin_cases l <;> fin_cases b <;>
      norm_num [partialTraceLeft, lift_apply, output, active, sigmaE, Y, amplitude, sign,
        Matrix.mul_apply, Matrix.diagonal_apply, Fintype.sum_prod_type,
        Fin.sum_univ_two, Fin.sum_univ_three]

theorem complementary_root : CFC.sqrt X =
    (1 / (Real.sqrt 62 : ℂ)) • lift Y := by
  have hp : (lift Y).PosSemidef :=
    amplitude_positive.posSemidef.mul_mul_conjTranspose_same inject
  apply CFC.sqrt_unique _ (hp.smul (by
    norm_num [Complex.nonneg_iff, Complex.div_re, Complex.div_im])).nonneg
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, lift_mul,
    one_div_mul_one_div]
  have hs : (Real.sqrt 62 : ℂ) * (Real.sqrt 62 : ℂ) = 62 := by
    exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 62)
  rw [hs, complementary_state, output, lift_smul]

def D : Matrix B B ℂ := Matrix.diagonal fun b => if b.2 = 0 then (s : ℂ) else t
def sqrtQ : Matrix P P ℂ := (1 / (Real.sqrt 62 : ℂ)) • lift D
/-- Appendix A's source matrix, with its transpose in the displayed marginal eigenbases. -/
def M : Matrix P P ℂ := (CFC.sqrt (Matrix.kronecker rho sigmaE) * CFC.sqrt X).transpose

theorem lift_diagonal (v : B → ℂ) : lift (Matrix.diagonal v) =
    Matrix.diagonal (fun p : P => if active p.2 then v (p.1, p.2.2.2) else 0) := by
  ext ⟨i, j, k, a⟩ ⟨l, m, n, b⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases a <;>
    fin_cases l <;> fin_cases m <;> fin_cases n <;> fin_cases b <;>
    simp [lift_apply, active, Matrix.diagonal_apply]

theorem product_marginal_root : CFC.sqrt (Matrix.kronecker rho sigmaE) = sqrtQ := by
  have hd : D.PosSemidef := by
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro b
    dsimp [D]
    split_ifs <;> simp [s, t, Complex.nonneg_iff, Real.sqrt_nonneg]
  have hp : sqrtQ.PosSemidef :=
    (hd.mul_mul_conjTranspose_same inject).smul (by
      norm_num [Complex.nonneg_iff, Complex.div_re, Complex.div_im])
  apply CFC.sqrt_unique _ hp.nonneg
  rw [sqrtQ, Matrix.smul_mul, Matrix.mul_smul, smul_smul, lift_mul,
    one_div_mul_one_div]
  have hs : (Real.sqrt 62 : ℂ) * (Real.sqrt 62 : ℂ) = 62 := by
    exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 62)
  rw [hs, D, Matrix.diagonal_mul_diagonal, lift_diagonal]
  ext ⟨i, j, k, a⟩ ⟨l, m, n, b⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases a <;>
    fin_cases l <;> fin_cases m <;> fin_cases n <;> fin_cases b <;>
    norm_num [rho, sigmaE, active, s, t, Matrix.diagonal_apply,
      Matrix.kroneckerMap_apply, Matrix.one_apply, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 11),
      Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 10)]

theorem source_matrix : M = lift activeM := by
  rw [M, product_marginal_root, complementary_root, sqrtQ,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, one_div_mul_one_div, lift_mul]
  have hs : (Real.sqrt 62 : ℂ) * (Real.sqrt 62 : ℂ) = 62 := by
    exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 62)
  rw [hs]
  ext p q
  simp only [Matrix.transpose_apply, Matrix.smul_apply, lift_apply,
    activeM, Matrix.smul_apply, Matrix.mul_diagonal, D, Matrix.diagonal_mul]
  by_cases hp : active p.2 <;> by_cases hq : active q.2 <;> simp [hp, hq]
  have hy : Y (q.1, q.2.2.2) (p.1, p.2.2.2) =
      Y (p.1, p.2.2.2) (q.1, q.2.2.2) := by
    have h := congrFun (congrFun amplitude_adjoint (p.1, p.2.2.2)) (q.1, q.2.2.2)
    simpa only [Matrix.conjTranspose_apply, Y, map_ofReal] using h
  rw [hy]
  ring

theorem full_polar_positive : (M * pad U).PosSemidef := by
  have h : M * pad U = lift (activeM * U) := by
    rw [source_matrix, pad, Matrix.mul_add, Matrix.mul_sub,
      Matrix.mul_one, lift_mul, lift_mul, Matrix.mul_one, sub_self, add_zero]
  rw [h]
  exact actual_polar_positive.mul_mul_conjTranspose_same inject

#print axioms injection_isometry
#print axioms source_unitary_identification
#print axioms purified_amplitude
#print axioms complementary_state
#print axioms physical_marginals
#print axioms complementary_root
#print axioms product_marginal_root
#print axioms source_matrix
#print axioms full_polar_positive

end D5.S3.Quantum.Recovery.BurriReverseSource
