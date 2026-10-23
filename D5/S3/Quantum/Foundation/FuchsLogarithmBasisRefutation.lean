/- GID: D5/S3/Quantum/Foundation/FuchsLogarithmBasisRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Foundation/FuchsLogarithmBasisRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Foundation/FuchsLogarithmBasisRefutation.claim; result=D5/S3/Quantum/Foundation/FuchsLogarithmBasisRefutation.result; claim=D5/S3/Quantum/Foundation/FuchsLogarithmBasisRefutation.claim
   digest: A faithful qutrit counterexample refutes the physical-basis diagonalization question. -/

/-
The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).
proof_shape: result: bind-only; admission_basis: open-problem-resolution (#18588; Refuted).
Direct frozen dependencies: PathSpectralClassical.relativeCongruence;
EntropyProductionCoherenceDeletionIdentity.cfc_diagonal.
escape_witness: none.
Consumed bind-only helpers: liftU_unitary (K_conj, physical_obstruction);
sqrt_diag (sqrt_rho0); unitary_column_ne_zero (physical_obstruction).
The claim keeps the source's literal Kronecker-sum logarithm argument; proofs use the existing relativeCongruence construction and pinned identities.
-/

import D5.S3.Resource.LogDet.PathSpectralClassical
import D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity

set_option autoImplicit false

noncomputable section

namespace D5.S3.Quantum.Foundation.FuchsLogarithmBasisRefutation

open Matrix
open scoped Kronecker MatrixOrder ComplexOrder

variable {d : ℕ}

/-- The Kronecker sum `X ⊕ X* = I ⊗ X + X* ⊗ I` of eqs. (3.237) and (3.242). -/
def ksum (X : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  (1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ X + X.map star ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)

/-- The matrix in the logarithm of eq. (3.244): `I + t ρ̃₀^{-1/2} Δ̃ ρ̃₀^{-1/2}`, with `ρ̃₀ = ρ₀ ⊕ ρ₀*`,
`Δ̃ = Δ ⊕ Δ*`, `Δ = ρ₁ - ρ₀`. -/
def logArg (ρ₀ ρ₁ : Matrix (Fin d) (Fin d) ℂ) (t : ℝ) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  1 + (t : ℂ) • ((CFC.sqrt (ksum ρ₀))⁻¹ * ksum (ρ₁ - ρ₀) * (CFC.sqrt (ksum ρ₀))⁻¹)

/-- The open question of §3.5.3: for invertible states `ρ₀, ρ₁` with invertible `Δ`, there is a basis
(a unitary change of basis `U`) in which the matrix in the logarithm is diagonal. -/
def claim : Prop :=
  ∀ (d : ℕ) (ρ₀ ρ₁ : Matrix (Fin d) (Fin d) ℂ), ρ₀.PosDef → ρ₁.PosDef →
    ρ₀.trace = 1 → ρ₁.trace = 1 → (ρ₁ - ρ₀).det ≠ 0 →
    ∀ t : ℝ, 0 < t → t ≤ 1 →
      ∃ U ∈ unitaryGroup (Fin d) ℂ,
        (logArg (star U * ρ₀ * U) (star U * ρ₁ * U) t).IsDiag

end D5.S3.Quantum.Foundation.FuchsLogarithmBasisRefutation


namespace D5.S3.Quantum.Foundation.FuchsLogarithmBasisRefutation
open Matrix
open scoped MatrixOrder ComplexOrder Kronecker
variable {n : ℕ}

private def liftU (U : Matrix (Fin n) (Fin n) ℂ) := U.map star ⊗ₖ U

private lemma conj_map_mul (A B : Matrix (Fin n) (Fin n) ℂ) :
    (A * B).map star = A.map star * B.map star := by
  exact Matrix.map_mul (f := starRingEnd ℂ)

private lemma liftU_unitary (U : Matrix (Fin n) (Fin n) ℂ) (hU : U ∈ unitaryGroup (Fin n) ℂ) :
    liftU U ∈ unitaryGroup (Fin n × Fin n) ℂ := by
  exact Matrix.kronecker_mem_unitary (Matrix.map_star_mem_unitaryGroup_iff.mpr hU) hU

private lemma ksum_conj (R U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ unitaryGroup (Fin n) ℂ) :
    ksum (star U * R * U) = star (liftU U) * ksum R * liftU U := by
  have hUU := mem_unitaryGroup_iff'.mp hU
  have hUc := mem_unitaryGroup_iff'.mp (map_star_mem_unitaryGroup_iff.mpr hU)
  simp only [ksum, liftU, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
    Matrix.mul_add, Matrix.add_mul]
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  simp only [Matrix.mul_one, ← Matrix.star_eq_conjTranspose,
    hUU, hUc, conj_map_mul]
  congr 2

private lemma sqrt_conj {ι : Type*} [Fintype ι] [DecidableEq ι] (A W : Matrix ι ι ℂ)
    (hW : W ∈ unitaryGroup ι ℂ) :
    CFC.sqrt (star W * A * W) = star W * CFC.sqrt A * W := by
  by_cases hA : 0 ≤ A
  · apply CFC.sqrt_unique
    · simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc W (star W), mem_unitaryGroup_iff.mp hW]
      simp only [Matrix.one_mul, ← Matrix.mul_assoc]
      rw [Matrix.mul_assoc (star W), CFC.sqrt_mul_sqrt_self A hA]
    · exact star_left_conjugate_nonneg (CFC.sqrt_nonneg A) W
  · have hWA : ¬ 0 ≤ star W * A * W := by
      exact fun hw => hA ((Unitary.isUnit_coe (U := (⟨W, hW⟩ : unitary (Matrix ι ι ℂ)))).star_left_conjugate_nonneg_iff.mp hw)
    simp [CFC.sqrt_of_not_nonneg hA, CFC.sqrt_of_not_nonneg hWA]

private lemma ksum_vec (R X : Matrix (Fin n) (Fin n) ℂ) (hR : R.IsHermitian) :
    ksum R *ᵥ X.vec = (R * X + X * R).vec := by
  simp only [ksum, Matrix.add_mulVec, Matrix.kronecker_mulVec_vec, Matrix.transpose_one,
    Matrix.mul_one, Matrix.one_mul, Matrix.vec_add]
  congr 2
  exact congrArg (fun A => X * A) hR.eq


private lemma inv_conj {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A W : Matrix ι ι ℂ) (hW : W ∈ unitaryGroup ι ℂ) :
    (star W * A * W)⁻¹ = star W * A⁻¹ * W := by
  have hi : W⁻¹ = star W := Matrix.inv_eq_left_inv (mem_unitaryGroup_iff'.mp hW)
  have his : (star W)⁻¹ = W := Matrix.inv_eq_left_inv (mem_unitaryGroup_iff.mp hW)
  simp only [Matrix.mul_inv_rev, hi, his, Matrix.mul_assoc]

private lemma K_conj (R D U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ unitaryGroup (Fin n) ℂ) :
    D5.S3.Resource.LogDet.PathSpectralClassical.relativeCongruence (ksum (star U * D * U)) (ksum (star U * R * U)) = star (liftU U) * D5.S3.Resource.LogDet.PathSpectralClassical.relativeCongruence (ksum D) (ksum R) * liftU U := by
  have hW := liftU_unitary U hU
  simp only [D5.S3.Resource.LogDet.PathSpectralClassical.relativeCongruence, ksum_conj _ _ hU, sqrt_conj _ _ hW, inv_conj _ _ hW]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (liftU U) (star (liftU U)), mem_unitaryGroup_iff.mp hW]
  simp only [Matrix.one_mul]
  rw [← Matrix.mul_assoc (liftU U) (star (liftU U)), mem_unitaryGroup_iff.mp hW]
  simp only [Matrix.one_mul]

private lemma ksum_add (A B : Matrix (Fin n) (Fin n) ℂ) :
    ksum (A + B) = ksum A + ksum B := by
  ext i j
  simp [ksum, Matrix.kroneckerMap_apply, Matrix.map_apply]
  ring

private lemma ksum_real_smul (a : ℝ) (A : Matrix (Fin n) (Fin n) ℂ) :
    ksum ((a : ℂ) • A) = (a : ℂ) • ksum A := by
  ext i j
  simp [ksum, Matrix.kroneckerMap_apply, Matrix.map_apply]
  ring

open Matrix
open scoped MatrixOrder ComplexOrder Kronecker

private def rho0 : Matrix (Fin 3) (Fin 3) ℂ := diagonal ![1/2, 1/3, 1/6]
private def rho1 : Matrix (Fin 3) (Fin 3) ℂ := !![7/16, -1/16, 0; -1/16, 5/16, 0; 0, 0, 1/4]
private def gramRow : Matrix (Fin 3) (Fin 3) ℂ := !![1/4, -1/4, 0; 0, 0, 0; 0, 0, 0]

private theorem rho0_posDef : rho0.PosDef := by
  apply Matrix.PosDef.diagonal
  intro i
  fin_cases i <;> norm_num

private theorem rho1_decomp : rho1 = diagonal ![3/8, 1/4, 1/4] + gramRowᴴ * gramRow := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [rho1, gramRow, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.conjTranspose_apply, map_ofNat]

private theorem rho1_posDef : rho1.PosDef := by
  rw [rho1_decomp]
  refine Matrix.PosDef.add_posSemidef ?_ (Matrix.posSemidef_conjTranspose_mul_self gramRow)
  apply Matrix.PosDef.diagonal (R := ℂ)
  intro i
  fin_cases i <;> norm_num

private theorem rho0_trace : rho0.trace = 1 := by
  norm_num [rho0, Matrix.trace, Matrix.diag, Fin.sum_univ_succ]

private theorem rho1_trace : rho1.trace = 1 := by
  norm_num [rho1, Matrix.trace, Matrix.diag, Fin.sum_univ_succ]

private theorem delta_det : (rho1 - rho0).det = -1/4608 := by
  norm_num [rho1, rho0, Matrix.det_fin_three]


private def H : Matrix (Fin 3) (Fin 3) ℂ := !![1/16, -1/16, 0; -1/16, 1/16, 0; 0, 0, 1/8]
private def P : Matrix (Fin 3) (Fin 3) ℂ := !![1,1,0;1,1,0;0,0,0]

private lemma kernel_H (X : Matrix (Fin 3) (Fin 3) ℂ) (h : H * X + X * H = 0) :
    X = X 0 0 • P := by
  have h00 := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℂ => A 0 0) h
  have h01 := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℂ => A 0 1) h
  have h10 := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℂ => A 1 0) h
  have h02 := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℂ => A 0 2) h
  have h12 := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℂ => A 1 2) h
  have h20 := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℂ => A 2 0) h
  have h21 := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℂ => A 2 1) h
  have h22 := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℂ => A 2 2) h
  norm_num [H, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ] at h00 h01 h10 h02 h12 h20 h21 h22
  have h01' : X 0 1 = X 0 0 := by linear_combination -8 * h00 + 4 * h01 - 4 * h10
  have h10' : X 1 0 = X 0 0 := by linear_combination -8 * h00 - 4 * h01 + 4 * h10
  have h11' : X 1 1 = X 0 0 := by linear_combination -16 * h00 - 8 * h01 - 8 * h10
  have h02' : X 0 2 = 0 := by linear_combination 6 * h02 + 2 * h12
  have h12' : X 1 2 = 0 := by linear_combination 2 * h02 + 6 * h12
  have h20' : X 2 0 = 0 := by linear_combination 6 * h20 + 2 * h21
  have h21' : X 2 1 = 0 := by linear_combination 2 * h20 + 6 * h21
  have h22' : X 2 2 = 0 := by linear_combination 4 * h22
  ext i j
  fin_cases i <;> fin_cases j <;> simp [P, h01', h10', h11', h02', h12', h20', h21', h22']

private lemma H_hermitian : H.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [H, Matrix.conjTranspose_apply]

private lemma HP : H * P + P * H = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [H,P,Matrix.mul_apply,Fin.sum_univ_succ]

open Matrix
open scoped MatrixOrder ComplexOrder Kronecker

private lemma sqrt_diag {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ι → ℝ) (hr : ∀ i, 0 ≤ r i) :
    CFC.sqrt (diagonal (fun i => (r i : ℂ))) =
      diagonal (fun i => (Real.sqrt (r i) : ℂ)) := by
  have hP : (Matrix.diagonal (fun i => (r i : ℂ))).PosSemidef :=
    Matrix.PosSemidef.diagonal (fun i => Complex.zero_le_real.mpr (hr i))
  rw [CFC.sqrt_eq_real_sqrt _ hP.nonneg, cfcₙ_eq_cfc]
  exact D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity.cfc_diagonal Real.sqrt r

private def rates : Fin 3 → ℝ := ![1/2,1/3,1/6]
private def S : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  diagonal (fun ij => (Real.sqrt (rates ij.1 + rates ij.2) : ℂ))
private def M : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1, (Real.sqrt (5/6) : ℂ), 0; (Real.sqrt (5/6) : ℂ), (Real.sqrt (2/3) : ℂ), 0; 0,0,0]

private lemma sqrt_minor : (Real.sqrt (2/3) : ℂ) - (Real.sqrt (5/6) : ℂ)^2 ≠ 0 := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5/6),
    ← Complex.ofReal_sub, ne_eq, Complex.ofReal_eq_zero]
  intro h
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2/3)
  have he : Real.sqrt (2/3) = 5/6 := sub_eq_zero.mp h
  rw [he] at hs
  norm_num at hs

private lemma M_minor : M 0 0 * M 1 1 - M 0 1 * M 1 0 ≠ 0 := by
  simpa [M, pow_two] using sqrt_minor

open Matrix
open scoped MatrixOrder ComplexOrder Kronecker

private lemma diagonal_has_eigen_column {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A W : Matrix ι ι ℂ) (lam : ℂ) (x : ι → ℂ)
    (hx : x ≠ 0) (he : A *ᵥ x = lam • x)
    (hW : W * star W = 1)
    (hd : (star W * A * W).IsDiag) :
    ∃ p, A *ᵥ W.col p = lam • W.col p := by
  let y := star W *ᵥ x
  have hWy : W *ᵥ y = x := by simp [y, Matrix.mulVec_mulVec, hW]
  have hy : y ≠ 0 := by
    intro h
    apply hx
    rw [← hWy, h, Matrix.mulVec_zero]
  obtain ⟨p, hp⟩ : ∃ p, y p ≠ 0 := Function.ne_iff.mp hy
  have he' : (star W * A * W) *ᵥ y = lam • y := by
    simp only [← Matrix.mulVec_mulVec, hWy, he, Matrix.mulVec_smul]
    rfl
  have hpp : (star W * A * W) p p = lam := by
    have hh := congrFun he' p
    rw [← hd.diagonal_diag] at hh
    simp only [Matrix.mulVec_diagonal, Matrix.diag_apply, Pi.smul_apply, smul_eq_mul] at hh
    exact mul_right_cancel₀ hp hh
  have hep : (star W * A * W) *ᵥ Pi.single p 1 = lam • Pi.single p 1 := by
    rw [← hd.diagonal_diag, Matrix.diagonal_mulVec_single]
    simp only [Matrix.diag_apply,hpp,mul_one]
    ext i
    by_cases hi : i = p <;> simp [hi]
  refine ⟨p, ?_⟩
  have hh := congrArg (fun z => W *ᵥ z) hep
  simp only [Matrix.mulVec_smul, Matrix.mulVec_mulVec] at hh
  have hm : W * (star W * A * W) = A * W := by
    simp only [← Matrix.mul_assoc, hW, Matrix.one_mul]
  rw [hm] at hh
  simpa only [Matrix.mulVec_single_one, Matrix.col_mul_eq_mulVec_col] using hh

private lemma unitary_column_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : Matrix ι ι ℂ) (hW : star W * W = 1) (p : ι) : W.col p ≠ 0 := by
  exact (Matrix.linearIndependent_cols_of_det_ne_zero (Matrix.UnitaryGroup.det_isUnit
    (⟨W, mem_unitaryGroup_iff'.mpr hW⟩ : unitaryGroup ι ℂ)).ne_zero).ne_zero p

private lemma product_column_minor (U : Matrix (Fin 3) (Fin 3) ℂ) (p : Fin 3 × Fin 3) :
    (U.map star ⊗ₖ U) (0,0) p * (U.map star ⊗ₖ U) (1,1) p -
      (U.map star ⊗ₖ U) (1,0) p * (U.map star ⊗ₖ U) (0,1) p = 0 := by
  simp only [Matrix.kroneckerMap_apply, Matrix.map_apply]
  ring

private lemma rates_pos (i : Fin 3) : 0 < rates i := by
  fin_cases i <;> norm_num [rates]

private lemma ksum_rho0 : ksum rho0 = diagonal (fun ij => ((rates ij.1 + rates ij.2 : ℝ) : ℂ)) := by
  ext ⟨i,j⟩ ⟨k,l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [ksum,rho0,rates,Matrix.kroneckerMap_apply,map_ofNat]

private lemma sqrt_rho0 : CFC.sqrt (ksum rho0) = S := by
  rw [ksum_rho0]
  exact sqrt_diag _ (fun ij => (add_pos (rates_pos _) (rates_pos _)).le)

private lemma S_posDef : S.PosDef := by
  apply Matrix.PosDef.diagonal
  intro ij
  exact_mod_cast Real.sqrt_pos.mpr (add_pos (rates_pos ij.1) (rates_pos ij.2))

private lemma S_mul_inv : S * S⁻¹ = 1 := by
  exact Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det S).mp S_posDef.isUnit)

private lemma S_inv_mul : S⁻¹ * S = 1 := by
  exact Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det S).mp S_posDef.isUnit)

private lemma S_sq : S * S = ksum rho0 := by
  rw [← sqrt_rho0]
  apply CFC.sqrt_mul_sqrt_self
  rw [ksum_rho0, Matrix.nonneg_iff_posSemidef, Matrix.posSemidef_diagonal_iff]
  intro ij
  exact_mod_cast (add_pos (rates_pos ij.1) (rates_pos ij.2)).le

private lemma S_P : S *ᵥ P.vec = M.vec := by
  ext ⟨i,j⟩
  fin_cases i <;> fin_cases j <;> norm_num [S,P,M,rates,Matrix.mulVec_diagonal,Matrix.vec,flip]

private lemma M_ne_zero : M.vec ≠ 0 := by
  intro h
  have hh := congrFun h (0,0)
  norm_num [M,Matrix.vec] at hh

private lemma shift_H : (rho1-rho0) + ((1/4:ℝ):ℂ) • rho0 = H := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [rho1,rho0,H]

private lemma ksum_shift_H : ksum (rho1-rho0) + (1/4:ℂ) • ksum rho0 = ksum H := by
  have h := congrArg ksum shift_H
  rw [ksum_add, ksum_real_smul] at h
  norm_num at h ⊢
  exact h

private lemma S_inv_M : S⁻¹ *ᵥ M.vec = P.vec := by
  rw [← S_P, Matrix.mulVec_mulVec, S_inv_mul, Matrix.one_mulVec]

private lemma H_P_vec : ksum H *ᵥ P.vec = 0 := by
  rw [ksum_vec H P H_hermitian, HP, Matrix.vec_zero]

private lemma B_P : ksum (rho1-rho0) *ᵥ P.vec = (-1/4:ℂ) • ((ksum rho0) *ᵥ P.vec) := by
  have h := H_P_vec
  rw [← ksum_shift_H, Matrix.add_mulVec, Matrix.smul_mulVec] at h
  ext ij
  have hh := congrFun h ij
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] at hh ⊢
  linear_combination hh

private lemma K_M : D5.S3.Resource.LogDet.PathSpectralClassical.relativeCongruence (ksum (rho1-rho0)) (ksum rho0) *ᵥ M.vec = (-1/4:ℂ) • M.vec := by
  rw [D5.S3.Resource.LogDet.PathSpectralClassical.relativeCongruence, sqrt_rho0]
  simp only [← Matrix.mulVec_mulVec, S_inv_M, B_P, Matrix.mulVec_smul]
  rw [← S_sq, ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec _ S⁻¹ S, S_inv_mul,
    Matrix.one_mulVec, S_P]

private lemma K_simple (x : Fin 3 × Fin 3 → ℂ)
    (he : D5.S3.Resource.LogDet.PathSpectralClassical.relativeCongruence (ksum (rho1-rho0)) (ksum rho0) *ᵥ x = (-1/4:ℂ) • x) :
    ∃ c : ℂ, x = c • M.vec := by
  let v := S⁻¹ *ᵥ x
  have hSv : S *ᵥ v = x := by simp [v,Matrix.mulVec_mulVec,S_mul_inv]
  have hB : ksum (rho1-rho0) *ᵥ v = (-1/4:ℂ) • (S *ᵥ x) := by
    have hh := congrArg (fun z => S *ᵥ z) he
    simp only [D5.S3.Resource.LogDet.PathSpectralClassical.relativeCongruence, sqrt_rho0, ← Matrix.mulVec_mulVec, Matrix.mulVec_smul] at hh
    rw [Matrix.mulVec_mulVec _ S S⁻¹, S_mul_inv, Matrix.one_mulVec] at hh
    exact hh
  have hAv : ksum rho0 *ᵥ v = S *ᵥ x := by
    rw [← S_sq, ← Matrix.mulVec_mulVec, hSv]
  have hHv : ksum H *ᵥ v = 0 := by
    rw [← ksum_shift_H, Matrix.add_mulVec, Matrix.smul_mulVec, hB,hAv]
    ext ij
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    ring
  let X : Matrix (Fin 3) (Fin 3) ℂ := fun i j => v (j,i)
  have hvX : X.vec = v := rfl
  have hHX : H * X + X * H = 0 := by
    apply Matrix.vec_inj.mp
    rw [Matrix.vec_zero, ← ksum_vec H X H_hermitian, hvX, hHv]
  have hX := kernel_H X hHX
  refine ⟨X 0 0, ?_⟩
  have hv : v = X 0 0 • P.vec := by
    have hh := congrArg Matrix.vec hX
    simpa only [Matrix.vec_smul,hvX] using hh
  rw [← hSv, hv, Matrix.mulVec_smul,S_P]

private lemma physical_obstruction (U : Matrix (Fin 3) (Fin 3) ℂ)
    (hU : U ∈ unitaryGroup (Fin 3) ℂ) :
    ¬ (star (liftU U) * D5.S3.Resource.LogDet.PathSpectralClassical.relativeCongruence (ksum (rho1-rho0)) (ksum rho0) * liftU U).IsDiag := by
  intro hd
  have hW := liftU_unitary U hU
  obtain ⟨p,hp⟩ := diagonal_has_eigen_column _ (liftU U) (-1/4) M.vec M_ne_zero K_M
    (mem_unitaryGroup_iff.mp hW) hd
  obtain ⟨c,hc⟩ := K_simple _ hp
  have hc0 : c ≠ 0 := by
    intro hc0
    have := unitary_column_ne_zero (liftU U) (mem_unitaryGroup_iff'.mp hW) p
    exact this (by simpa [hc0] using hc)
  have h00 := congrFun hc (0,0)
  have h11 := congrFun hc (1,1)
  have h10 := congrFun hc (1,0)
  have h01 := congrFun hc (0,1)
  have hm := product_column_minor U p
  change liftU U (0,0) p * liftU U (1,1) p -
    liftU U (1,0) p * liftU U (0,1) p = 0 at hm
  change liftU U (0,0) p = c * M 0 0 at h00
  change liftU U (1,1) p = c * M 1 1 at h11
  change liftU U (1,0) p = c * M 0 1 at h10
  change liftU U (0,1) p = c * M 1 0 at h01
  rw [h00,h11,h10,h01] at hm
  have hz : c^2 * (M 0 0 * M 1 1 - M 0 1 * M 1 0) = 0 := by
    linear_combination hm
  exact M_minor ((mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ hc0))

theorem result : ¬ claim := by
  intro h
  obtain ⟨U,hU,hd⟩ := h 3 rho0 rho1 rho0_posDef rho1_posDef rho0_trace rho1_trace
    (by rw [delta_det]; norm_num) 1 (by norm_num) (by norm_num)
  apply physical_obstruction U hU
  have hD : star U * rho1 * U - star U * rho0 * U = star U * (rho1-rho0) * U := by
    simp [Matrix.mul_sub,Matrix.sub_mul]
  have heq : logArg (star U * rho0 * U) (star U * rho1 * U) 1 =
      1 + star (liftU U) * D5.S3.Resource.LogDet.PathSpectralClassical.relativeCongruence (ksum (rho1-rho0)) (ksum rho0) * liftU U := by
    simp only [logArg,Complex.ofReal_one,one_smul]
    change 1 + D5.S3.Resource.LogDet.PathSpectralClassical.relativeCongruence (ksum (star U * rho1 * U - star U * rho0 * U)) (ksum (star U * rho0 * U)) = _
    rw [hD, K_conj _ _ _ hU]
  rw [heq] at hd
  intro i j hij
  have hh := hd hij
  simpa [Matrix.add_apply,Matrix.one_apply,hij] using hh

end D5.S3.Quantum.Foundation.FuchsLogarithmBasisRefutation
