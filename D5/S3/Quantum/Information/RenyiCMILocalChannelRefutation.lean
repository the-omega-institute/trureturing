/- GID: D5/S3/Quantum/Information/RenyiCMILocalChannelRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/RenyiCMILocalChannelRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Information/RenyiCMILocalChannelRefutation.claim; result=D5/S3/Quantum/Information/RenyiCMILocalChannelRefutation.result; claim=D5/S3/Quantum/Information/RenyiCMILocalChannelRefutation.claim
   digest: A qubit dephasing channel refutes local Rényi CMI monotonicity. -/

/-
escape_witness: Three qubits, classical B, with AE blocks
M(13,8,7;13,39)/144 and M(7,8,13;39,13)/144. Complete dephasing of A,
K₀ = diagonal(1,0), K₁ = diagonal(0,1), increases equation (3.18) at α = 2
from 0 to log((217 + √21489)/360) > 0.
direct_frozen_dependencies:
  GID: D5/S3/Quantum/Information/PartialTraceMutualInformation
  statement_id: sha256:feb11c5d059c340c0873b6b17e3dcb2099d8bc5dde1a470924469d789d6788ba
proof_shape: mpow = definition; live_consumers: renyiCMI, mpow_two, negative_half, half_marginal, inside_rho, before_zero, negative_half_tau, inside_tau, after_positive
proof_shape: margAE = definition; live_consumers: renyiCMI, margAE_rho, margAE_tau, inside_rho, negative_half_tau, inside_tau
proof_shape: margE = definition; live_consumers: renyiCMI, margE_rho, margE_tau, inside_rho, inside_tau
proof_shape: traceA = definition; live_consumers: renyiCMI, middle_rho, inside_rho, inside_tau
proof_shape: extAE = definition; live_consumers: renyiCMI, extAE_block, extAE_posDef, extAE_mul, extAE_one, extAE_herm, extAE_psd, negative_half, middle_rho, inside_rho, negative_half_tau, inside_tau
proof_shape: extE = definition; live_consumers: renyiCMI, half_marginal, inside_rho, inside_tau
proof_shape: renyiCMI = definition; live_consumers: claim, before_zero, after_positive
proof_shape: applyA = definition; live_consumers: claim, applyA_eq_tau
proof_shape: claim = definition; live_consumers: result
proof_shape: diagHom = definition; live_consumers: cfc_diag
proof_shape: cfc_diag = bind-only; live_consumers: half_marginal, before_zero, negative_half_tau, inside_tau, after_positive
proof_shape: M = definition; live_consumers: X0, X1, M0_pos, M1_pos, X0_herm, X1_herm, rhoBD_pos, rho_trace, applyA_eq_tau, S, margAE_rho, margE_rho, S4, S4_pos, H4, J4, H4_pos, H_sq, HJ, middle_rho
proof_shape: X0 = definition; live_consumers: rhoBD, X0_pos, X0_herm, rhoBD_pos, rho_trace, applyA_eq_tau, margAE_rho, margE_rho, middle_rho
proof_shape: X1 = definition; live_consumers: rhoBD, X1_pos, X1_herm, rhoBD_pos, rho_trace, applyA_eq_tau, margAE_rho, margE_rho, middle_rho
proof_shape: M0_pos = bind-only; live_consumers: X0_pos
proof_shape: M1_pos = bind-only; live_consumers: X1_pos
proof_shape: idx = definition; live_consumers: rho, rho_pos, tau, rho_trace, applyA_eq_tau, S, margAE_rho, margE_rho, margAE_tau, margE_tau, idx_injective, H, Jm, H_sq, HJ, negative_half, middle_rho, inside_tau
proof_shape: rhoBD = definition; live_consumers: rho, rhoBD_pos, rho_trace, applyA_eq_tau, margAE_rho, margE_rho, middle_rho
proof_shape: rho = definition; live_consumers: rho_pos, rho_trace, applyA_eq_tau, margAE_rho, margE_rho, middle_rho, inside_rho, before_zero, result
proof_shape: X0_pos = bind-only; live_consumers: rhoBD_pos
proof_shape: X1_pos = bind-only; live_consumers: rhoBD_pos
proof_shape: X0_herm = bind-only; live_consumers: rhoBD_pos
proof_shape: X1_herm = bind-only; live_consumers: rhoBD_pos
proof_shape: rhoBD_pos = bind-only; live_consumers: rho_pos
proof_shape: rho_pos = bind-only; live_consumers: inside_rho, result
proof_shape: K = definition; live_consumers: K_complete, applyA_eq_tau, result
proof_shape: val0 = definition; live_consumers: tau, applyA_eq_tau, margAE_tau, margE_tau, inside_tau
proof_shape: val1 = definition; live_consumers: tau, applyA_eq_tau, margAE_tau, margE_tau, inside_tau
proof_shape: tau = definition; live_consumers: applyA_eq_tau, margAE_tau, margE_tau, negative_half_tau, inside_tau, after_positive
proof_shape: rho_trace = bind-only; live_consumers: result
proof_shape: K_complete = bind-only; live_consumers: result
proof_shape: applyA_eq_tau = bind-only; live_consumers: result
proof_shape: S = definition; live_consumers: margAE_rho, S_pos, H_sq, negative_half
proof_shape: margAE_rho = bind-only; live_consumers: inside_rho
proof_shape: margE_rho = bind-only; live_consumers: inside_rho
proof_shape: margAE_tau = bind-only; live_consumers: negative_half_tau
proof_shape: margE_tau = bind-only; live_consumers: inside_tau
proof_shape: mpow_two = bind-only; live_consumers: inside_rho
proof_shape: S4 = definition; live_consumers: S4_pos, H_sq
proof_shape: S4_pos = bind-only; live_consumers: S_pos
proof_shape: idx_injective = bind-only; live_consumers: S_pos
proof_shape: S_pos = bind-only; live_consumers: negative_half
proof_shape: H4 = definition; live_consumers: H, H4_pos, H_sq, HJ
proof_shape: J4 = definition; live_consumers: Jm, HJ, middle_rho
proof_shape: H = definition; live_consumers: H_sq, HJ, negative_half
proof_shape: Jm = definition; live_consumers: HJ, negative_half, middle_rho
proof_shape: sqrt13_sq = bind-only; live_consumers: sqrt13_sqC, HJ
proof_shape: sqrt13_sqC = bind-only; live_consumers: H_sq, middle_rho, inside_tau
proof_shape: H4_pos = bind-only; live_consumers: negative_half
proof_shape: H_sq = bind-only; live_consumers: negative_half
proof_shape: HJ = bind-only; live_consumers: negative_half
proof_shape: blockDiagonal_posDef = bind-only; live_consumers: extAE_posDef
proof_shape: extMap = definition; live_consumers: extAE_block, extMap_injective, extAE_posDef
proof_shape: extAE_block = bind-only; live_consumers: extAE_posDef
proof_shape: extMap_injective = bind-only; live_consumers: extAE_posDef
proof_shape: extAE_posDef = bind-only; live_consumers: negative_half
proof_shape: extAE_mul = bind-only; live_consumers: negative_half
proof_shape: extAE_one = bind-only; live_consumers: negative_half
proof_shape: extAE_herm = bind-only; live_consumers: extAE_psd
proof_shape: extAE_psd = bind-only; live_consumers: negative_half
proof_shape: negative_half = bind-only; live_consumers: inside_rho
proof_shape: half_marginal = bind-only; live_consumers: inside_rho, inside_tau
proof_shape: middle_rho = bind-only; live_consumers: inside_rho
proof_shape: inside_rho = bind-only; live_consumers: before_zero
proof_shape: before_zero = bind-only; live_consumers: result
proof_shape: negative_half_tau = bind-only; live_consumers: inside_tau
proof_shape: inside_tau = bind-only; live_consumers: after_positive
proof_shape: after_positive = bind-only; live_consumers: result
proof_shape: result = bind-only; live_consumers: external-open-problem-resolution
admission_basis: open-problem-resolution (#16068; Refuted).
The result is an external open-problem settlement; consumed bind-only helpers
organize its certificates and do not constitute independent mathematical novelty.
-/

import D5.S3.Quantum.Information.PartialTraceMutualInformation

open Matrix
open scoped Kronecker ComplexOrder MatrixOrder
open D5.S3.Quantum.Information.PartialTraceMutualInformation

namespace D5.S3.Quantum.Information.RenyiCMILocalChannelRefutation

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

variable {A B E : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype E] [DecidableEq E]

/-- Real matrix power through the continuous functional calculus. Since `0 ^ p = 0` for
`p ≠ 0`, negative powers are generalized inverses on the support, as in the source. -/
noncomputable def mpow {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) (p : ℝ) : Matrix n n ℂ :=
  cfc (fun t : ℝ => t ^ p) X

/-- The marginal on `A E`. -/
noncomputable def margAE (ρ : Matrix ((A × B) × E) ((A × B) × E) ℂ) : Matrix (A × E) (A × E) ℂ :=
  partialTraceLeft (ρ.submatrix (fun x : B × (A × E) => ((x.2.1, x.1), x.2.2))
    (fun x : B × (A × E) => ((x.2.1, x.1), x.2.2)))

/-- The marginal on `E`. -/
noncomputable def margE (ρ : Matrix ((A × B) × E) ((A × B) × E) ℂ) : Matrix E E ℂ :=
  partialTraceLeft ρ

/-- The partial trace over `A`. -/
noncomputable def traceA (X : Matrix ((A × B) × E) ((A × B) × E) ℂ) : Matrix (B × E) (B × E) ℂ :=
  partialTraceLeft (X.submatrix (fun x : A × (B × E) => ((x.1, x.2.1), x.2.2))
    (fun x : A × (B × E) => ((x.1, x.2.1), x.2.2)))

/-- The identity extension `S_{AE} ⊗ 1_B`. -/
def extAE (S : Matrix (A × E) (A × E) ℂ) : Matrix ((A × B) × E) ((A × B) × E) ℂ :=
  Matrix.of fun x y => if x.1.2 = y.1.2 then S (x.1.1, x.2) (y.1.1, y.2) else 0

/-- The identity extension `1_B ⊗ W_E`. -/
def extE (W : Matrix E E ℂ) : Matrix (B × E) (B × E) ℂ := (1 : Matrix B B ℂ) ⊗ₖ W

/-- The Rényi conditional mutual information, equation (3.18). -/
noncomputable def renyiCMI (α : ℝ) (ρ : Matrix ((A × B) × E) ((A × B) × E) ℂ) : ℝ :=
  α / (α - 1) * Real.log (Matrix.trace (mpow
    (mpow (extE (B := B) (margE ρ)) ((α - 1) / 2) *
      traceA (mpow (extAE (B := B) (margAE ρ)) ((1 - α) / 2) * mpow ρ α *
        mpow (extAE (B := B) (margAE ρ)) ((1 - α) / 2)) *
      mpow (extE (B := B) (margE ρ)) ((α - 1) / 2)) (1 / α))).re

/-- A quantum channel on `A` with Kraus operators `K`, tensored with the identity on `B E`. -/
def applyA {A' : Type*} [Fintype A'] [DecidableEq A'] {r : ℕ} (K : Fin r → Matrix A' A ℂ)
    (ρ : Matrix ((A × B) × E) ((A × B) × E) ℂ) : Matrix ((A' × B) × E) ((A' × B) × E) ℂ :=
  ∑ j, ((K j ⊗ₖ (1 : Matrix B B ℂ)) ⊗ₖ (1 : Matrix E E ℂ)) * ρ *
    ((K j ⊗ₖ (1 : Matrix B B ℂ)) ⊗ₖ (1 : Matrix E E ℂ))ᴴ

/-- Conjecture 1 of arXiv:1410.1443 for finite-dimensional systems and Kraus channels
(every CPTP map has a finite Kraus representation). -/
def claim : Prop :=
  ∀ (dA dA' dB dE r : ℕ)
    (ρ : Matrix ((Fin dA × Fin dB) × Fin dE) ((Fin dA × Fin dB) × Fin dE) ℂ)
    (K : Fin r → Matrix (Fin dA') (Fin dA) ℂ) (α : ℝ),
    ρ.PosSemidef → ρ.trace = 1 → ∑ j, (K j)ᴴ * K j = 1 →
    ((0 < α ∧ α < 1) ∨ (1 < α ∧ α ≤ 2)) →
    renyiCMI α (applyA K ρ) ≤ renyiCMI α ρ

private def diagHom (n : Type*) [Fintype n] [DecidableEq n] : (n → ℂ) →⋆ₐ[ℂ] Matrix n n ℂ where
  toAlgHom := diagonalAlgHom (n := n) (α := ℂ) ℂ
  map_star' a := by ext i j; simp [diagonal]; split_ifs <;> simp_all

private lemma cfc_diag {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n] (f : ℝ → ℝ) (d : n → ℝ) :
    cfc f (diagonal (fun i => (d i : ℂ))) = diagonal (fun i => (f (d i) : ℂ)) := by
  let : ContinuousFunctionalCalculus ℂ ℂ IsStarNormal := IsStarNormal.instContinuousFunctionalCalculus
  let : ContinuousFunctionalCalculus ℂ (n → ℂ) IsStarNormal := IsStarNormal.instContinuousFunctionalCalculus
  let : ContinuousFunctionalCalculus ℝ (n → ℂ) IsSelfAdjoint := IsSelfAdjoint.instContinuousFunctionalCalculus
  have hc : ContinuousOn f (spectrum ℝ (fun i => (d i : ℂ))) := by
    apply Set.Finite.continuousOn _ f
    rw [Pi.spectrum_eq]
    apply Set.finite_iUnion
    intro i
    change (spectrum ℝ (algebraMap ℝ ℂ (d i))).Finite
    rw [CFC.spectrum_algebraMap_eq]
    exact Set.finite_singleton _
  have hmap := (diagHom n).map_cfc (p := IsSelfAdjoint) (q := IsSelfAdjoint) f (fun i => (d i : ℂ)) hc (by
    change Continuous (fun d : n → ℂ => diagonal d)
    apply continuous_pi; intro i; apply continuous_pi; intro j
    by_cases h : i = j <;> simp [diagonal, h] <;> fun_prop) (by
      change star (fun i => (d i : ℂ)) = _
      ext i; simp) (by
      exact (isHermitian_diagonal_of_self_adjoint _ (by ext i; simp)).isSelfAdjoint)
  change cfc f ((diagHom n) (fun i => (d i : ℂ))) = _
  rw [← hmap, cfc_map_pi (S := ℂ) (p := IsSelfAdjoint) (q := fun _ => IsSelfAdjoint) f (fun i => (d i : ℂ)) (by simpa only [Pi.spectrum_eq] using hc)
    (by change star (fun i => (d i : ℂ)) = _; ext i; simp)
    (by intro i; change star (d i : ℂ) = _; simp)]
  change diagonal (fun i => cfc f (d i : ℂ)) = _
  congr 1
  funext i
  simpa using (cfc_algebraMap (A := ℂ) (d i) f)

private def M (p q s u v : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![(p : ℂ), 0, 0, q; 0, u, 0, 0; 0, 0, v, 0; q, 0, 0, s]

private noncomputable def X0 : Matrix (Fin 4) (Fin 4) ℂ := (1 / 144 : ℂ) • M 13 8 7 13 39
private noncomputable def X1 : Matrix (Fin 4) (Fin 4) ℂ := (1 / 144 : ℂ) • M 7 8 13 39 13

private lemma M0_pos : (M 13 8 7 13 39).PosSemidef := by
  let U : Matrix (Fin 4) (Fin 4) ℂ := !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 8/13, 0, 0, 1]
  let D : Matrix (Fin 4) (Fin 4) ℂ :=
    diagonal ![(13 : ℂ), 13, 39, 27/13]
  have hD : D.PosSemidef := by
    apply posSemidef_diagonal_iff.mpr
    intro i
    fin_cases i <;> norm_num [D] <;> positivity
  have hU : U * D * Uᴴ = M 13 8 7 13 39 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [U, D, M, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_four,
        Matrix.conjTranspose_apply, Complex.star_def] <;>
      norm_num [map_ofNat] <;> ring
  rw [← hU]
  exact hD.mul_mul_conjTranspose_same U

private lemma M1_pos : (M 7 8 13 39 13).PosSemidef := by
  let U : Matrix (Fin 4) (Fin 4) ℂ := !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 8/7, 0, 0, 1]
  let D : Matrix (Fin 4) (Fin 4) ℂ :=
    diagonal ![(7 : ℂ), 39, 13, 27/7]
  have hD : D.PosSemidef := by
    apply posSemidef_diagonal_iff.mpr
    intro i
    fin_cases i <;> norm_num [D] <;> positivity
  have hU : U * D * Uᴴ = M 7 8 13 39 13 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [U, D, M, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_four,
        Matrix.conjTranspose_apply, Complex.star_def] <;>
      norm_num [map_ofNat] <;> ring
  rw [← hU]
  exact hD.mul_mul_conjTranspose_same U

private def idx (a e : Fin 2) : Fin 4 := ⟨2 * a.val + e.val, by omega⟩

private noncomputable def rhoBD : Matrix (Fin 4 × Fin 2) (Fin 4 × Fin 2) ℂ :=
  Matrix.blockDiagonal (fun b => if b = 0 then X0 else X1)

private noncomputable def rho : Matrix ((Fin 2 × Fin 2) × Fin 2) ((Fin 2 × Fin 2) × Fin 2) ℂ :=
  rhoBD.submatrix (fun x => (idx x.1.1 x.2, x.1.2)) (fun x => (idx x.1.1 x.2, x.1.2))

private lemma X0_pos : X0.PosSemidef := by
  unfold X0
  exact M0_pos.smul (by norm_num; positivity)

private lemma X1_pos : X1.PosSemidef := by
  unfold X1
  exact M1_pos.smul (by norm_num; positivity)

private lemma X0_herm : X0ᴴ = X0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [X0, M, Matrix.conjTranspose_apply, Complex.star_def] <;> norm_num

private lemma X1_herm : X1ᴴ = X1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [X1, M, Matrix.conjTranspose_apply, Complex.star_def] <;> norm_num

private lemma rhoBD_pos : rhoBD.PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · change rhoBDᴴ = rhoBD
    ext i j
    by_cases h : i.2 = j.2
    · by_cases hb : j.2 = 0
      · simp [rhoBD, Matrix.blockDiagonal_apply, h, hb, X0_herm]
        simpa [Matrix.conjTranspose_apply] using congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M i.1 j.1) X0_herm
      · have hb1 : j.2 = 1 := Fin.eq_one_of_ne_zero j.2 hb
        simp [rhoBD, Matrix.blockDiagonal_apply, h, hb, hb1, X1_herm]
        simpa [Matrix.conjTranspose_apply] using congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M i.1 j.1) X1_herm
    · have hji : ¬j.2 = i.2 := fun h' => h h'.symm
      simp [rhoBD, Matrix.blockDiagonal_apply, h, hji]
  · intro x
    have hquad : star x ⬝ᵥ (rhoBD *ᵥ x) =
        ∑ b : Fin 2, star (fun i : Fin 4 => x (i, b)) ⬝ᵥ
          ((if b = 0 then X0 else X1) *ᵥ (fun i : Fin 4 => x (i, b))) := by
      simp [rhoBD, dotProduct, Matrix.mulVec, Matrix.blockDiagonal_apply,
        Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_add_distrib]
    rw [hquad]
    apply Finset.sum_nonneg
    intro b hb
    by_cases h : b = 0
    · subst b
      simpa using (X0_pos.dotProduct_mulVec_nonneg (fun i => x (i, 0)))
    · have hb1 : b = 1 := Fin.eq_one_of_ne_zero b h
      subst b
      simpa using (X1_pos.dotProduct_mulVec_nonneg (fun i => x (i, 1)))

private lemma rho_pos : rho.PosSemidef := by
  exact rhoBD_pos.submatrix
    (fun x : ((Fin 2 × Fin 2) × Fin 2) => (idx x.1.1 x.2, x.1.2))

private def K : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ := fun j =>
  if j = 0 then diagonal ![(1 : ℂ), 0] else diagonal ![(0 : ℂ), 1]

private noncomputable def val0 : Fin 4 → ℝ := ![13 / 144, 13 / 144, 39 / 144, 7 / 144]
private noncomputable def val1 : Fin 4 → ℝ := ![7 / 144, 39 / 144, 13 / 144, 13 / 144]

private noncomputable def tau : Matrix ((Fin 2 × Fin 2) × Fin 2) ((Fin 2 × Fin 2) × Fin 2) ℂ :=
  diagonal (fun x => ((if x.1.2 = 0 then val0 (idx x.1.1 x.2) else val1 (idx x.1.1 x.2) : ℝ) : ℂ))

private lemma rho_trace : rho.trace = 1 := by
  norm_num [rho, rhoBD, Matrix.trace, Matrix.diag_apply, Matrix.blockDiagonal_apply,
    X0, X1, M, idx, Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_four]

set_option maxHeartbeats 2000000 in
private lemma K_complete : ∑ j, (K j)ᴴ * K j = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [K, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
      diagonal, Complex.star_def] <;> norm_num

set_option maxHeartbeats 4000000 in
private lemma applyA_eq_tau : applyA K rho = tau := by
  ext x y
  fin_cases x <;> fin_cases y <;>
    simp [applyA, K, rho, rhoBD, Matrix.blockDiagonal_apply, idx, tau, val0, val1,
      X0, X1,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_four, M,
      diagonal, Complex.star_def] <;> norm_num

private noncomputable def S : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  ((1 / 36 : ℂ) • M 5 4 5 13 13).submatrix
    (fun x => idx x.1 x.2) (fun x => idx x.1 x.2)

private lemma margAE_rho : margAE rho = S := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [margAE, partialTraceLeft, rho, rhoBD, Matrix.blockDiagonal_apply, idx, S, X0, X1, M,
      Matrix.submatrix_apply, Fin.sum_univ_two, Fin.sum_univ_four,
      Fintype.sum_prod_type] <;> norm_num

private lemma margE_rho : margE rho = (1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [margE, partialTraceLeft, rho, rhoBD, Matrix.blockDiagonal_apply, idx, X0, X1, M,
      Matrix.submatrix_apply, Fin.sum_univ_two, Fin.sum_univ_four,
      Fintype.sum_prod_type] <;> norm_num

private lemma margAE_tau : margAE tau = diagonal (fun i : Fin 2 × Fin 2 =>
    (((if i = (0,0) ∨ i = (1,1) then 5 / 36 else 13 / 36) : ℝ) : ℂ)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [margAE, tau, val0, val1, idx, Matrix.submatrix_apply,
      partialTraceLeft, Fin.sum_univ_two] <;> norm_num

private lemma margE_tau : margE tau = (1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [margE, tau, val0, val1, idx, partialTraceLeft, Fin.sum_univ_two,
      Fin.sum_univ_four, Fintype.sum_prod_type] <;> norm_num

private lemma mpow_two {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) (hX : X.PosSemidef) : mpow X 2 = X * X := by
  unfold mpow
  rw [← CFC.rpow_eq_cfc_real hX.nonneg]
  simpa [pow_two] using (CFC.rpow_natCast X 2 hX.nonneg)

private noncomputable def S4 : Matrix (Fin 4) (Fin 4) ℂ := (1 / 36 : ℂ) • M 5 4 5 13 13

private lemma S4_pos : S4.PosDef := by
  let U : Matrix (Fin 4) (Fin 4) ℂ := !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 4/5, 0, 0, 1]
  let D : Matrix (Fin 4) (Fin 4) ℂ := diagonal ![(5 : ℂ), 13, 13, 9/5]
  have hD : D.PosDef := by
    apply Matrix.PosDef.diagonal
    intro i
    fin_cases i <;> norm_num [D]
  have hU : U * D * Uᴴ = M 5 4 5 13 13 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [U, D, M, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_four,
        Matrix.conjTranspose_apply, Complex.star_def] <;> norm_num [map_ofNat] <;> ring
  have hUinv : U * !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; -4/5, 0, 0, 1] = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [U, Matrix.mul_apply, Fin.sum_univ_four] <;> norm_num
  have hUinj : Function.Injective (fun v => v ᵥ* U) := by
    intro v w h
    have hh := congrArg (fun z => z ᵥ* !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; -4/5, 0, 0, 1]) h
    simpa [vecMul_vecMul, hUinv] using hh
  have hM : (M 5 4 5 13 13).PosDef := by
    rw [← hU]
    exact hD.mul_mul_conjTranspose_same hUinj
  exact hM.smul (by norm_num)

private lemma idx_injective : Function.Injective (fun x : Fin 2 × Fin 2 => idx x.1 x.2) := by
  intro x y h
  fin_cases x <;> fin_cases y <;> simp [idx] at h ⊢

private lemma S_pos : S.PosDef := by
  unfold S
  exact S4_pos.submatrix idx_injective

private noncomputable def H4 : Matrix (Fin 4) (Fin 4) ℂ :=
  (1 / 6 : ℂ) • M 2 1 2 (Real.sqrt 13) (Real.sqrt 13)

private noncomputable def J4 : Matrix (Fin 4) (Fin 4) ℂ :=
  M 4 (-2) 4 (6 / Real.sqrt 13) (6 / Real.sqrt 13)

private noncomputable def H : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  H4.submatrix (fun x => idx x.1 x.2) (fun x => idx x.1 x.2)
private noncomputable def Jm : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  J4.submatrix (fun x => idx x.1 x.2) (fun x => idx x.1 x.2)

private lemma sqrt13_sq : (Real.sqrt 13)^2 = 13 := by
  exact Real.sq_sqrt (by norm_num)

private lemma sqrt13_sqC : (Real.sqrt 13 : ℂ)^2 = 13 := by
  exact_mod_cast sqrt13_sq

private lemma H4_pos : H4.PosSemidef := by
  let U : Matrix (Fin 4) (Fin 4) ℂ := !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 1/2, 0, 0, 1]
  let D : Matrix (Fin 4) (Fin 4) ℂ :=
    diagonal ![(2 : ℂ), (Real.sqrt 13 : ℂ), Real.sqrt 13, 3/2]
  have hD : D.PosSemidef := by
    apply posSemidef_diagonal_iff.mpr
    intro i
    fin_cases i <;> norm_num [D] <;> positivity
  have hU : U * D * Uᴴ = M 2 1 2 (Real.sqrt 13) (Real.sqrt 13) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [U, D, M, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_four,
        Matrix.conjTranspose_apply, Complex.star_def] <;> norm_num [map_ofNat] <;> ring
  have hM : (M 2 1 2 (Real.sqrt 13) (Real.sqrt 13)).PosSemidef := by
    rw [← hU]
    exact hD.mul_mul_conjTranspose_same U
  exact hM.smul (by norm_num; positivity)

private lemma H_sq : H * H = S := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [H, S, H4, S4, M, Matrix.mul_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, idx, Complex.ofReal_pow] <;> norm_num <;>
      ring_nf <;> try rw [sqrt13_sqC] <;> norm_num

private lemma HJ : H * Jm = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [H, Jm, J4, H4, M, Matrix.mul_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, idx, sqrt13_sq] <;>
    field_simp [Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 13)] <;> ring

private lemma blockDiagonal_posDef {T : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ}
    (hT : T.PosDef) :
    (Matrix.blockDiagonal (fun _ : Fin 2 => T)).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · change (Matrix.blockDiagonal (fun _ : Fin 2 => T))ᴴ = _
    ext i j
    by_cases h : i.2 = j.2
    · simp [Matrix.blockDiagonal_apply, h]
      simpa [Matrix.conjTranspose_apply] using congrArg (fun M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ => M i.1 j.1) hT.isHermitian.eq
    · have h' : ¬j.2 = i.2 := fun h' => h h'.symm
      simp [Matrix.blockDiagonal_apply, h, h']
  · intro x hx
    have hquad : star x ⬝ᵥ (Matrix.blockDiagonal (fun _ : Fin 2 => T) *ᵥ x) =
        ∑ b : Fin 2, star (fun i : Fin 2 × Fin 2 => x (i, b)) ⬝ᵥ
          (T *ᵥ (fun i : Fin 2 × Fin 2 => x (i, b))) := by
      simp [dotProduct, Matrix.mulVec, Matrix.blockDiagonal_apply,
        Fintype.sum_prod_type, Finset.mul_sum] <;> ring
    rw [hquad]
    apply Finset.sum_pos'
    · intro b hb
      exact hT.posSemidef.dotProduct_mulVec_nonneg (x := fun i => x (i, b))
    · by_contra hn
      have hall : ∀ b : Fin 2, (fun i : Fin 2 × Fin 2 => x (i, b)) = 0 := by
        intro b
        by_contra hb
        have hp := hT.dotProduct_mulVec_pos hb
        exact hn ⟨b, by simp, hp⟩
      apply hx
      funext z
      have hz := congrFun (hall z.2) z.1
      simpa using hz

private def extMap (x : ((Fin 2 × Fin 2) × Fin 2)) : ((Fin 2 × Fin 2) × Fin 2) :=
  ((x.1.1, x.2), x.1.2)

private lemma extAE_block (T : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    extAE T = (Matrix.blockDiagonal (fun _ : Fin 2 => T)).submatrix extMap extMap := by
  ext i j
  simp [extAE, extMap, Matrix.blockDiagonal_apply]

private lemma extMap_injective : Function.Injective extMap := by
  intro x y h
  cases x with
  | mk xa e => cases xa with
    | mk a b =>
      cases y with
      | mk ya e' => cases ya with
        | mk a' b' => simpa [extMap, and_assoc, and_left_comm, and_comm] using h

private lemma extAE_posDef {T : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ}
    (hT : T.PosDef) :
      (extAE (A := Fin 2) (B := Fin 2) (E := Fin 2) T).PosDef := by
  have hs :
      ((Matrix.blockDiagonal (fun _ : Fin 2 => T)).submatrix extMap extMap).PosDef :=
    (blockDiagonal_posDef (T := T) hT).submatrix (e := extMap) extMap_injective
  rw [extAE_block T]
  exact hs

private lemma extAE_mul (T V : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    extAE (B := Fin 2) (T * V) = extAE (B := Fin 2) T * extAE (B := Fin 2) V := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [extAE, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]

private lemma extAE_one : extAE (B := Fin 2) (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [extAE]

private lemma extAE_herm {T : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ}
    (hT : T.IsHermitian) : (extAE (B := Fin 2) T).IsHermitian := by
  change (extAE (B := Fin 2) T)ᴴ = _
  ext i j
  by_cases h : i.1.2 = j.1.2
  · simp only [Matrix.conjTranspose_apply, extAE, Matrix.of_apply, if_pos h, if_pos h.symm]
    exact hT.apply _ _
  · simp only [Matrix.conjTranspose_apply, extAE, Matrix.of_apply, if_neg h, if_neg (Ne.symm h), star_zero]

private lemma extAE_psd {T : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ}
    (hT : T.PosSemidef) : (extAE (B := Fin 2) T).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (extAE_herm hT.isHermitian)
  intro x
  have he : star x ⬝ᵥ (extAE (B := Fin 2) T *ᵥ x) =
      ∑ b : Fin 2, star (fun i : Fin 2 × Fin 2 => x ((i.1,b),i.2)) ⬝ᵥ
        (T *ᵥ (fun i : Fin 2 × Fin 2 => x ((i.1,b),i.2))) := by
    simp [extAE, dotProduct, Matrix.mulVec, Fintype.sum_prod_type] <;> ring
  rw [he]
  exact Finset.sum_nonneg (fun b _ => hT.dotProduct_mulVec_nonneg _)

private lemma negative_half : mpow (extAE (B := Fin 2) S) (-1 / 2) = extAE (B := Fin 2) Jm := by
  have hS := extAE_posDef S_pos
  have hH := extAE_psd (H4_pos.submatrix (fun x : Fin 2 × Fin 2 => idx x.1 x.2))
  have hsq : extAE (B := Fin 2) H * extAE (B := Fin 2) H = extAE (B := Fin 2) S := by
    rw [← extAE_mul, H_sq]
  have hsqrt : mpow (extAE (B := Fin 2) S) (1 / 2) = extAE (B := Fin 2) H := by
    rw [mpow, ← CFC.rpow_eq_cfc_real hS.posSemidef.nonneg, ← CFC.sqrt_eq_rpow]
    exact CFC.sqrt_unique hsq hH.nonneg
  have hinv : mpow (extAE (B := Fin 2) S) (-1 / 2) * extAE (B := Fin 2) H = 1 := by
    rw [← hsqrt, mpow, mpow, ← CFC.rpow_eq_cfc_real hS.posSemidef.nonneg,
      ← CFC.rpow_eq_cfc_real hS.posSemidef.nonneg]
    convert CFC.rpow_neg_mul_rpow (1 / 2 : ℝ) hS.isStrictlyPositive using 1 <;> congr 2 <;> ring
  have hHJ : extAE (B := Fin 2) H * extAE (B := Fin 2) Jm = 1 := by
    rw [← extAE_mul, HJ, extAE_one]
  calc
    mpow (extAE (B := Fin 2) S) (-1 / 2) =
        mpow (extAE (B := Fin 2) S) (-1 / 2) * (extAE (B := Fin 2) H * extAE (B := Fin 2) Jm) := by rw [hHJ, Matrix.mul_one]
    _ = extAE (B := Fin 2) Jm := by rw [← Matrix.mul_assoc, hinv, Matrix.one_mul]

private lemma half_marginal :
    mpow (extE (B := Fin 2) ((1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))) (1 / 2) =
      diagonal (fun _ : Fin 2 × Fin 2 => (Real.sqrt (1 / 2) : ℂ)) := by
  have he : extE (B := Fin 2) ((1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) =
      diagonal (fun _ : Fin 2 × Fin 2 => ((1 / 2 : ℝ) : ℂ)) := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [extE, Matrix.kroneckerMap_apply]
  rw [he, mpow, cfc_diag]
  congr 1
  funext i
  rw [← Real.sqrt_eq_rpow]

private lemma middle_rho :
    traceA (extAE (B := Fin 2) Jm * (rho * rho) * extAE (B := Fin 2) Jm) =
      diagonal (fun x : Fin 2 × Fin 2 => (((if x.1 = x.2 then 9 / 32 else 1 / 32) : ℝ) : ℂ)) := by
  have hs : (Real.sqrt 13 : ℂ)^2 = 13 := sqrt13_sqC
  have hn : (Real.sqrt 13 : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 13)).ne'
  ext x y
  fin_cases x <;> fin_cases y <;>
    simp [traceA, partialTraceLeft, extAE, Jm, J4, rho, rhoBD, X0, X1, M, idx,
      Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.blockDiagonal_apply]
    <;> push_cast <;> field_simp [hn] <;> ring_nf <;> simp [hs] <;> ring

private lemma inside_rho :
    mpow (extE (B := Fin 2) (margE rho)) (1 / 2) *
      traceA (mpow (extAE (B := Fin 2) (margAE rho)) (-1 / 2) * mpow rho 2 *
        mpow (extAE (B := Fin 2) (margAE rho)) (-1 / 2)) *
      mpow (extE (B := Fin 2) (margE rho)) (1 / 2) =
      diagonal (fun x : Fin 2 × Fin 2 => (((if x.1 = x.2 then 9 / 64 else 1 / 64) : ℝ) : ℂ)) := by
  rw [margE_rho, half_marginal, margAE_rho, negative_half, mpow_two rho rho_pos,
    middle_rho, diagonal_mul_diagonal, diagonal_mul_diagonal]
  ext x y
  fin_cases x <;> fin_cases y <;>
    simp <;> push_cast <;> ring_nf <;>
    simp [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2)] <;> norm_num

private lemma before_zero : renyiCMI 2 rho = 0 := by
  unfold renyiCMI
  rw [show (2 - 1 : ℝ) / 2 = 1 / 2 by norm_num,
    show (1 - 2 : ℝ) / 2 = -1 / 2 by norm_num]
  rw [inside_rho, mpow, cfc_diag]
  have h9 : Real.sqrt (9 / 64) = 3 / 8 := by
    norm_num [Real.sqrt_div]
  have h1 : Real.sqrt (1 / 64) = 1 / 8 := by
    norm_num [Real.sqrt_div]
  simp only [← Real.sqrt_eq_rpow]
  simp [Matrix.trace, Fintype.sum_prod_type, Fin.sum_univ_two, h9, h1]
  norm_num [Real.sqrt_div]

private lemma negative_half_tau :
    mpow (extAE (B := Fin 2) (margAE tau)) (-1 / 2) = diagonal
      (fun x : (Fin 2 × Fin 2) × Fin 2 =>
        ((if x.1.1 = x.2 then 6 / Real.sqrt 5 else 6 / Real.sqrt 13 : ℝ) : ℂ)) := by
  rw [margAE_tau]
  have he : extAE (B := Fin 2) (diagonal (fun i : Fin 2 × Fin 2 =>
      (((if i = (0,0) ∨ i = (1,1) then 5 / 36 else 13 / 36) : ℝ) : ℂ))) =
      diagonal (fun x : (Fin 2 × Fin 2) × Fin 2 =>
        (((if x.1.1 = x.2 then 5 / 36 else 13 / 36) : ℝ) : ℂ)) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [extAE]
  rw [he, mpow, cfc_diag]
  congr 1
  funext x
  congr 1
  have h5 : Real.sqrt (5 / 36) = Real.sqrt 5 / 6 := by
    rw [Real.sqrt_div (by norm_num)]; norm_num
  have h13 : Real.sqrt (13 / 36) = Real.sqrt 13 / 6 := by
    rw [Real.sqrt_div (by norm_num)]; norm_num
  by_cases hx : x.1.1 = x.2 <;> simp only [hx, if_true, if_false]
  · rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_neg_eq_inv_rpow,
      ← Real.sqrt_eq_rpow, Real.sqrt_inv, h5]; simp [div_eq_mul_inv]
  · rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_neg_eq_inv_rpow,
      ← Real.sqrt_eq_rpow, Real.sqrt_inv, h13]; simp [div_eq_mul_inv]

private lemma inside_tau :
    mpow (extE (B := Fin 2) (margE tau)) (1 / 2) *
      traceA (mpow (extAE (B := Fin 2) (margAE tau)) (-1 / 2) * mpow tau 2 *
        mpow (extAE (B := Fin 2) (margAE tau)) (-1 / 2)) *
      mpow (extE (B := Fin 2) (margE tau)) (1 / 2) =
      diagonal (fun x : Fin 2 × Fin 2 => (((if x.1 = x.2 then 377 / 2880 else 57 / 2880) : ℝ) : ℂ)) := by
  rw [margE_tau, half_marginal, negative_half_tau]
  have ht : mpow tau 2 = diagonal (fun x : (Fin 2 × Fin 2) × Fin 2 =>
      ((if x.1.2 = 0 then val0 (idx x.1.1 x.2) else val1 (idx x.1.1 x.2))^2 : ℂ)) := by
    rw [tau, mpow, cfc_diag]
    simp only [Real.rpow_two, Complex.ofReal_pow]
  rw [ht, diagonal_mul_diagonal, diagonal_mul_diagonal]
  have hn5 : (Real.sqrt 5 : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 5)).ne'
  have hn13 : (Real.sqrt 13 : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 13)).ne'
  have hs5 : (Real.sqrt 5 : ℂ)^2 = 5 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have hs2 : (Real.sqrt 2 : ℂ)^2 = 2 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  ext x y
  fin_cases x <;> fin_cases y <;>
    simp [traceA, partialTraceLeft, Matrix.mul_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, val0, val1, idx] <;> push_cast <;>
    field_simp [hn5, hn13] <;> ring_nf <;> simp [hs5, sqrt13_sqC, hs2] <;> ring

private lemma after_positive : 0 < renyiCMI 2 tau := by
  unfold renyiCMI
  rw [show (2 - 1 : ℝ) / 2 = 1 / 2 by norm_num,
    show (1 - 2 : ℝ) / 2 = -1 / 2 by norm_num, inside_tau, mpow, cfc_diag]
  simp only [← Real.sqrt_eq_rpow]
  have he : (Matrix.trace (diagonal (fun x : Fin 2 × Fin 2 =>
      (Real.sqrt (if x.1 = x.2 then (377 / 2880 : ℝ) else 57 / 2880) : ℂ)))).re =
      2 * Real.sqrt (377 / 2880) + 2 * Real.sqrt (57 / 2880) := by
    simp [Matrix.trace, Fintype.sum_prod_type, Fin.sum_univ_two]
    ring
  rw [he]
  have h377 : (361 / 1000 : ℝ) < Real.sqrt (377 / 2880) := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 377/2880), Real.sqrt_nonneg (377/2880)]
  have h57 : (14 / 100 : ℝ) < Real.sqrt (57 / 2880) := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 57/2880), Real.sqrt_nonneg (57/2880)]
  have hp : 1 < 2 * Real.sqrt (377/2880) + 2 * Real.sqrt (57/2880) := by linarith
  have hl := Real.log_pos hp
  rw [show (2 : ℝ) / (2 - 1) = 2 by norm_num]
  exact mul_pos (by norm_num) hl

theorem result : ¬ claim := by
  intro h
  have hh := h 2 2 2 2 2 rho K 2 rho_pos rho_trace K_complete (by norm_num)
  rw [applyA_eq_tau, before_zero] at hh
  exact (not_le_of_gt after_positive) hh

end
end D5.S3.Quantum.Information.RenyiCMILocalChannelRefutation
