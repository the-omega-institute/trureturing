/- GID: D5/S3/Quantum/Matrix/SpectralGeometricLogEuclideanRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Matrix/SpectralGeometricLogEuclideanRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Matrix/SpectralGeometricLogEuclideanRefutation.claim; result=D5/S3/Quantum/Matrix/SpectralGeometricLogEuclideanRefutation.result; claim=D5/S3/Quantum/Matrix/SpectralGeometricLogEuclideanRefutation.claim
   digest: A positive definite matrix pair refutes spectral geometric log-majorization. -/

/-
escape_witness: At α=2 and p=1, A=diag(1,2^20) and
B=[[272,504],[504,1853]]/125 have SG(0,0)>2 and every LE eigenvalue ≤2.
Direct frozen dependencies: none (pinned Mathlib only).
proof_shape: mpow = definition; live_consumers: wgm, specMean, SG, mpow_one, mpow_two, Ai_powers, X_half
proof_shape: wgm = definition; live_consumers: specMean, geometric
proof_shape: specMean = definition; live_consumers: SG, SG_formula
proof_shape: SG = definition; live_consumers: claim, SG_formula, SG_herm, SG_entry, SG_large, result
proof_shape: LE = definition; live_consumers: claim, LE_herm, LE_le, result
proof_shape: LogMajorized = definition; live_consumers: claim, result
proof_shape: claim = definition; live_consumers: result
proof_shape: diagHom = definition; live_consumers: cfc_diag
proof_shape: cfc_diag = bind-only; live_consumers: Ai_powers, log_A, log_B
proof_shape: mpow_one = bind-only; live_consumers: SG_formula
proof_shape: mpow_two = bind-only; live_consumers: SG_formula
proof_shape: A = definition; live_consumers: A_pos, inverse_A, riccati, SG_formula, log_A, result
proof_shape: B = definition; live_consumers: B_diag, B_pos, X, H, SG_entry, log_B, result
proof_shape: U = definition; live_consumers: U_unitary, B_diag, log_B
proof_shape: Ai = definition; live_consumers: inverse_A, Ai_powers, H, L_pos
proof_shape: R = definition; live_consumers: Ai_powers, X, X_pos
proof_shape: Ri = definition; live_consumers: Ai_powers, geometric
proof_shape: H = definition; live_consumers: L, geometric, riccati, SG_formula, SG_entry
proof_shape: X = definition; live_consumers: K, X_pos, K_square, X_half, geometric
proof_shape: K = definition; live_consumers: K_pos, K_square, X_half, geometric
proof_shape: T = definition; live_consumers: L, sqrt_scalar, K_square, X_half, riccati, SG_formula, SG_entry
proof_shape: L = definition; live_consumers: geometric, L_pos, riccati, SG_formula, SG_herm
proof_shape: N = definition; live_consumers: logarithm, N_herm, N_le, LE_le
proof_shape: A_pos = bind-only; live_consumers: SG_formula, result
proof_shape: U_unitary = bind-only; live_consumers: B_pos, log_B
proof_shape: B_diag = bind-only; live_consumers: B_pos, log_B
proof_shape: B_pos = bind-only; live_consumers: X_pos, L_pos, SG_formula, SG_herm, log_B, result
proof_shape: inverse_A = bind-only; live_consumers: geometric
proof_shape: Ai_powers = bind-only; live_consumers: geometric
proof_shape: X_pos = bind-only; live_consumers: K_pos, X_half
proof_shape: K_pos = bind-only; live_consumers: X_half
proof_shape: sqrt_scalar = bind-only; live_consumers: X_half, riccati, SG_formula, SG_herm
proof_shape: K_square = bind-only; live_consumers: X_half
proof_shape: X_half = bind-only; live_consumers: geometric
proof_shape: geometric = bind-only; live_consumers: SG_formula
proof_shape: L_pos = bind-only; live_consumers: SG_formula, SG_herm
proof_shape: riccati = bind-only; live_consumers: SG_formula
proof_shape: SG_formula = bind-only; live_consumers: SG_herm, SG_entry
proof_shape: SG_herm = bind-only; live_consumers: SG_large, result
proof_shape: SG_entry = bind-only; live_consumers: SG_large
proof_shape: log_A = bind-only; live_consumers: logarithm
proof_shape: log_B = bind-only; live_consumers: logarithm
proof_shape: logarithm = bind-only; live_consumers: LE_le
proof_shape: N_herm = bind-only; live_consumers: LE_le
proof_shape: N_le = bind-only; live_consumers: LE_le
proof_shape: LE_herm = bind-only; live_consumers: result
proof_shape: LE_le = bind-only; live_consumers: result
proof_shape: SG_large = bind-only; live_consumers: result
proof_shape: result = bind-only; live_consumers: external-open-problem-resolution
admission_basis: open-problem-resolution (#16129; Refuted).
-/

import D5.S3.Quantum.Matrix.SpectralPower
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

set_option maxRecDepth 8192
set_option maxHeartbeats 800000

noncomputable section
open Matrix
open scoped ComplexOrder MatrixOrder
namespace D5.S3.Quantum.Matrix.SpectralGeometricLogEuclideanRefutation
open D5.S3.Quantum.Matrix.SpectralPower (mpow LE mpow_one mpow_two)

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The weighted geometric mean `A #_α B = A^{1/2} (A^{-1/2} B A^{-1/2})^α A^{1/2}`. -/
noncomputable def wgm (A B : Matrix n n ℂ) (α : ℝ) : Matrix n n ℂ :=
  mpow A (1 / 2) * mpow (mpow A (-1 / 2) * B * mpow A (-1 / 2)) α * mpow A (1 / 2)
/-- The weighted spectral geometric mean `Fα(A,B) = (A⁻¹ # B)^α A (A⁻¹ # B)^α`, equation (2.3). -/
noncomputable def specMean (A B : Matrix n n ℂ) (α : ℝ) : Matrix n n ℂ :=
  mpow (wgm A⁻¹ B (1 / 2)) α * A * mpow (wgm A⁻¹ B (1 / 2)) α
/-- `SGα,p(A,B) = Fα(A^p, B^p)^{1/p}`, equation (2.4). -/
noncomputable def SG (α p : ℝ) (A B : Matrix n n ℂ) : Matrix n n ℂ :=
  mpow (specMean (mpow A p) (mpow B p) α) (1 / p)
/-- Log-majorization `X ≺log Y` for positive definite `X, Y`: the product of any `k`
eigenvalues of `X` is at most the product of some `k` eigenvalues of `Y` (equivalently, the
products of the `k` largest eigenvalues are ordered), and the determinants agree. -/
def LogMajorized {m : ℕ} (X Y : Matrix (Fin m) (Fin m) ℂ) (hX : X.IsHermitian)
    (hY : Y.IsHermitian) : Prop :=
  (∀ s : Finset (Fin m), ∃ t : Finset (Fin m), t.card = s.card ∧
      ∏ i ∈ s, hX.eigenvalues i ≤ ∏ i ∈ t, hY.eigenvalues i) ∧ X.det = Y.det
/-- The open case of Problem 3.20: `SGα,p ≺log LEα` for every `α > 1`, `p > 0` and all positive
definite `A, B` (both means are Hermitian for such data). -/
def claim : Prop :=
  ∀ (α p : ℝ) (m : ℕ) (A B : Matrix (Fin m) (Fin m) ℂ), 1 < α → 0 < p → A.PosDef → B.PosDef →
    ∀ (hX : (SG α p A B).IsHermitian) (hY : (LE α A B).IsHermitian),
      LogMajorized (SG α p A B) (LE α A B) hX hY

private def diagHom (n : Type*) [Fintype n] [DecidableEq n] :
    (n → ℂ) →⋆ₐ[ℂ] Matrix n n ℂ where
  toAlgHom := diagonalAlgHom (n := n) (α := ℂ) ℂ
  map_star' a := by ext i j; simp [diagonal]; split_ifs <;> simp_all

private lemma cfc_diag [Nonempty n] (f : ℝ → ℝ) (d : n → ℝ) :
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
  have hmap := (diagHom n).map_cfc (p := IsSelfAdjoint) (q := IsSelfAdjoint) f
    (fun i => (d i : ℂ)) hc (by
      change Continuous (fun d : n → ℂ => diagonal d)
      apply continuous_pi; intro i; apply continuous_pi; intro j
      by_cases h : i = j <;> simp [diagonal, h] <;> fun_prop) (by
        change star (fun i => (d i : ℂ)) = _
        ext i; simp) (by
          exact (isHermitian_diagonal_of_self_adjoint _ (by ext i; simp)).isSelfAdjoint)
  change cfc f ((diagHom n) (fun i => (d i : ℂ))) = _
  rw [← hmap, cfc_map_pi (S := ℂ) (p := IsSelfAdjoint) (q := fun _ => IsSelfAdjoint) f
    (fun i => (d i : ℂ)) (by simpa only [Pi.spectrum_eq] using hc)
    (by change star (fun i => (d i : ℂ)) = _; ext i; simp)
    (by intro i; change star (d i : ℂ) = _; simp)]
  change diagonal (fun i => cfc f (d i : ℂ)) = _
  congr 1
  funext i
  simpa using (cfc_algebraMap (A := ℂ) (d i) f)


private def A : Matrix (Fin 2) (Fin 2) ℂ := diagonal ![1, 1048576]
private def B : Matrix (Fin 2) (Fin 2) ℂ := !![272/125, 504/125; 504/125, 1853/125]
private def U : Matrix (Fin 2) (Fin 2) ℂ := !![24/25, 7/25; -7/25, 24/25]
private def Ai : Matrix (Fin 2) (Fin 2) ℂ := diagonal ![1, 1/1048576]
private def R : Matrix (Fin 2) (Fin 2) ℂ := diagonal ![1, 1024]
private def Ri : Matrix (Fin 2) (Fin 2) ℂ := diagonal ![1, 1/1024]
private def H : Matrix (Fin 2) (Fin 2) ℂ := B + (4096 : ℂ) • Ai
private def X : Matrix (Fin 2) (Fin 2) ℂ := R * B * R
private def K : Matrix (Fin 2) (Fin 2) ℂ := X + (4096 : ℂ) • 1
private def T : ℝ := 77761424 / 5
private def L : Matrix (Fin 2) (Fin 2) ℂ := (Real.sqrt T)⁻¹ • H
private def N : Matrix (Fin 2) (Fin 2) ℂ := (1/625 : ℂ) • !![392,1344;1344,-7892]

private lemma A_pos : A.PosDef := by
  apply Matrix.PosDef.diagonal
  intro i; fin_cases i <;> norm_num [Complex.lt_def]

private lemma U_unitary : U ∈ unitary (Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [Unitary.mem_iff]
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [U, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_apply, Matrix.one_apply, map_ofNat]

private lemma B_diag : B = U * diagonal (![1,16] : Fin 2 → ℂ) * Uᴴ := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [B, U, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.conjTranspose_apply,
      Matrix.diagonal_apply, map_ofNat]

private lemma B_pos : B.PosDef := by
  rw [B_diag]
  apply Matrix.PosDef.mul_mul_conjTranspose_same
  · apply Matrix.PosDef.diagonal
    intro i; fin_cases i <;> norm_num [Complex.lt_def]
  · exact Matrix.vecMul_injective_iff_isUnit.mpr (Unitary.isUnit_coe (U := ⟨U, U_unitary⟩))

private lemma inverse_A : A⁻¹ = Ai := by
  apply Matrix.inv_eq_left_inv
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [A, Ai, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.diagonal_apply, Matrix.one_apply]


private lemma Ai_powers : mpow Ai (1/2) = Ri ∧ mpow Ai (-1/2) = R := by
  have hs : Real.sqrt (1048576 : ℝ) = 1024 := by
    rw [Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)]; norm_num
  have hai : Ai = diagonal (fun i => ((![1, 1/1048576] : Fin 2 → ℝ) i : ℂ)) := by
    ext i j; fin_cases i <;> fin_cases j <;> norm_num [Ai, Matrix.diagonal_apply]
  constructor
  · rw [mpow, hai, cfc_diag]
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [Ri, Matrix.diagonal_apply, ← Real.sqrt_eq_rpow, Real.sqrt_div, hs]
  · rw [mpow, hai, cfc_diag]
    have hp : (1/1048576 : ℝ) ^ (-1/2 : ℝ) = 1024 := by
      rw [show (-1/2 : ℝ) = -(1/2) by norm_num, Real.rpow_neg (by norm_num),
        ← Real.sqrt_eq_rpow]
      norm_num [Real.sqrt_div, hs]
    ext i j; fin_cases i <;> fin_cases j <;> norm_num [R, Matrix.diagonal_apply, hp]

private lemma X_pos : X.PosSemidef := by
  have hr : Rᴴ = R := by
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [R, Matrix.conjTranspose_apply, Matrix.diagonal_apply, map_ofNat]
  simpa only [hr, X] using B_pos.posSemidef.mul_mul_conjTranspose_same R

private lemma K_pos : K.PosSemidef :=
  X_pos.add (Matrix.PosSemidef.one.smul (by norm_num : (0 : ℂ) ≤ 4096))

private lemma sqrt_scalar : ((Real.sqrt T)⁻¹)^2 = T⁻¹ := by
  rw [inv_pow, Real.sq_sqrt (by norm_num [T])]

private lemma K_square : K * K = T • X := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [K, X, R, B, T, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_two, Matrix.diagonal_apply, Matrix.one_apply]

private lemma X_half : mpow X (1/2) = (Real.sqrt T)⁻¹ • K := by
  rw [mpow, ← CFC.rpow_eq_cfc_real X_pos.nonneg, ← CFC.sqrt_eq_rpow]
  apply CFC.sqrt_unique
  · simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
    rw [K_square, smul_smul, ← pow_two, sqrt_scalar]
    norm_num [T]
  · exact (K_pos.smul (inv_nonneg.mpr (Real.sqrt_nonneg T))).nonneg

private lemma geometric : wgm A⁻¹ B (1/2) = L := by
  rw [wgm, inverse_A, Ai_powers.1, Ai_powers.2]
  change Ri * mpow X (1/2) * Ri = L
  rw [X_half]
  simp only [mul_smul_comm, smul_mul_assoc, L]
  congr 1
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [Ri, K, X, R, H, Ai, B, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_two, Matrix.diagonal_apply, Matrix.one_apply]

private lemma L_pos : L.PosSemidef := by
  have hi : Ai.PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i; fin_cases i <;> norm_num [Complex.le_def]
  exact (B_pos.posSemidef.add (hi.smul (by norm_num : (0 : ℂ) ≤ 4096))).smul
    (inv_nonneg.mpr (Real.sqrt_nonneg T))

private lemma riccati : L * A * L = B := by
  have hh : H * A * H = T • B := by
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [H, A, Ai, B, T, Matrix.mul_apply, Matrix.vecMul, dotProduct,
        Fin.sum_univ_two, Matrix.diagonal_apply]
  simp only [L, smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [hh, smul_smul, ← pow_two, sqrt_scalar]
  norm_num [T]

private lemma SG_formula : SG 2 1 A B = T⁻¹ • (H * B * H) := by
  have he : specMean A B 2 = L * B * L := by
    rw [specMean, geometric, mpow_two L_pos.isHermitian]
    calc L * L * A * (L * L) = L * (L * A * L) * L := by simp only [mul_assoc]
         _ = L * B * L := by rw [riccati]
  have hp : (L * B * L).PosSemidef := by
    simpa only [L_pos.isHermitian.eq] using B_pos.posSemidef.mul_mul_conjTranspose_same L
  rw [SG, mpow_one A_pos.isHermitian, mpow_one B_pos.isHermitian]
  norm_num only [div_one]
  rw [he, mpow_one hp.isHermitian]
  simp only [L, smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [← pow_two, sqrt_scalar]

private lemma SG_herm : (SG 2 1 A B).IsHermitian := by
  have hp : (L * B * L).PosSemidef := by
    simpa only [L_pos.isHermitian.eq] using B_pos.posSemidef.mul_mul_conjTranspose_same L
  have he : SG 2 1 A B = L * B * L := by
    rw [SG_formula]
    simp only [L, smul_mul_assoc, mul_smul_comm, smul_smul]
    rw [← pow_two, sqrt_scalar]
  exact he ▸ hp.isHermitian

private lemma SG_entry : (SG 2 1 A B) 0 0 = (286558676 / 121502225 : ℂ) := by
  rw [SG_formula]
  norm_num [H, B, Ai, T, Matrix.mul_apply, Matrix.vecMul, dotProduct,
    Fin.sum_univ_two, Matrix.diagonal_apply]


private lemma log_A : cfc Real.log A = diagonal ![0, ((20 * Real.log 2 : ℝ) : ℂ)] := by
  have ha : A = diagonal (fun i => ((![1, (2:ℝ)^20] : Fin 2 → ℝ) i : ℂ)) := by
    ext i j; fin_cases i <;> fin_cases j <;> norm_num [A, Matrix.diagonal_apply]
  rw [ha, cfc_diag]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Real.log_pow]

private lemma log_B : cfc Real.log B =
    U * diagonal ![0, ((4 * Real.log 2 : ℝ) : ℂ)] * Uᴴ := by
  let D : Matrix (Fin 2) (Fin 2) ℂ :=
    diagonal (fun i => ((![1,16] : Fin 2 → ℝ) i : ℂ))
  let φ := Unitary.conjStarAlgAut ℂ (Matrix (Fin 2) (Fin 2) ℂ) ⟨U, U_unitary⟩
  have hd : D.IsHermitian := by
    apply isHermitian_diagonal_of_self_adjoint
    ext i; simp
  have he : φ D = B := by
    change U * D * Uᴴ = B
    rw [B_diag]
    congr 2
    ext i j; fin_cases i <;> fin_cases j <;> norm_num [D, Matrix.diagonal_apply]
  have hc : ContinuousOn Real.log (spectrum ℝ D) := by
    apply Set.Finite.continuousOn _ Real.log
    rw [hd.spectrum_real_eq_range_eigenvalues]
    exact Set.finite_range _
  have hm := StarAlgHomClass.map_cfc φ Real.log D hc (by
    change Continuous (fun Z : Matrix (Fin 2) (Fin 2) ℂ => U * Z * Uᴴ)
    fun_prop) hd.isSelfAdjoint (he.symm ▸ B_pos.isHermitian.isSelfAdjoint)
  rw [he] at hm
  rw [← hm]
  change U * cfc Real.log D * Uᴴ = _
  dsimp only [D]
  rw [cfc_diag]
  have hl : Real.log 16 = 4 * Real.log 2 := by
    simpa only [Nat.cast_ofNat, show (2 : ℝ)^4 = 16 by norm_num] using Real.log_pow (2 : ℝ) 4
  congr 2
  ext i j; fin_cases i <;> fin_cases j <;> simp [hl]

private lemma logarithm :
    (1 - (2:ℝ)) • cfc Real.log A + (2:ℝ) • cfc Real.log B = Real.log 2 • N := by
  rw [log_A, log_B]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [N, U, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
      Matrix.diagonal_apply, Matrix.conjTranspose_apply, map_ofNat,
      Complex.real_smul, Complex.ofReal_mul] <;> ring

private lemma N_herm : N.IsHermitian := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [N, Matrix.conjTranspose_apply, map_ofNat]

private lemma N_le : N ≤ 1 := by
  let V : Matrix (Fin 2) (Fin 2) ℂ := !![1,0;-1344/233,1]
  have hd : (diagonal (![233/625,285/233] : Fin 2 → ℂ)).PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i; fin_cases i <;> norm_num [Complex.le_def]
  change (1 - N).PosSemidef
  convert hd.mul_mul_conjTranspose_same V using 1
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [N, V, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
      Matrix.diagonal_apply, Matrix.conjTranspose_apply, Matrix.one_apply, map_ofNat]

private lemma LE_herm : (LE 2 A B).IsHermitian := IsSelfAdjoint.cfc

private lemma LE_le : LE 2 A B ≤ (2:ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have hg : IsSelfAdjoint (Real.log 2 • N) :=
    N_herm.smul (IsSelfAdjoint.all (Real.log 2))
  have hg_le : Real.log 2 • N ≤ Real.log 2 • (1 : Matrix (Fin 2) (Fin 2) ℂ) :=
    smul_le_smul_of_nonneg_left N_le (Real.log_nonneg (by norm_num))
  have hspec : ∀ x ∈ spectrum ℝ (Real.log 2 • N), x ≤ Real.log 2 := by
    apply (le_algebraMap_iff_spectrum_le hg).mp
    simpa [Algebra.algebraMap_eq_smul_one] using hg_le
  rw [D5.S3.Quantum.Matrix.SpectralPower.LE, logarithm]
  have hb := cfc_le_algebraMap Real.exp 2 (Real.log 2 • N) (fun x hx => by
    calc Real.exp x ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr (hspec x hx)
         _ = 2 := Real.exp_log (by norm_num)) (ha := hg)
  simpa [Algebra.algebraMap_eq_smul_one] using hb

private lemma SG_large : ∃ i, 2 < SG_herm.eigenvalues i := by
  by_contra! h
  have hs : SG 2 1 A B ≤ (2:ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    have hh := (le_algebraMap_iff_spectrum_le SG_herm.isSelfAdjoint).mpr
      (fun x hx => by
        obtain ⟨i, rfl⟩ := SG_herm.spectrum_real_eq_range_eigenvalues ▸ hx
        exact h i)
    simpa [Algebra.algebraMap_eq_smul_one] using hh
  have hh := (Matrix.le_iff.mp hs).diag_nonneg (i := (0 : Fin 2))
  rw [Matrix.sub_apply, SG_entry] at hh
  norm_num [Matrix.one_apply, Complex.le_def, Complex.real_smul] at hh

/-- The positive definite pair at α=2, p=1 violates the singleton eigenvalue comparison. -/
theorem result : ¬ claim := by
  intro hc
  have hm := (hc 2 1 2 A B (by norm_num) (by norm_num) A_pos B_pos SG_herm LE_herm).1
  obtain ⟨i, hi⟩ := SG_large
  obtain ⟨t, ht, hprod⟩ := hm {i}
  have ht1 : t.card = 1 := by simpa using ht
  obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp ht1
  simp only [Finset.prod_singleton] at hprod
  have hj : LE_herm.eigenvalues j ≤ 2 := by
    apply (le_algebraMap_iff_spectrum_le LE_herm.isSelfAdjoint).mp
      (by simpa [Algebra.algebraMap_eq_smul_one] using LE_le)
    exact LE_herm.eigenvalues_mem_spectrum_real j
  exact (not_lt_of_ge (hprod.trans hj)) hi

end D5.S3.Quantum.Matrix.SpectralGeometricLogEuclideanRefutation
