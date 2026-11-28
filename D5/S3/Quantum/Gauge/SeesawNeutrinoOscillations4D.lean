/- GID: D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D
   generality: G
   mirror-B: D5/B/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact seesaw masses, unitary vacuum oscillations, and the three-flavor CP difference. -/

import OmegaBuild.Commands
import D5.S3.Quantum.Gauge.CKMFlavorJarlskog4D
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Positivity

/-! The real symmetric seesaw matrix has a nonpositive light eigenvalue and a
nonnegative heavy eigenvalue. Oscillation indices list the initial flavor first. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix Complex Filter
open scoped BigOperators ComplexConjugate Matrix Topology

namespace D5.S3.Quantum.Gauge.SeesawNeutrinoOscillations4D

def seesawMatrix (mD M : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![0, mD; mD, M]

def seesawHeavy (mD M : ℝ) : ℝ := (M + Real.sqrt (M ^ 2 + 4 * mD ^ 2)) / 2

def seesawLight (mD M : ℝ) : ℝ := (Real.sqrt (M ^ 2 + 4 * mD ^ 2) - M) / 2

theorem seesaw_det_trace (mD M : ℝ) :
    (seesawMatrix mD M).det = -mD ^ 2 ∧ (seesawMatrix mD M).trace = M := by
  constructor
  · simp [seesawMatrix, Matrix.det_fin_two_of, pow_two]
  · simp [seesawMatrix, Matrix.trace_fin_two_of]

theorem seesaw_mass_product_and_diff (mD M : ℝ) :
    seesawLight mD M * seesawHeavy mD M = mD ^ 2 ∧
      seesawHeavy mD M - seesawLight mD M = M := by
  have h := Real.sq_sqrt (show 0 ≤ M ^ 2 + 4 * mD ^ 2 by positivity)
  unfold seesawLight seesawHeavy
  constructor
  · nlinarith only [h]
  · ring

/-- Columns are oriented light and heavy eigenvectors. When the off-diagonal
entry vanishes, the coordinate axes are ordered by the signed eigenvalues. -/
def seesawRotation (mD M : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  if mD = 0 then
    if M < 0 then !![0, 1; -1, 0] else 1
  else
    let h := seesawHeavy mD M
    (Real.sqrt (h ^ 2 + mD ^ 2))⁻¹ • !![h, mD; -mD, h]

theorem seesaw_orthogonal_diagonalization (mD M : ℝ) :
    let O := seesawRotation mD M
    Oᵀ * O = 1 ∧ O.det = 1 ∧
      Oᵀ * seesawMatrix mD M * O = !![-seesawLight mD M, 0; 0, seesawHeavy mD M] := by
  dsimp only
  classical
  by_cases hd : mD = 0
  · subst mD
    by_cases hM : M < 0
    · have hL : seesawLight 0 M = -M := by
        simp [seesawLight, Real.sqrt_sq_eq_abs, abs_of_neg hM]
        ring
      have hH : seesawHeavy 0 M = 0 := by
        simp [seesawHeavy, Real.sqrt_sq_eq_abs, abs_of_neg hM]
      simp only [seesawRotation, ite_eq_left hM, hL, hH, neg_neg]
      refine ⟨?_, by norm_num [Matrix.det_fin_two_of], ?_⟩ <;>
        ext i j <;> fin_cases i <;> fin_cases j <;>
        norm_num [seesawMatrix, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]
    · have hL : seesawLight 0 M = 0 := by
        simp [seesawLight, Real.sqrt_sq_eq_abs, abs_of_nonneg (le_of_not_gt hM)]
      have hH : seesawHeavy 0 M = M := by
        simp [seesawHeavy, Real.sqrt_sq_eq_abs, abs_of_nonneg (le_of_not_gt hM)]
      simp [seesawRotation, hM, hL, hH, seesawMatrix]
  · let H := seesawHeavy mD M
    let L := seesawLight mD M
    let s := Real.sqrt (H ^ 2 + mD ^ 2)
    let B : Matrix (Fin 2) (Fin 2) ℝ := !![H, mD; -mD, H]
    let D : Matrix (Fin 2) (Fin 2) ℝ := !![-L, 0; 0, H]
    have hsq : s ^ 2 = H ^ 2 + mD ^ 2 := Real.sq_sqrt (by positivity)
    have hs : s ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
    obtain ⟨hprod, hdiff⟩ := seesaw_mass_product_and_diff mD M
    change L * H = _ at hprod
    change H - L = _ at hdiff
    rw [seesawRotation, ite_eq_right hd]
    change (s⁻¹ • B)ᵀ * (s⁻¹ • B) = 1 ∧ (s⁻¹ • B).det = 1 ∧
      (s⁻¹ • B)ᵀ * seesawMatrix mD M * (s⁻¹ • B) = D
    have hO : (s⁻¹ • B)ᵀ * (s⁻¹ • B) = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [B, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;>
        field_simp [hs] <;> linarith only [hsq]
    have hdet : (s⁻¹ • B).det = 1 := by
      rw [Matrix.det_fin_two]
      simp [B]
      field_simp [hs]
      linarith only [hsq]
    have heigen : seesawMatrix mD M * B = B * D := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [B, D, seesawMatrix, Matrix.mul_apply, Fin.sum_univ_two] <;>
        nlinarith only [hprod, hdiff, congrArg (fun y : ℝ => y * H) hdiff,
          congrArg (fun y : ℝ => y * mD) hdiff]
    refine ⟨hO, hdet, ?_⟩
    rw [mul_assoc, Matrix.mul_smul, heigen, ← Matrix.smul_mul, ← mul_assoc, hO, one_mul]

theorem seesaw_exact_correction (mD M : ℝ) (hM : M ≠ 0) :
    mD ^ 2 / M - seesawLight mD M = seesawLight mD M ^ 2 / M := by
  obtain ⟨hprod, hdiff⟩ := seesaw_mass_product_and_diff mD M
  field_simp [hM]
  linear_combination -hprod + seesawLight mD M * hdiff

private theorem seesaw_light_nonnegative (mD M : ℝ) : 0 ≤ seesawLight mD M := by
  have h : Real.sqrt (M ^ 2) ≤ Real.sqrt (M ^ 2 + 4 * mD ^ 2) :=
    Real.sqrt_le_sqrt (by nlinarith only [sq_nonneg mD])
  rw [Real.sqrt_sq_eq_abs] at h
  unfold seesawLight
  linarith only [h, le_abs_self M]

theorem seesaw_strict_hierarchy_bounds (mD M : ℝ) (hd : mD ≠ 0) (hM : 0 < M) :
    0 < seesawLight mD M ∧ seesawLight mD M < mD ^ 2 / M ∧
      M < seesawHeavy mD M ∧ 0 < mD ^ 2 / M - seesawLight mD M ∧
      mD ^ 2 / M - seesawLight mD M < mD ^ 4 / M ^ 3 := by
  obtain ⟨hprod, hdiff⟩ := seesaw_mass_product_and_diff mD M
  have hL : 0 < seesawLight mD M :=
    lt_of_le_of_ne (seesaw_light_nonnegative mD M) fun heq => by
      rw [← heq, zero_mul] at hprod
      have hsq : mD ^ 2 = 0 := hprod.symm
      exact (pow_ne_zero 2 hd) hsq
  have hcorr := seesaw_exact_correction mD M hM.ne'
  have hgap : 0 < mD ^ 2 / M - seesawLight mD M := by rw [hcorr]; positivity
  have hsmall : seesawLight mD M < mD ^ 2 / M := by linarith only [hgap]
  refine ⟨hL, hsmall, by linarith only [hL, hdiff], hgap, ?_⟩
  rw [hcorr]
  calc
    _ < (mD ^ 2 / M) ^ 2 / M :=
      div_lt_div_of_pos_right (pow_lt_pow_left₀ hsmall hL.le (by decide)) hM
    _ = _ := by ring

theorem seesaw_asymptotic_limits (mD : ℝ) :
    Tendsto (seesawLight mD) atTop (𝓝 0) ∧
      Tendsto (fun M => M * seesawLight mD M) atTop (𝓝 (mD ^ 2)) ∧
      Tendsto (fun M => seesawHeavy mD M / M) atTop (𝓝 1) := by
  have hp : ∀ᶠ M : ℝ in atTop, 0 < M := eventually_gt_atTop 0
  have hL : Tendsto (seesawLight mD) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      ((tendsto_id : Tendsto (fun M : ℝ => M) atTop atTop).const_div_atTop (mD ^ 2))
    · exact Eventually.of_forall (seesaw_light_nonnegative mD)
    · filter_upwards [hp] with M hM
      change seesawLight mD M ≤ mD ^ 2 / M
      have h := seesaw_exact_correction mD M hM.ne'
      linarith only [h, show 0 ≤ seesawLight mD M ^ 2 / M by positivity]
  refine ⟨hL, ?_, ?_⟩
  · have h := (tendsto_const_nhds (x := mD ^ 2) (f := atTop)).sub (hL.pow 2)
    simp only [zero_pow (by decide : (2 : ℕ) ≠ 0), sub_zero] at h
    apply h.congr'
    filter_upwards with M
    obtain ⟨hprod, hdiff⟩ := seesaw_mass_product_and_diff mD M
    linear_combination -hprod + seesawLight mD M * hdiff
  · have h := (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop)).add
      (hL.div_atTop (tendsto_id : Tendsto (fun M : ℝ => M) atTop atTop))
    simp only [add_zero] at h
    apply h.congr'
    filter_upwards [hp] with M hM
    change 1 + seesawLight mD M / M = seesawHeavy mD M / M
    have hdiff := (seesaw_mass_product_and_diff mD M).2
    field_simp [hM.ne']
    linarith only [hdiff]

section Block

variable {n : Type*} [Fintype n] [DecidableEq n]

def blockSeesaw (M_D M_R : Matrix n n ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ :=
  Matrix.fromBlocks 0 M_D M_Dᵀ M_R

theorem block_seesaw_schur_congruence (M_D M_R : Matrix n n ℝ)
    (hR : IsUnit M_R.det) (hSym : M_Rᵀ = M_R) :
    let L := Matrix.fromBlocks 1 (-M_D * M_R⁻¹) 0 1
    L * blockSeesaw M_D M_R * Lᵀ =
      Matrix.fromBlocks (-M_D * M_R⁻¹ * M_Dᵀ) 0 0 M_R := by
  have hleft : M_D * M_R⁻¹ * M_R = M_D := Matrix.nonsing_inv_mul_cancel_right M_R _ hR
  have hinv : M_R⁻¹ᵀ = M_R⁻¹ := by rw [Matrix.transpose_nonsing_inv, hSym]
  have hright : M_R * (M_R⁻¹ * M_Dᵀ) = M_Dᵀ :=
    Matrix.mul_nonsing_inv_cancel_left M_R _ hR
  simp [blockSeesaw, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
    Matrix.transpose_mul, hinv, hleft, hright]

theorem block_seesaw_det (M_D M_R : Matrix n n ℝ) (hR : IsUnit M_R.det) :
    (blockSeesaw M_D M_R).det = (-1 : ℝ) ^ Fintype.card n * M_D.det ^ 2 := by
  let : Invertible M_R := Matrix.invertibleOfIsUnitDet _ hR
  simp only [blockSeesaw, Matrix.det_fromBlocks₂₂, zero_sub, Matrix.det_neg,
    Matrix.det_mul, Matrix.det_transpose, Matrix.invOf_eq_nonsing_inv]
  calc
    _ = (M_R⁻¹.det * M_R.det) * ((-1 : ℝ) ^ Fintype.card n * M_D.det ^ 2) := by ring
    _ = _ := by rw [Matrix.det_nonsing_inv_mul_det _ hR, one_mul]

end Block

open D5.S3.Quantum.Gauge.CKMFlavorJarlskog4D
  (jarlskogQuartet jarlskogQuartet_unitary_universal leviSign)

private def oscPhase (s : ℝ) : ℂ := Complex.exp ((-s : ℝ) * Complex.I)

private theorem oscPhase_add (s t : ℝ) :
    oscPhase (s + t) = oscPhase s * oscPhase t := by
  unfold oscPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem oscPhase_norm (s : ℝ) : ‖oscPhase s‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I (-s)

private theorem oscPhase_conj (s : ℝ) : conj (oscPhase s) = oscPhase (-s) := by
  simp [oscPhase, ← Complex.exp_conj]

private theorem oscPhase_zero : oscPhase 0 = 1 := by simp [oscPhase]

/-- The transition amplitude from flavor `α` to flavor `β` with phase parameter `x`. -/
def oscAmp {N : ℕ} (U : Matrix (Fin N) (Fin N) ℂ) (mSq : Fin N → ℝ)
    (x : ℝ) (α β : Fin N) : ℂ :=
  ∑ k : Fin N, U β k * oscPhase (mSq k * x) * star (U α k)

def oscProb {N : ℕ} (U : Matrix (Fin N) (Fin N) ℂ) (mSq : Fin N → ℝ)
    (x : ℝ) (α β : Fin N) : ℝ :=
  ‖oscAmp U mSq x α β‖ ^ 2

theorem oscProb_nonneg {N : ℕ} (U : Matrix (Fin N) (Fin N) ℂ) (mSq : Fin N → ℝ)
    (x : ℝ) (α β : Fin N) : 0 ≤ oscProb U mSq x α β :=
  sq_nonneg _

private def oscEvolution {N : ℕ} (U : Matrix (Fin N) (Fin N) ℂ)
    (mSq : Fin N → ℝ) (x : ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  U * Matrix.diagonal (fun k => oscPhase (mSq k * x)) * Uᴴ

private theorem oscEvolution_apply {N : ℕ} (U : Matrix (Fin N) (Fin N) ℂ)
    (mSq : Fin N → ℝ) (x : ℝ) (α β : Fin N) :
    oscEvolution U mSq x β α = oscAmp U mSq x α β := by
  rw [oscEvolution, Matrix.mul_apply]
  simp only [oscAmp, Matrix.mul_diagonal, Matrix.conjTranspose_apply]

theorem oscProb_zero_baseline {N : ℕ} (U : Matrix (Fin N) (Fin N) ℂ)
    (mSq : Fin N → ℝ) (α β : Fin N) (hU : U * Uᴴ = 1) :
    oscProb U mSq 0 α β = if α = β then 1 else 0 := by
  rw [oscProb, ← oscEvolution_apply]
  simp only [oscEvolution, mul_zero, oscPhase_zero, Matrix.diagonal_one, mul_one, hU]
  by_cases h : α = β
  · subst β
    simp
  · simp [h, Ne.symm h]

private theorem oscEvolution_unitary {N : ℕ} (U : Matrix (Fin N) (Fin N) ℂ)
    (mSq : Fin N → ℝ) (x : ℝ) (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1) :
    (oscEvolution U mSq x)ᴴ * oscEvolution U mSq x = 1 := by
  let D := Matrix.diagonal (fun k => oscPhase (mSq k * x))
  have hD : Dᴴ * D = 1 := by
    dsimp [D]
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    change Matrix.diagonal (fun k => star (oscPhase (mSq k * x)) * oscPhase (mSq k * x)) = 1
    simp [oscPhase_conj, ← oscPhase_add, oscPhase_zero]
  change (U * D * Uᴴ)ᴴ * (U * D * Uᴴ) = 1
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  calc
    U * (Dᴴ * (Uᴴ * (U * (D * Uᴴ)))) = U * (Dᴴ * (D * Uᴴ)) := by
      rw [← Matrix.mul_assoc Uᴴ U, hU, one_mul]
    _ = 1 := by rw [← Matrix.mul_assoc Dᴴ D, hD, one_mul, hU']

theorem oscProb_unitarity_sum {N : ℕ} (U : Matrix (Fin N) (Fin N) ℂ)
    (mSq : Fin N → ℝ) (x : ℝ) (α β : Fin N) (hU : Uᴴ * U = 1 ∧ U * Uᴴ = 1) :
    (∑ β, oscProb U mSq x α β) = 1 ∧
      (∑ α, oscProb U mSq x α β) = 1 ∧ oscProb U mSq x α β ≤ 1 := by
  let V := oscEvolution U mSq x
  have hV : Vᴴ * V = 1 := oscEvolution_unitary U mSq x hU.1 hU.2
  have hV' : V * Vᴴ = 1 := mul_eq_one_comm.mp hV
  have col : (∑ b, oscProb U mSq x α b) = 1 := by
    apply Complex.ofReal_injective
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq,
      star_def, mul_comm, Complex.mul_conj', ← oscEvolution_apply, oscProb,
      Complex.ofReal_sum, Complex.ofReal_one, Complex.ofReal_pow] using
      congrArg (fun A : Matrix (Fin N) (Fin N) ℂ => A α α) hV
  have row : (∑ a, oscProb U mSq x a β) = 1 := by
    apply Complex.ofReal_injective
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq,
      star_def, Complex.mul_conj', ← oscEvolution_apply, oscProb,
      Complex.ofReal_sum, Complex.ofReal_one, Complex.ofReal_pow] using
      congrArg (fun A : Matrix (Fin N) (Fin N) ℂ => A β β) hV'
  refine ⟨col, row, ?_⟩
  rw [← col]
  exact Finset.single_le_sum (fun b _ => oscProb_nonneg U mSq x α b) (Finset.mem_univ β)

theorem oscProb_common_shift_invariant {N : ℕ} (U : Matrix (Fin N) (Fin N) ℂ)
    (mSq : Fin N → ℝ) (x c : ℝ) (α β : Fin N) :
    oscProb U (fun k => mSq k + c) x α β = oscProb U mSq x α β := by
  have h : oscAmp U (fun k => mSq k + c) x α β =
      oscAmp U mSq x α β * oscPhase (c * x) := by
    simp only [oscAmp, Finset.sum_mul, add_mul, oscPhase_add]
    apply Finset.sum_congr rfl
    intro k _
    ring
  simp [oscProb, h, oscPhase_norm]

def antiMatrix {N : ℕ} (U : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  U.map star

theorem oscProb_cpt_symmetry {N : ℕ} (U : Matrix (Fin N) (Fin N) ℂ)
    (mSq : Fin N → ℝ) (x : ℝ) (α β : Fin N) :
    oscProb (antiMatrix U) mSq x α β = oscProb U mSq x β α := by
  unfold oscProb
  congr 2
  simp only [oscAmp, antiMatrix, Matrix.map_apply, star_star]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem oscProb_survival_cp_zero {N : ℕ} (U : Matrix (Fin N) (Fin N) ℂ)
    (mSq : Fin N → ℝ) (x : ℝ) (α : Fin N) :
    oscProb (antiMatrix U) mSq x α α = oscProb U mSq x α α :=
  oscProb_cpt_symmetry U mSq x α α

/-- The real mixing rotation embedded entrywise in the complex amplitudes. -/
def rot2 (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.cos θ : ℂ), (Real.sin θ : ℂ); -(Real.sin θ : ℂ), (Real.cos θ : ℂ)]

private theorem rot2_unitary (θ : ℝ) : (rot2 θ)ᴴ * rot2 θ = 1 := by
  have h : (Real.cos θ : ℂ) ^ 2 + (Real.sin θ : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.cos_sq_add_sin_sq θ
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [rot2, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
      Matrix.one_apply, star_def, ← Complex.ofReal_cos, ← Complex.ofReal_sin] <;>
    first | linear_combination h | ring

theorem two_flavor_oscProb_formula (θ : ℝ) (mSq : Fin 2 → ℝ) (x : ℝ) :
    let Δ := mSq 1 - mSq 0
    oscProb (rot2 θ) mSq x 0 1 = Real.sin (2 * θ) ^ 2 * Real.sin (Δ * x / 2) ^ 2 ∧
      oscProb (rot2 θ) mSq x 0 0 = 1 - Real.sin (2 * θ) ^ 2 * Real.sin (Δ * x / 2) ^ 2 := by
  dsimp only
  have h : oscAmp (rot2 θ) mSq x 0 1 = (Real.sin θ : ℂ) * (Real.cos θ : ℂ) *
      oscPhase (mSq 0 * x) * (oscPhase ((mSq 1 - mSq 0) * x) - 1) := by
    rw [oscAmp, Fin.sum_univ_two]
    change -(Real.sin θ : ℂ) * oscPhase (mSq 0 * x) * star (Real.cos θ : ℂ) +
      (Real.cos θ : ℂ) * oscPhase (mSq 1 * x) * star (Real.sin θ : ℂ) = _
    simp only [star_def, conj_ofReal]
    rw [show (mSq 1 - mSq 0) * x = mSq 1 * x + -(mSq 0 * x) by ring, oscPhase_add]
    have hcancel : oscPhase (mSq 0 * x) * oscPhase (-(mSq 0 * x)) = 1 := by
      rw [← oscPhase_add, add_neg_cancel, oscPhase_zero]
    linear_combination -(Real.sin θ : ℂ) * (Real.cos θ : ℂ) * oscPhase (mSq 1 * x) * hcancel
  have hd (s : ℝ) : ‖oscPhase s - 1‖ = |2 * Real.sin (s / 2)| := by
    unfold oscPhase
    rw [mul_comm, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs]
    simp [neg_div, abs_neg]
  have transition :
      oscProb (rot2 θ) mSq x 0 1 =
        Real.sin (2 * θ) ^ 2 * Real.sin ((mSq 1 - mSq 0) * x / 2) ^ 2 := by
    rw [oscProb, h, Real.sin_two_mul]
    simp only [norm_mul, hd, Complex.norm_real, Real.norm_eq_abs, oscPhase_norm, mul_one,
      abs_mul, mul_pow, sq_abs]
    ring
  have hrot := rot2_unitary θ
  have total := (oscProb_unitarity_sum (rot2 θ) mSq x 0 0
    ⟨hrot, mul_eq_one_comm.mp hrot⟩).1
  rw [Fin.sum_univ_two, transition] at total
  exact ⟨transition, eq_sub_of_add_eq total⟩

def cpAsymmetry {N : ℕ} (U : Matrix (Fin N) (Fin N) ℂ) (mSq : Fin N → ℝ)
    (x : ℝ) (α β : Fin N) : ℝ :=
  oscProb U mSq x α β - oscProb (antiMatrix U) mSq x α β

theorem cpAsymmetry_antisymm {N : ℕ} (U : Matrix (Fin N) (Fin N) ℂ)
    (mSq : Fin N → ℝ) (x : ℝ) (α β : Fin N) :
    cpAsymmetry U mSq x β α = -cpAsymmetry U mSq x α β ∧ cpAsymmetry U mSq x α α = 0 := by
  constructor
  · simp only [cpAsymmetry, oscProb_cpt_symmetry]
    ring
  · simp only [cpAsymmetry, oscProb_survival_cp_zero, sub_self]

private theorem normSq_add_three (a b c : ℂ) :
    normSq (a + b + c) = normSq a + normSq b + normSq c +
      2 * (a * conj b).re + 2 * (a * conj c).re + 2 * (b * conj c).re := by
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.add_re, Complex.add_im,
    Complex.conj_re, Complex.conj_im]
  ring

private theorem oscPhase_pair (s t : ℝ) :
    oscPhase s * conj (oscPhase t) = Complex.exp (((t - s : ℝ) : ℂ) * Complex.I) := by
  rw [oscPhase_conj, ← oscPhase_add]
  unfold oscPhase
  congr 2
  push_cast
  ring

private theorem osc_pair_difference (a b : ℂ) (s t : ℝ) :
    2 * ((a * oscPhase s) * conj (b * oscPhase t)).re -
      2 * ((conj a * oscPhase s) * conj (conj b * oscPhase t)).re =
      -4 * (a * conj b).im * Real.sin (t - s) := by
  let z := a * conj b
  have forward :
      (a * oscPhase s) * conj (b * oscPhase t) = z * (oscPhase s * conj (oscPhase t)) := by
    simp only [z, map_mul]
    ring
  have reverse :
      (conj a * oscPhase s) * conj (conj b * oscPhase t) =
        conj z * (oscPhase s * conj (oscPhase t)) := by
    simp only [z, map_mul, Complex.conj_conj]
    ring
  rw [forward, reverse, oscPhase_pair, Complex.exp_mul_I,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.conj_re, Complex.conj_im]
  change _ = -4 * z.im * _
  ring

private theorem sin_sum_difference (u v : ℝ) :
    Real.sin u + Real.sin v - Real.sin (u + v) =
      4 * Real.sin (u / 2) * Real.sin (v / 2) * Real.sin ((u + v) / 2) := by
  rw [Real.sin_add_sin, show (u + v) = 2 * ((u + v) / 2) by ring, Real.sin_two_mul]
  rw [show 2 * ((u + v) / 2) / 2 = (u + v) / 2 by ring]
  rw [show (u - v) / 2 = u / 2 - v / 2 by ring,
    show (u + v) / 2 = u / 2 + v / 2 by ring, Real.cos_sub, Real.cos_add]
  ring

theorem three_flavor_cp_asymmetry_jarlskog (U : Matrix (Fin 3) (Fin 3) ℂ)
    (hU : Uᴴ * U = 1) (mSq : Fin 3 → ℝ) (x : ℝ) (α β : Fin 3) :
    let Δ21 := mSq 1 - mSq 0
    let Δ32 := mSq 2 - mSq 1
    let Δ31 := mSq 2 - mSq 0
    cpAsymmetry U mSq x α β =
      16 * jarlskogQuartet U α 0 β 1 * Real.sin (Δ21 * x / 2) *
        Real.sin (Δ32 * x / 2) * Real.sin (Δ31 * x / 2) := by
  let z (j : Fin 3) := U β j * conj (U α j)
  let s (j : Fin 3) := mSq j * x
  have forward :
      oscAmp U mSq x α β =
        z 0 * oscPhase (s 0) + z 1 * oscPhase (s 1) + z 2 * oscPhase (s 2) := by
    simp only [oscAmp, Fin.sum_univ_three, z, s, star_def]
    ring
  have reverse :
      oscAmp (antiMatrix U) mSq x α β =
        conj (z 0) * oscPhase (s 0) + conj (z 1) * oscPhase (s 1) +
          conj (z 2) * oscPhase (s 2) := by
    simp only [oscAmp, Fin.sum_univ_three, z, s, antiMatrix, Matrix.map_apply,
      star_def, map_mul, Complex.conj_conj]
    ring
  have hnormSq (j : Fin 3) :
      normSq (conj (z j) * oscPhase (s j)) = normSq (z j * oscPhase (s j)) := by
    simp only [map_mul, Complex.normSq_conj]
  have him (j k : Fin 3) : (z j * conj (z k)).im = -jarlskogQuartet U α j β k := by
    have h : z j * conj (z k) = conj (U α j * U β k * conj (U α k) * conj (U β j)) := by
      simp only [z, map_mul, Complex.conj_conj]
      ring
    rw [h, Complex.conj_im, jarlskogQuartet]
  have expand :
      cpAsymmetry U mSq x α β = 4 * jarlskogQuartet U α 0 β 1 * Real.sin (s 1 - s 0) +
        4 * jarlskogQuartet U α 0 β 2 * Real.sin (s 2 - s 0) +
        4 * jarlskogQuartet U α 1 β 2 * Real.sin (s 2 - s 1) := by
    simp only [cpAsymmetry, oscProb, forward, reverse, Complex.sq_norm, normSq_add_three, hnormSq]
    have h01 := osc_pair_difference (z 0) (z 1) (s 0) (s 1)
    have h02 := osc_pair_difference (z 0) (z 2) (s 0) (s 2)
    have h12 := osc_pair_difference (z 1) (z 2) (s 1) (s 2)
    rw [him] at h01 h02 h12
    linear_combination h01 + h02 + h12
  have h12 : jarlskogQuartet U α 1 β 2 = jarlskogQuartet U α 0 β 1 := by
    rw [jarlskogQuartet_unitary_universal U hU α 1 β 2,
      jarlskogQuartet_unitary_universal U hU α 0 β 1]
    norm_num [leviSign]
  have h02 : jarlskogQuartet U α 0 β 2 = -jarlskogQuartet U α 0 β 1 := by
    rw [jarlskogQuartet_unitary_universal U hU α 0 β 2,
      jarlskogQuartet_unitary_universal U hU α 0 β 1]
    norm_num [leviSign]
  dsimp only
  rw [expand, h12, h02]
  have hs21 : s 1 - s 0 = (mSq 1 - mSq 0) * x := by dsimp [s]; ring
  have hs32 : s 2 - s 1 = (mSq 2 - mSq 1) * x := by dsimp [s]; ring
  have hs31 : s 2 - s 0 = (mSq 2 - mSq 0) * x := by dsimp [s]; ring
  have hsum : (mSq 1 - mSq 0) * x + (mSq 2 - mSq 1) * x = (mSq 2 - mSq 0) * x := by
    ring
  rw [hs21, hs32, hs31]
  have hsin := sin_sum_difference ((mSq 1 - mSq 0) * x) ((mSq 2 - mSq 1) * x)
  rw [hsum] at hsin
  linear_combination 4 * jarlskogQuartet U α 0 β 1 * hsin

theorem three_flavor_cp_asymmetry_bound (U : Matrix (Fin 3) (Fin 3) ℂ)
    (hU : Uᴴ * U = 1) (mSq : Fin 3 → ℝ) (x : ℝ) (α β : Fin 3) :
    |cpAsymmetry U mSq x α β| ≤ 16 * |jarlskogQuartet U α 0 β 1| := by
  rw [three_flavor_cp_asymmetry_jarlskog U hU]
  simp only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 16)]
  calc
    _ ≤ 16 * |jarlskogQuartet U α 0 β 1| * 1 * 1 * 1 := by
      gcongr <;> exact Real.abs_sin_le_one _
    _ = _ := by simp

theorem three_flavor_cp_asymmetry_zero_iff (U : Matrix (Fin 3) (Fin 3) ℂ)
    (hU : Uᴴ * U = 1) (mSq : Fin 3 → ℝ) (x : ℝ) (α β : Fin 3) :
    cpAsymmetry U mSq x α β = 0 ↔
      jarlskogQuartet U α 0 β 1 = 0 ∨ Real.sin ((mSq 1 - mSq 0) * x / 2) = 0 ∨
        Real.sin ((mSq 2 - mSq 1) * x / 2) = 0 ∨ Real.sin ((mSq 2 - mSq 0) * x / 2) = 0 := by
  rw [three_flavor_cp_asymmetry_jarlskog U hU]
  simp [mul_eq_zero, or_assoc]

theorem three_flavor_cp_asymmetry_zero_of_degenerate (U : Matrix (Fin 3) (Fin 3) ℂ)
    (hU : Uᴴ * U = 1) (mSq : Fin 3 → ℝ) (x : ℝ) (α β : Fin 3)
    {j k : Fin 3} (hjk : j ≠ k) (hdeg : mSq j = mSq k) : cpAsymmetry U mSq x α β = 0 := by
  apply (three_flavor_cp_asymmetry_zero_iff U hU mSq x α β).2
  fin_cases j <;> fin_cases k <;> simp_all

end D5.S3.Quantum.Gauge.SeesawNeutrinoOscillations4D
