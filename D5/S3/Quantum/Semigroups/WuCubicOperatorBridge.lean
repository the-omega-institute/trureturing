/- GID: D5/S3/Quantum/Semigroups/WuCubicOperatorBridge
   generality: I
   mirror-B: D5/B/S3/Quantum/Semigroups/WuCubicOperatorBridge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact operator-trace bridge for Wu's equal-cap two-mode cubic source. -/

import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.ForMathlib.Isometry
import D5.S3.Quantum.Semigroups.WuOneModeCubic
import Batteries.Tactic.OpenPrivate

/-! Operator-side data for the equal-cap Wu cubic source. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
open D5.S3.Quantum.Semigroups.TwistedTwoModeOUComparison (modeJump)

namespace D5.S3.Quantum.Semigroups.WuCubicOperatorBridge

open D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic (weight sourceDeficit alpha)
open private levels energyKernel gibbsLogColumn total normSq_conj_mul from
  D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic
open private gibbsOccupation gibbsLow gibbsHigh from
  D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic
open private gamma from D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic
open private jump_zero jump_one from
  D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic

abbrev Occupation := Fin 2 × Fin 2
abbrev Frame := Matrix Occupation (Fin 4) ℂ
abbrev Mat := Matrix Occupation Occupation ℂ

def D (r : ℝ) : Mat :=
  diagonal fun i => ((gibbsOccupation r i.1 * gibbsOccupation r i.2 : ℝ) : ℂ)
private def rootScale (r : ℝ) : ℝ := gibbsLow r ^ (1 / 3 : ℝ)
private def rootRatio (r : ℝ) : ℝ := Real.sqrt r
private def rootValue (r : ℝ) (i : Occupation) : ℝ :=
  ![rootScale r, rootScale r * rootRatio r,
    rootScale r * rootRatio r, rootScale r * r] (finProdFinEquiv i)
def G (r : ℝ) : Mat := diagonal fun i => (rootValue r i : ℂ)
def GInv (r : ℝ) : Mat := diagonal fun i => ((rootValue r i)⁻¹ : ℂ)

def dissipator (J X : Mat) : Mat :=
  (1 / 2 : ℂ) • ((Jᴴ * J) * X + X * (Jᴴ * J)) - Jᴴ * X * J

def generator (r : ℝ) (X : Mat) : Mat :=
  ∑ k : Fin 2,
    ((2 * (gibbsLow r : ℂ)) • dissipator (modeJump k) X +
      (2 * (gibbsHigh r : ℂ)) • dissipator (modeJump k)ᴴ X)

def spectral (U : Frame) (m n : ℝ) : Mat :=
  U * diagonal (fun i => (levels m n i : ℂ)) * Uᴴ
def transported (r : ℝ) (U : Frame) (m n : ℝ) : Mat :=
  GInv r * spectral U m n * GInv r

def sourceEnergy (r : ℝ) (U : Frame) (m n : ℝ) : ℝ :=
  (9 / 8 : ℝ) * (spectral U m n ^ 2 *
      (G r * generator r (transported r U m n) * G r)).trace.re

def sourceEntropy (r : ℝ) (U : Frame) (m n : ℝ) : ℝ :=
  m ^ 3 * Real.log (m ^ 3) + 2 * n ^ 3 * Real.log (n ^ 3) -
    total m n * Real.log (total m n) -
      ∑ i, gibbsLogColumn r U i * (levels m n i) ^ 3

private def spectralEntropy (r : ℝ) (U : Frame) (v : Fin 4 → ℝ) : ℝ :=
  (∑ i, v i ^ 3 * Real.log (v i ^ 3)) -
    (∑ i, v i ^ 3) * Real.log (∑ i, v i ^ 3) -
      ∑ i, gibbsLogColumn r U i * v i ^ 3

private theorem source_entropy_eq_spectral (r : ℝ) (U : Frame) (m n : ℝ) :
    sourceEntropy r U m n = spectralEntropy r U (levels m n) := by
  simp [sourceEntropy, spectralEntropy, total, levels, Fin.sum_univ_four] <;> ring

private theorem source_deficit_energy_entropy (r : ℝ) (U : Frame) (m n : ℝ) :
    sourceDeficit r U m n =
      (∑ i, ∑ j, weight U i j * energyKernel r (levels m n i) (levels m n j)) -
        alpha r * sourceEntropy r U m n := by
  rfl

private theorem entropy_frame_mul (U : Frame) (hU : Uᴴ * U = 1)
    (A B : Matrix (Fin 4) (Fin 4) ℂ) :
    (U * A * Uᴴ) * (U * B * Uᴴ) = U * (A * B) * Uᴴ := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Uᴴ U, hU, Matrix.one_mul]

private theorem entropy_trace_frame (U : Frame) (hU : Uᴴ * U = 1)
    (A : Matrix (Fin 4) (Fin 4) ℂ) :
    (U * A * Uᴴ).trace = A.trace := by
  rw [Matrix.trace_mul_cycle, hU, Matrix.one_mul]

private theorem spectral_entropy_operator (r : ℝ) (U : Frame)
    (hU : Uᴴ * U = 1) (hUU : U * Uᴴ = 1) (v : Fin 4 → ℝ) :
    let M := U * diagonal (fun i => (v i : ℂ)) * Uᴴ
    spectralEntropy r U v =
      (M ^ 3 * (cfc Real.log (M ^ 3) - cfc Real.log (D r))).trace.re -
        (M ^ 3).trace.re * Real.log (M ^ 3).trace.re := by
  let x : Fin 4 → ℝ := fun i => v i ^ 3
  let L : Matrix (Fin 4) (Fin 4) ℂ := diagonal fun i => (v i : ℂ)
  let M := U * L * Uᴴ
  let A : Matrix (Fin 4) (Fin 4) ℂ := diagonal fun i => (x i : ℂ)
  let B : Matrix (Fin 4) (Fin 4) ℂ := diagonal fun i => (Real.log (x i) : ℂ)
  change spectralEntropy r U v =
    (M ^ 3 * (cfc Real.log (M ^ 3) - cfc Real.log (D r))).trace.re -
      (M ^ 3).trace.re * Real.log (M ^ 3).trace.re
  have hPower : L ^ 3 = A := by
    simp only [L, A, Matrix.diagonal_pow]
    congr 1
    funext i
    simp only [Pi.pow_apply, x, Complex.ofReal_pow]
  have hCube : M ^ 3 = U * A * Uᴴ := by
    change (U * L * Uᴴ) ^ 3 = _
    calc
      (U * L * Uᴴ) ^ 3 = U * L ^ 3 * Uᴴ := by
        simp only [pow_succ (U * L * Uᴴ) 2, pow_succ L 2, pow_two, entropy_frame_mul U hU]
      _ = _ := by rw [hPower]
  have hU' : U.Isometry := hU
  have hUU' : Uᴴ.Isometry := by
    simpa only [Matrix.Isometry, Matrix.conjTranspose_conjTranspose] using hUU
  have hDiagLog : cfc Real.log A = B := by
    simpa only [A, B, Function.comp_def, RCLike.ofReal_eq_complex_ofReal] using
      Matrix.cfc_diagonal_real (𝕜 := ℂ) x Real.log
  have hLogCube : cfc Real.log (M ^ 3) = U * B * Uᴴ := by
    rw [hCube, Matrix.cfc_conj_isometry Real.log hU' hUU', hDiagLog]
  have hMass : (M ^ 3).trace.re = ∑ i, x i := by
    rw [hCube, entropy_trace_frame U hU]
    simp only [A, Matrix.trace_diagonal, Complex.re_sum, Complex.ofReal_re]
  have hEntropy :
      (M ^ 3 * cfc Real.log (M ^ 3)).trace.re = ∑ i, x i * Real.log (x i) := by
    rw [hLogCube, hCube, entropy_frame_mul U hU, entropy_trace_frame U hU]
    simp only [A, B, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal,
      Complex.re_sum, ← Complex.ofReal_mul, Complex.ofReal_re]
  let g : Occupation → ℝ := fun o => gibbsOccupation r o.1 * gibbsOccupation r o.2
  let K : Mat := diagonal fun o => (Real.log (g o) : ℂ)
  have hLogD : cfc Real.log (D r) = K := by
    simpa only [D, K, g, Function.comp_def, RCLike.ofReal_eq_complex_ofReal] using
      Matrix.cfc_diagonal_real (𝕜 := ℂ) g Real.log
  have hColumn (i : Fin 4) : ((Uᴴ * K * U) i i).re = gibbsLogColumn r U i := by
    rw [Matrix.mul_apply, Complex.re_sum, gibbsLogColumn]
    apply Finset.sum_congr rfl
    intro o _
    rw [show (Uᴴ * K) i o = (Uᴴ) i o * (Real.log (g o) : ℂ) from
      Matrix.mul_diagonal _ _ _ _, Matrix.conjTranspose_apply]
    change ((star (U o i) * (Real.log (g o) : ℂ)) * U o i).re =
      Complex.normSq (U o i) * Real.log (g o)
    rw [mul_right_comm, Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, normSq_conj_mul]
  have hGibbsTrace :
      (M ^ 3 * cfc Real.log (D r)).trace.re =
        ∑ i, gibbsLogColumn r U i * x i := by
    rw [hCube, hLogD]
    calc
      ((U * A * Uᴴ) * K).trace.re = (A * (Uᴴ * K * U)).trace.re := by
        rw [Matrix.mul_assoc (U * A) Uᴴ K, Matrix.trace_mul_cycle U A (Uᴴ * K),
          Matrix.trace_mul_comm (Uᴴ * K * U) A]
      _ = _ := by
        simp only [A, Matrix.trace, Matrix.diag_apply, Matrix.diagonal_mul,
          Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          zero_mul, sub_zero, hColumn]
        exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re, hEntropy, hGibbsTrace, hMass]
  unfold spectralEntropy
  exact sub_right_comm _ _ _

/-- Wu's cubic entropy evaluated with the ordinary trace and the Gibbs density `D r`.
The real matrix CFC uses `Real.log 0 = 0`, so zero levels are included. -/
private theorem source_entropy_operator (r : ℝ) (U : Frame)
    (hU : Uᴴ * U = 1) (hUU : U * Uᴴ = 1) (m n : ℝ) :
    sourceEntropy r U m n =
      (spectral U m n ^ 3 *
        (cfc Real.log (spectral U m n ^ 3) - cfc Real.log (D r))).trace.re -
      (spectral U m n ^ 3).trace.re * Real.log (spectral U m n ^ 3).trace.re := by
  rw [source_entropy_eq_spectral]
  exact spectral_entropy_operator r U hU hUU (levels m n)

private theorem rootScale_pos {r : ℝ} (hr : 0 ≤ r) : 0 < rootScale r := by
  unfold rootScale gibbsLow
  positivity

private theorem rootRatio_sq {r : ℝ} (hr : 0 ≤ r) : rootRatio r ^ 2 = r := by
  unfold rootRatio
  exact Real.sq_sqrt hr

private theorem rootValue_pos {r : ℝ} (hr : 1 ≤ r) (i : Occupation) :
    0 < rootValue r i := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  rcases i with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;>
    simp [rootValue, finProdFinEquiv,
      rootScale_pos (le_trans zero_le_one hr), rootRatio, hr,
      Real.sqrt_pos.2 hr0, hr0]

private theorem GInv_mul_G {r : ℝ} (hr : 1 ≤ r) :
    GInv r * G r = 1 := by
  rw [GInv, G, diagonal_mul_diagonal]
  congr 1
  funext i
  have hi : (rootValue r i : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (rootValue_pos hr i))
  exact inv_mul_cancel₀ hi

private theorem G_mul_GInv {r : ℝ} (hr : 1 ≤ r) :
    G r * GInv r = 1 := by
  rw [GInv, G, diagonal_mul_diagonal]
  congr 1
  funext i
  have hi : (rootValue r i : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (rootValue_pos hr i))
  exact mul_inv_cancel₀ hi

private theorem sandwich_transported {r : ℝ} (hr : 1 ≤ r) (U : Frame) (m n : ℝ) :
    G r * transported r U m n * G r = spectral U m n := by
  unfold transported
  calc
    _ = (G r * GInv r) * spectral U m n * (GInv r * G r) := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [G_mul_GInv hr, GInv_mul_G hr, Matrix.one_mul, Matrix.mul_one]

private theorem G_pow_six {r : ℝ} (hr : 1 ≤ r) : G r ^ 6 = D r := by
  have hr0 : 0 ≤ r := zero_le_one.trans hr
  have hl : 0 ≤ gibbsLow r := by unfold gibbsLow; positivity
  have hs : rootScale r ^ 6 = gibbsLow r ^ 2 := by
    unfold rootScale
    rw [← Real.rpow_mul_natCast hl]
    norm_num
  have hq : rootRatio r ^ 6 = r ^ 3 := by
    rw [show (6 : ℕ) = 2 * 3 by decide, pow_mul, rootRatio_sq hr0]
  rw [G, D, diagonal_pow]
  congr 1
  funext ⟨i, j⟩
  rw [Pi.pow_apply, ← Complex.ofReal_pow]
  apply congrArg Complex.ofReal
  fin_cases i <;> fin_cases j <;>
    simp [rootValue, finProdFinEquiv, gibbsOccupation, gibbsHigh, mul_pow, hs, hq] <;>
    ring

private theorem diagonal_conj_entry (g h : Occupation → ℂ) (J : Mat) (i j : Occupation) :
    (diagonal g * J * diagonal h) i j = g i * J i j * h j := by
  simp [Matrix.mul_apply, Matrix.diagonal_apply, mul_assoc]

private theorem modular_lower {r : ℝ} (hr : 1 ≤ r) (k : Fin 2) :
    G r * modeJump k * GInv r =
      ((Real.sqrt r)⁻¹ : ℂ) • modeJump k := by
  have hq : Real.sqrt r ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by linarith : 0 < r))
  have ht : rootScale r ≠ 0 := ne_of_gt (rootScale_pos (le_trans zero_le_one hr))
  have hs : (Real.sqrt r : ℂ) ^ 2 = (r : ℂ) := by
    exact_mod_cast rootRatio_sq (le_trans zero_le_one hr)
  ext ⟨a₁,a₂⟩ ⟨b₁,b₂⟩
  fin_cases k <;> fin_cases a₁ <;> fin_cases a₂ <;>
    fin_cases b₁ <;> fin_cases b₂ <;>
    simp [G, GInv, jump_zero, jump_one, Matrix.smul_apply,
      smul_eq_mul, rootValue, finProdFinEquiv, rootRatio]
  all_goals
    field_simp [hq, ht]
    all_goals try rw [hs]
    all_goals ring

private theorem modular_raise {r : ℝ} (hr : 1 ≤ r) (k : Fin 2) :
    G r * (modeJump k)ᴴ * GInv r =
      (Real.sqrt r : ℂ) • (modeJump k)ᴴ := by
  have hq : Real.sqrt r ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by linarith : 0 < r))
  have ht : rootScale r ≠ 0 := ne_of_gt (rootScale_pos (le_trans zero_le_one hr))
  have hs : (Real.sqrt r : ℂ) ^ 2 = (r : ℂ) := by
    exact_mod_cast rootRatio_sq (le_trans zero_le_one hr)
  ext ⟨a₁,a₂⟩ ⟨b₁,b₂⟩
  fin_cases k <;> fin_cases a₁ <;> fin_cases a₂ <;>
    fin_cases b₁ <;> fin_cases b₂ <;>
    simp [G, GInv, jump_zero, jump_one, Matrix.smul_apply,
      smul_eq_mul, rootValue, finProdFinEquiv, rootRatio]
  all_goals
    field_simp [hq, ht]
    all_goals try rw [hs]
    all_goals ring

private theorem projection_commute (r : ℝ) (k : Fin 2) :
    G r * ((modeJump k)ᴴ * modeJump k) =
      ((modeJump k)ᴴ * modeJump k) * G r ∧
    G r * (modeJump k * (modeJump k)ᴴ) =
      (modeJump k * (modeJump k)ᴴ) * G r := by
  constructor <;> ext ⟨a₁,a₂⟩ ⟨b₁,b₂⟩ <;>
    fin_cases k <;> fin_cases a₁ <;> fin_cases a₂ <;>
      fin_cases b₁ <;> fin_cases b₂ <;>
      simp [G, jump_zero, jump_one, Matrix.mul_apply, Matrix.diagonal_apply,
        Matrix.kroneckerMap_apply, Matrix.conjTranspose_apply,
        Fintype.sum_prod_type, Fin.sum_univ_two, rootValue, finProdFinEquiv]

set_option maxHeartbeats 6000000 in
-- Expanding both CAR dissipators requires polynomial normalization of all sixteen entries.
theorem operator_trace_modular_identity {r : ℝ} (hr : 1 ≤ r) (M : Mat) :
    G r * generator r (GInv r * M * GInv r) * G r =
      ∑ k : Fin 2, ((gibbsLow r : ℂ) •
          (((modeJump k)ᴴ * modeJump k) * M + M * ((modeJump k)ᴴ * modeJump k)) -
        (2 * (gibbsLow r : ℂ) * (r : ℂ)) • ((modeJump k)ᴴ * M * modeJump k) +
        (gibbsHigh r : ℂ) •
          ((modeJump k * (modeJump k)ᴴ) * M + M * (modeJump k * (modeJump k)ᴴ)) -
        (2 * (gibbsHigh r : ℂ) * (r : ℂ)⁻¹) •
          (modeJump k * M * (modeJump k)ᴴ)) := by
  have hq : Real.sqrt r ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by linarith [hr]))
  have ht : rootScale r ≠ 0 := ne_of_gt (rootScale_pos (le_trans zero_le_one hr))
  have hs : (Real.sqrt r : ℂ) ^ 2 = (r : ℂ) := by
    exact_mod_cast rootRatio_sq (le_trans zero_le_one hr)
  ext ⟨a₁, a₂⟩ ⟨b₁, b₂⟩
  fin_cases a₁ <;> fin_cases a₂ <;> fin_cases b₁ <;> fin_cases b₂ <;>
    simp [generator, dissipator, G, GInv, jump_zero, jump_one,
      Matrix.mul_apply, Matrix.diagonal_apply, Matrix.kroneckerMap_apply,
      Matrix.conjTranspose_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      rootValue, finProdFinEquiv, rootRatio, Matrix.smul_apply, smul_eq_mul]
  all_goals
    field_simp [hq, ht]
    all_goals try rw [hs]
    all_goals ring

private theorem trace_spectral_sandwich
    (U : Frame) (hU : Uᴴ * U = 1) (hUU : U * Uᴴ = 1)
    (v : Fin 4 → ℝ) (J : Mat) (a b : ℕ) :
    let M := U * diagonal (fun i => (v i : ℂ)) * Uᴴ
    (M ^ a * Jᴴ * M ^ b * J).trace.re =
      ∑ i, ∑ j, Complex.normSq ((Uᴴ * J * U) i j) * v j ^ a * v i ^ b := by
  let L := diagonal (fun i => (v i : ℂ))
  let M := U * L * Uᴴ
  let A := Uᴴ * J * U
  change (M ^ a * Jᴴ * M ^ b * J).trace.re =
    ∑ i, ∑ j, Complex.normSq (A i j) * v j ^ a * v i ^ b
  have conjugate_mul (X Y : Mat) :
      Uᴴ * (X * Y) * U = (Uᴴ * X * U) * (Uᴴ * Y * U) := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc U Uᴴ, hUU, Matrix.one_mul]
  have conjugate_M : Uᴴ * M * U = L := by
    calc
      _ = (Uᴴ * U) * L * (Uᴴ * U) := by simp only [M, Matrix.mul_assoc]
      _ = _ := by rw [hU, Matrix.one_mul, Matrix.mul_one]
  have conjugate_pow (n : ℕ) : Uᴴ * M ^ n * U = L ^ n := by
    induction n with
    | zero => simp [hU]
    | succ n ih => rw [pow_succ, conjugate_mul, ih, conjugate_M, pow_succ]
  have conjugate_adjoint : Uᴴ * Jᴴ * U = Aᴴ := by
    simp only [A, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  have trace_conjugate (X : Mat) : (Uᴴ * X * U).trace = X.trace := by
    rw [Matrix.trace_mul_cycle, hUU, Matrix.one_mul]
  rw [← trace_conjugate (M ^ a * Jᴴ * M ^ b * J)]
  simp only [conjugate_mul, conjugate_pow, conjugate_adjoint]
  change (L ^ a * Aᴴ * L ^ b * A).trace.re = _
  simp only [L, diagonal_pow, Matrix.trace, Matrix.diag_apply, Complex.re_sum]
  simp only [Matrix.mul_apply (N := A), Matrix.mul_diagonal,
    Matrix.diagonal_mul, Pi.pow_apply, Matrix.conjTranspose_apply, Complex.re_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [Complex.star_def, show
    ((v j : ℂ) ^ a * (starRingEnd ℂ) (A i j) * (v i : ℂ) ^ b * A i j) =
      A i j * (starRingEnd ℂ) (A i j) * ((v j : ℂ) ^ a * (v i : ℂ) ^ b) by ring,
    Complex.mul_conj, ← Complex.ofReal_pow, ← Complex.ofReal_pow,
    ← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_re]
  ring

private theorem weighted_spectral_energy
    {r : ℝ} (hr : 1 ≤ r) (U : Frame) (hU : Uᴴ * U = 1) (hUU : U * Uᴴ = 1)
    (v : Fin 4 → ℝ) :
    let M := U * diagonal (fun i => (v i : ℂ)) * Uᴴ
    (9 / 8 : ℝ) * (M ^ 2 * (G r * generator r (GInv r * M * GInv r) * G r)).trace.re =
      ∑ i, ∑ j, weight U i j * energyKernel r (v i) (v j) := by
  let M := U * diagonal (fun i => (v i : ℂ)) * Uᴴ
  dsimp only
  change (9 / 8 : ℝ) * (M ^ 2 * (G r * generator r (GInv r * M * GInv r) * G r)).trace.re = _
  have trace_sandwich (J : Mat) (a b : ℕ) :
      (M ^ a * Jᴴ * M ^ b * J).trace.re =
        ∑ i, ∑ j, Complex.normSq ((Uᴴ * J * U) i j) * v j ^ a * v i ^ b :=
    trace_spectral_sandwich U hU hUU v J a b
  have trace_anticommutator (J : Mat) :
      (M ^ 2 * (Jᴴ * J * M + M * (Jᴴ * J))).trace.re =
        2 * ∑ i, ∑ j, Complex.normSq ((Uᴴ * J * U) i j) * v j ^ 3 := by
    have left :
        (M ^ 2 * (Jᴴ * J * M)).trace = (M ^ 3 * Jᴴ * M ^ 0 * J).trace := by
      rw [Matrix.trace_mul_cycle', ← Matrix.mul_assoc M, ← pow_succ',
        pow_zero, Matrix.mul_one, Matrix.mul_assoc]
    have right :
        (M ^ 2 * (M * (Jᴴ * J))).trace = (M ^ 3 * Jᴴ * M ^ 0 * J).trace := by
      rw [← Matrix.mul_assoc, ← pow_succ, pow_zero, Matrix.mul_one, Matrix.mul_assoc]
    rw [Matrix.mul_add, Matrix.trace_add, Complex.add_re, left, right, trace_sandwich]
    simp only [pow_zero, mul_one, two_mul]
  have adjoint_normSq (J : Mat) (i j : Fin 4) :
      Complex.normSq ((Uᴴ * Jᴴ * U) j i) = Complex.normSq ((Uᴴ * J * U) i j) := by
    have h : Uᴴ * Jᴴ * U = (Uᴴ * J * U)ᴴ := by
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [h, Matrix.conjTranspose_apply, Complex.star_def, Complex.normSq_conj]
  have lowerCoeff :
      2 * (gibbsLow r : ℂ) * (r : ℂ) = ((2 * gibbsLow r * r : ℝ) : ℂ) := by
    push_cast
    rfl
  have upperCoeff :
      2 * (gibbsHigh r : ℂ) * (r : ℂ)⁻¹ = ((2 * gibbsLow r * r ^ 2 : ℝ) : ℂ) := by
    have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast (zero_lt_one.trans_le hr).ne'
    push_cast
    simp only [gibbsHigh, Complex.ofReal_mul, Complex.ofReal_pow]
    field_simp
    <;> ring
  have prefactor : gamma r = (9 / 4) * gibbsLow r := by
    rw [gamma, gibbsLow, div_mul_div_comm, mul_one]
  have mode_energy (J : Mat) :
      (9 / 8 : ℝ) *
        (M ^ 2 * ((gibbsLow r : ℂ) • (Jᴴ * J * M + M * (Jᴴ * J)) -
          (2 * (gibbsLow r : ℂ) * (r : ℂ)) • (Jᴴ * M * J) +
          (gibbsHigh r : ℂ) • (J * Jᴴ * M + M * (J * Jᴴ)) -
          (2 * (gibbsHigh r : ℂ) * (r : ℂ)⁻¹) • (J * M * Jᴴ))).trace.re =
        ∑ i, ∑ j, Complex.normSq ((Uᴴ * J * U) i j) * energyKernel r (v i) (v j) := by
    have adjoint_anticommutator := trace_anticommutator Jᴴ
    rw [Matrix.conjTranspose_conjTranspose, Finset.sum_comm] at adjoint_anticommutator
    simp only [adjoint_normSq J] at adjoint_anticommutator
    have adjoint_sandwich := trace_sandwich Jᴴ 2 1
    rw [Matrix.conjTranspose_conjTranspose, Finset.sum_comm] at adjoint_sandwich
    simp only [adjoint_normSq J, pow_one] at adjoint_sandwich
    have lower_sandwich := trace_sandwich J 2 1
    simp only [pow_one] at lower_sandwich
    rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re,
      Matrix.mul_add, Matrix.trace_add, Complex.add_re,
      Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
    simp only [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul,
      lowerCoeff, upperCoeff, Complex.re_ofReal_mul]
    rw [trace_anticommutator J, adjoint_anticommutator]
    simp only [Matrix.mul_assoc] at lower_sandwich adjoint_sandwich ⊢
    rw [lower_sandwich, adjoint_sandwich]
    simp only [mul_assoc, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [energyKernel, prefactor, gibbsHigh]
    ring
  rw [operator_trace_modular_identity hr]
  simp only [Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum, Finset.mul_sum, mode_energy]
  unfold weight
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  exact Finset.sum_comm

/-- The operator trace gives Wu's weighted cubic energy, including at zero levels. -/
private theorem source_energy_weighted_spectral
    {r : ℝ} (hr : 1 ≤ r) (U : Frame) (hU : Uᴴ * U = 1) (hUU : U * Uᴴ = 1)
    (m n : ℝ) :
    sourceEnergy r U m n =
      ∑ i, ∑ j, weight U i j * energyKernel r (levels m n i) (levels m n j) :=
  weighted_spectral_energy hr U hU hUU (levels m n)

/-- Wu v1 (3.54) at exponent three for two CAR modes with equal cap
`μ⁴ = r³` and normalized embedded spectrum `(m,n,n,1)`.
Here `M = G X G`, `G⁶ = D`, and the trace is unnormalized. -/
private theorem source_operator_inequality
    {r : ℝ} (hr : 1 ≤ r) (U : Frame) (hU : Uᴴ * U = 1) (hUU : U * Uᴴ = 1)
    {m n : ℝ} (hm : 0 ≤ m) (hmn : m ≤ n) (hn1 : n ≤ 1) :
    let X := transported r U m n
    let M := G r * X * G r
    alpha r * ((M ^ 3 * (cfc Real.log (M ^ 3) - cfc Real.log (D r))).trace.re -
        (M ^ 3).trace.re * Real.log (M ^ 3).trace.re) ≤
      (9 / 8 : ℝ) * (M ^ 2 * (G r * generator r X * G r)).trace.re := by
  obtain ⟨hHolder, hFrame, hDeficit⟩ :=
    WuRepeatedMiddleCubic.repeated_middle_lower_bound hr (WuOneModeCubic.one_mode_bound hr)
      U hU hUU hm hmn hn1
  have hNonneg := (add_nonneg hHolder hFrame).trans hDeficit
  rw [source_deficit_energy_entropy, ← source_energy_weighted_spectral hr U hU hUU] at hNonneg
  dsimp only
  rw [sandwich_transported hr U m n]
  change alpha r * _ ≤ sourceEnergy r U m n
  rw [← source_entropy_operator r U hU hUU m n]
  exact sub_nonneg.mp hNonneg

private theorem mul_log_scale (a x : ℝ) :
    (a * x) * Real.log (a * x) =
      a * (x * Real.log x) + (a * Real.log a) * x := by
  by_cases ha : a = 0
  · simp [ha]
  by_cases hx : x = 0
  · simp [hx]
  rw [Real.log_mul ha hx]
  ring

private theorem spectral_entropy_scale (r : ℝ) (U : Frame) (c : ℝ) (v : Fin 4 → ℝ) :
    spectralEntropy r U (fun i => c * v i) = c ^ 3 * spectralEntropy r U v := by
  have hGibbs :
      (∑ i, gibbsLogColumn r U i * (c * v i) ^ 3) =
        c ^ 3 * ∑ i, gibbsLogColumn r U i * v i ^ 3 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  unfold spectralEntropy
  rw [hGibbs]
  -- The log of the scale contributes the same term to the level sum and the mass term.
  simp only [mul_pow, mul_log_scale, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

private theorem weighted_spectral_energy_scale (r : ℝ) (U : Frame) (c : ℝ)
    (v : Fin 4 → ℝ) :
    (∑ i, ∑ j, weight U i j * energyKernel r (c * v i) (c * v j)) =
      c ^ 3 * ∑ i, ∑ j, weight U i j * energyKernel r (v i) (v j) := by
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  unfold energyKernel
  ring

/-- Wu's cubic Gibbs entropy is bounded by the Dirichlet trace for the equal-cap
two-mode spectrum `(m,n,n,L)`, including the zero matrix. -/
theorem source_operator_inequality_unnormalized
    {r : ℝ} (hr : 1 ≤ r) (U : Frame) (hU : Uᴴ * U = 1) (hUU : U * Uᴴ = 1)
    {m n L : ℝ} (hm : 0 ≤ m) (hmn : m ≤ n) (hnL : n ≤ L) :
    let v : Fin 4 → ℝ := ![m, n, n, L]
    let M := U * diagonal (fun i => (v i : ℂ)) * Uᴴ
    let X := GInv r * M * GInv r
    alpha r * ((M ^ 3 * (cfc Real.log (M ^ 3) - cfc Real.log (D r))).trace.re -
        (M ^ 3).trace.re * Real.log (M ^ 3).trace.re) ≤
      (9 / 8 : ℝ) * (M ^ 2 * (G r * generator r X * G r)).trace.re := by
  let v : Fin 4 → ℝ := ![m, n, n, L]
  let M := U * diagonal (fun i => (v i : ℂ)) * Uᴴ
  change alpha r * ((M ^ 3 * (cfc Real.log (M ^ 3) - cfc Real.log (D r))).trace.re -
      (M ^ 3).trace.re * Real.log (M ^ 3).trace.re) ≤
    (9 / 8 : ℝ) * (M ^ 2 * (G r * generator r (GInv r * M * GInv r) * G r)).trace.re
  rw [← spectral_entropy_operator r U hU hUU v, weighted_spectral_energy hr U hU hUU v]
  have hL : 0 ≤ L := hm.trans (hmn.trans hnL)
  have hNormalized := source_operator_inequality hr U hU hUU
    (m := m / L) (n := n / L) (div_nonneg hm hL)
    (div_le_div_of_nonneg_right hmn hL) (div_le_one_of_le₀ hnL hL)
  dsimp only at hNormalized
  rw [sandwich_transported hr U (m / L) (n / L)] at hNormalized
  change alpha r * _ ≤ sourceEnergy r U (m / L) (n / L) at hNormalized
  rw [← source_entropy_operator r U hU hUU, source_entropy_eq_spectral,
    source_energy_weighted_spectral hr U hU hUU] at hNormalized
  have scale_level (x : ℝ) (hx : 0 ≤ x) (hxL : x ≤ L) : L * (x / L) = x := by
    by_cases hL0 : L = 0
    · have hx0 : x = 0 := le_antisymm (hxL.trans_eq hL0) hx
      simp [hx0]
    · rw [mul_comm, div_mul_cancel₀ _ hL0]
  have hv : v = fun i => L * levels (m / L) (n / L) i := by
    funext i
    fin_cases i <;>
      simp [v, levels, scale_level m hm (hmn.trans hnL), scale_level n (hm.trans hmn) hnL]
  rw [hv, spectral_entropy_scale, weighted_spectral_energy_scale, mul_left_comm (alpha r)]
  exact mul_le_mul_of_nonneg_left hNormalized (pow_nonneg hL 3)

end D5.S3.Quantum.Semigroups.WuCubicOperatorBridge
