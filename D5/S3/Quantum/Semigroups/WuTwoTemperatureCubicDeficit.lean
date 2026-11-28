/- GID: D5/S3/Quantum/Semigroups/WuTwoTemperatureCubicDeficit
   generality: I
   mirror-B: D5/B/S3/Quantum/Semigroups/WuTwoTemperatureCubicDeficit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Physical two-temperature cubic deficit and conditional same-frame rank-two margin. -/

/-
proof_shape: content
admission_basis: escape-witness
escape_witness: Unitarity gives unit Gibbs overlap rows, and the CAR trace gives total
weight two for each physical jump. Functional calculus in the spectral and occupation
bases identifies the entropy trace, and the physical energy identity then identifies the
full ordinary-trace deficit. With the strict tracial rank-two operator baseline hbase
in the same frame, the spectral perturbation theorem gives the strict half-margin
for the normalized two-temperature operator deficit.
-/

import D5.S3.Quantum.Semigroups.WuNearRankTwoSpectralPerturbation
import D5.S3.Quantum.Semigroups.WuTwoTemperatureCubicPhysicalBridge

/-! The full operator deficit in Wu v1 (3.54)–(3.55), in one complex spectral
frame for the tracial rank-two baseline and the two-temperature perturbation. -/

set_option autoImplicit false

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

namespace D5.S3.Quantum.Semigroups.WuTwoTemperatureCubicDeficit

open WuCubicOperatorBridge (Frame Mat Occupation)
open WuRepeatedMiddleCubic (alpha)
open WuTwoModeCliffordPluecker (jump)
open WuTwoTemperatureCubicPhysicalBridge (D G GInv generator weight energy energy_eq_operator)
open WuNearRankTwoSpectralPerturbation
  (deficit entropy gibbsEigenvalue gibbsLogField mass rankTwoMargin near_rank_two_unequal_temperature)
open private normSq_conj_mul from D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic
open private jump_car from D5.S3.Quantum.Semigroups.WuTwoModeCliffordPluecker
open private entropy_frame_mul entropy_trace_frame trace_spectral_sandwich from
  D5.S3.Quantum.Semigroups.WuCubicOperatorBridge

/-- Row `i` is the probability distribution of spectral column `i` in the occupation basis. -/
def referenceProb (U : Frame) (i : Fin 4) (o : Occupation) : ℝ := Complex.normSq (U o i)

theorem referenceProb_nonneg (U : Frame) (i : Fin 4) (o : Occupation) :
    0 ≤ referenceProb U i o :=
  Complex.normSq_nonneg _

theorem referenceProb_sum (U : Frame) (hU : Uᴴ * U = 1) (i : Fin 4) :
    (∑ o, referenceProb U i o) = 1 := by
  have h := congrArg (fun A : Matrix (Fin 4) (Fin 4) ℂ => (A i i).re) hU
  simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum, normSq_conj_mul,
    Matrix.one_apply_eq, Complex.one_re, referenceProb] using h

theorem weight_nonneg (U : Frame) (j : Fin 2) (i k : Fin 4) : 0 ≤ weight U j i k :=
  Complex.normSq_nonneg _

theorem weight_sum (U : Frame) (hU : Uᴴ * U = 1) (hUU : U * Uᴴ = 1) (j : Fin 2) :
    (∑ i, ∑ k, weight U j i k) = 2 := by
  have hweights : ((jump j)ᴴ * jump j).trace.re = ∑ i, ∑ k, weight U j i k := by
    simpa only [pow_zero, Matrix.one_mul, Matrix.mul_one, mul_one, weight] using
      trace_spectral_sandwich U hU hUU (fun _ => 0) (jump j) 0 0
  have hcar := congrArg (fun A : Mat => A.trace.re) (jump_car j)
  change (jump j * (jump j)ᴴ + (jump j)ᴴ * jump j).trace.re = (1 : Mat).trace.re at hcar
  have hone : (1 : Mat).trace.re = 4 := by
    norm_num [Matrix.trace_one, Fintype.card_prod]
  rw [Matrix.trace_add, Complex.add_re, Matrix.trace_mul_comm (jump j) ((jump j)ᴴ), hone] at hcar
  linarith only [hweights, hcar]

def spectralMatrix (U : Frame) (v : Fin 4 → ℝ) : Mat :=
  U * diagonal (fun i => (v i : ℂ)) * Uᴴ

def operatorEntropy (R r : ℝ) (M : Mat) : ℝ :=
  (M ^ 3 * (cfc Real.log (M ^ 3) - cfc Real.log (D R r))).trace.re -
    (M ^ 3).trace.re * Real.log (M ^ 3).trace.re

/-- The ordinary-trace deficit with `X = G⁻¹ M G⁻¹` for the Gibbs sandwich. -/
def operatorDeficit (R r : ℝ) (M : Mat) : ℝ :=
  (9 / 8 : ℝ) * (M ^ 2 * (G R r * generator R r (GInv R r * M * GInv R r) * G R r)).trace.re -
    alpha R * operatorEntropy R r M

/-- The trace calculation of `WuTracialSpectatorRepeatedMiddle.entropy_eq_operator`
with the full product Gibbs diagonal. It also applies to zero roots. -/
theorem entropy_eq_operator (R r : ℝ) (U : Frame) (hU : Uᴴ * U = 1)
    (hUU : U * Uᴴ = 1) (v : Fin 4 → ℝ) :
    entropy (gibbsLogField R r (referenceProb U)) v = operatorEntropy R r (spectralMatrix U v) := by
  let L := diagonal (fun i => (v i : ℂ))
  let M := spectralMatrix U v
  let x : Fin 4 → ℝ := fun i => v i ^ 3
  let A := diagonal (fun i => (x i : ℂ))
  let B := diagonal (fun i => (Real.log (x i) : ℂ))
  let g : Occupation → ℝ := gibbsEigenvalue R r
  let K := diagonal (fun o => (Real.log (g o) : ℂ))
  change _ = (M ^ 3 * (cfc Real.log (M ^ 3) - cfc Real.log (D R r))).trace.re -
    (M ^ 3).trace.re * Real.log (M ^ 3).trace.re
  have hCube : M ^ 3 = U * A * Uᴴ := by
    have hPower : L ^ 3 = A := by
      simp only [L, A, Matrix.diagonal_pow]
      congr 1
      funext i
      simp only [Pi.pow_apply, x, Complex.ofReal_pow]
    change (U * L * Uᴴ) ^ 3 = _
    calc
      _ = U * L ^ 3 * Uᴴ := by
        simp only [pow_succ (U * L * Uᴴ) 2, pow_succ L 2, pow_two, entropy_frame_mul U hU]
      _ = _ := by rw [hPower]
  have hU' : U.Isometry := hU
  have hUU' : Uᴴ.Isometry := by
    simpa only [Matrix.Isometry, Matrix.conjTranspose_conjTranspose] using hUU
  have hLogA : cfc Real.log A = B := by
    simpa only [A, B, Function.comp_def, RCLike.ofReal_eq_complex_ofReal] using
      Matrix.cfc_diagonal_real (𝕜 := ℂ) x Real.log
  have hLogCube : cfc Real.log (M ^ 3) = U * B * Uᴴ := by
    rw [hCube, Matrix.cfc_conj_isometry Real.log hU' hUU', hLogA]
  have hMass : (M ^ 3).trace.re = ∑ i, x i := by
    rw [hCube, entropy_trace_frame U hU]
    simp only [A, Matrix.trace_diagonal, Complex.re_sum, Complex.ofReal_re]
  have hSelf : (M ^ 3 * cfc Real.log (M ^ 3)).trace.re = ∑ i, x i * Real.log (x i) := by
    rw [hLogCube, hCube, entropy_frame_mul U hU, entropy_trace_frame U hU]
    simp only [A, B, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal,
      Complex.re_sum, ← Complex.ofReal_mul, Complex.ofReal_re]
  have hLogD : cfc Real.log (D R r) = K := by
    change cfc Real.log (diagonal fun o => (g o : ℂ)) = K
    simpa only [K, Function.comp_def, RCLike.ofReal_eq_complex_ofReal] using
      Matrix.cfc_diagonal_real (𝕜 := ℂ) g Real.log
  have hColumn (i : Fin 4) : ((Uᴴ * K * U) i i).re = gibbsLogField R r (referenceProb U) i := by
    rw [Matrix.mul_apply, Complex.re_sum, gibbsLogField]
    apply Finset.sum_congr rfl
    intro o _
    rw [show (Uᴴ * K) i o = (Uᴴ) i o * (Real.log (g o) : ℂ) from Matrix.mul_diagonal _ _ _ _,
      Matrix.conjTranspose_apply, mul_right_comm, Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, normSq_conj_mul,
      referenceProb, g]
  have hGibbs : (M ^ 3 * cfc Real.log (D R r)).trace.re =
      ∑ i, x i * gibbsLogField R r (referenceProb U) i := by
    rw [hCube, hLogD, Matrix.mul_assoc (U * A) Uᴴ K, Matrix.trace_mul_cycle U A (Uᴴ * K),
      Matrix.trace_mul_comm (Uᴴ * K * U) A]
    simp only [A, Matrix.trace, Matrix.diag_apply, Matrix.diagonal_mul,
      Complex.re_sum, Complex.re_ofReal_mul, hColumn]
  rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re, hSelf, hGibbs, hMass]
  simp only [entropy, mass, Finset.sum_sub_distrib, x]

/-- The spectral deficit with the literal CAR weights equals the full operator deficit. -/
theorem deficit_eq_operator {R r : ℝ} (hR : 0 < R) (hr : 0 < r) (U : Frame)
    (hU : Uᴴ * U = 1) (hUU : U * Uᴴ = 1) (v : Fin 4 → ℝ) :
    deficit R r (weight U 0) (weight U 1) (referenceProb U) v =
      operatorDeficit R r (spectralMatrix U v) := by
  change energy R U 0 v + energy r U 1 v -
    alpha R * entropy (gibbsLogField R r (referenceProb U)) v = _
  rw [entropy_eq_operator R r U hU hUU v, operatorDeficit]
  exact congrArg (fun E : ℝ => E - alpha R * operatorEntropy R r (spectralMatrix U v))
    (energy_eq_operator hR hr U hU hUU v)

/-- The strict tracial rank-two estimate in the same frame supplies the baseline
for the normalized near-rank-two bound at two ratios. -/
theorem near_rank_two_operator_deficit {R r ε u v m : ℝ} (hR : 1 < R) (hr : r ∈ Set.Icc 1 R)
    (hu : 0 ≤ u) (huv : u ≤ v) (hvm : v ≤ m) (hm : m ≤ 1) (hve : v ≤ ε)
    (hε : ε ≤ min (rankTwoMargin R / 36) ((2 * (1 + R ^ 3)) ^ (-(1 / 3) : ℝ)))
    (hlog : Real.log r ≤ rankTwoMargin R / 104)
    (U : Frame) (hU : Uᴴ * U = 1) (hUU : U * Uᴴ = 1)
    (hbase : rankTwoMargin R * mass ![0, 0, m, 1] <
      operatorDeficit R 1 (spectralMatrix U ![0, 0, m, 1])) :
    rankTwoMargin R / 2 < operatorDeficit R r (spectralMatrix U ![u, v, m, 1]) := by
  have hR₀ := zero_lt_one.trans hR
  rw [← deficit_eq_operator hR₀ zero_lt_one U hU hUU ![0, 0, m, 1]] at hbase
  rw [← deficit_eq_operator hR₀ (zero_lt_one.trans_le hr.1) U hU hUU ![u, v, m, 1]]
  exact near_rank_two_unequal_temperature hR hr hu huv hvm hm hve hε hlog
    (weight_nonneg U 0) (weight_sum U hU hUU 0) (weight_nonneg U 1) (weight_sum U hU hUU 1)
    (referenceProb_nonneg U) (referenceProb_sum U hU) hbase

end D5.S3.Quantum.Semigroups.WuTwoTemperatureCubicDeficit
