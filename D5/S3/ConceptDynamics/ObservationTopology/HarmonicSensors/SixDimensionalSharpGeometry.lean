/- GID: D5/S3/ConceptDynamics/ObservationTopology/HarmonicSensors/SixDimensionalSharpGeometry
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ObservationTopology/HarmonicSensors/SixDimensionalSharpGeometry
   mirror-E: none(waiver:pure-mathematical-argument)
   anchors: []
   utility: none
   digest: Physical six-coordinate correlation and its moving-domain sharp supremum limit. -/

import D5.S3.ConceptDynamics.ObservationTopology.CircleGraphCharts
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Data.Int.GCD
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Data.Complex.BigOperators
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.CStarAlgebra.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
open WithLp Filter Set
open scoped BigOperators Matrix Classical Topology Matrix.Norms.L2Operator

namespace D5.S3.ConceptDynamics.ObservationTopology.HarmonicSensors.PairedDelayGeometry

noncomputable section

variable {ι : Type*} [Fintype ι]
/-- Rows are the present readout and the readout at the specified delay. -/
def delayMatrix (k : ι → ℕ) (a : ι → ℝ) (θ φ : ℝ) :
    Matrix (Fin 2) (ι × Fin 2) ℝ :=
  fun i p => if i = 0 then pairedSensor k a φ p
    else pairedSensor k a (φ - θ) p
/-- Select Mathlib's actual Frobenius norm independently of the spectral norm. -/
def frobeniusNorm {m n : Type*} [Fintype m] [Fintype n]
    (M : Matrix m n ℝ) : ℝ := by
  letI := Matrix.frobeniusNormedAddCommGroup (m := m) (n := n) (α := ℝ)
  exact ‖M‖
/-- The denominator is the actual spectral norm on Euclidean spaces. -/
def matrixStableRank {m n : Type*} [Fintype m] [Fintype n]
    (M : Matrix m n ℝ) : ℝ := frobeniusNorm M ^ 2 / ‖M‖ ^ 2

/-- Different states means different points on the physical unit circle. -/
def stableRankValues (k : ι → ℕ) (a : ι → ℝ) (θ : ℝ) : Set ℝ :=
  {r | ∃ φ ψ : ℝ, circleState φ ≠ circleState ψ ∧
    r = matrixStableRank (delayMatrix k a θ φ - delayMatrix k a θ ψ)}
def sensorStableRank (k : ι → ℕ) (a : ι → ℝ) (θ : ℝ) : ℝ :=
  sInf (stableRankValues k a θ)
def rowEnergy (k : ι → ℕ) (a : ι → ℝ) (d : ℝ) : ℝ :=
  4 * ∑ i, a i ^ 2 * Real.sin ((k i : ℝ) * d / 2) ^ 2
def rowCorrelation (k : ι → ℕ) (a : ι → ℝ) (θ d : ℝ) : ℝ :=
  4 * ∑ i, a i ^ 2 * Real.cos ((k i : ℝ) * θ) *
    Real.sin ((k i : ℝ) * d / 2) ^ 2
private theorem paired_shifted_dot (k : ι → ℕ) (a : ι → ℝ) (φ ψ t : ℝ) :
    (∑ p, (pairedSensor k a φ p - pairedSensor k a ψ p) *
      (pairedSensor k a (φ - t) p - pairedSensor k a (ψ - t) p)) =
    rowCorrelation k a t (φ - ψ) := by
  classical
  rw [Fintype.sum_prod_type]
  unfold rowCorrelation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [pairedSensor, PiLp.toLp_apply, Fin.sum_univ_two]
  norm_num
  have hu : (k i : ℝ) * (φ - t) = (k i : ℝ) * φ - (k i : ℝ) * t := by ring
  have hv : (k i : ℝ) * (ψ - t) = (k i : ℝ) * ψ - (k i : ℝ) * t := by ring
  have hd : ((k i : ℝ) * φ - (k i : ℝ) * ψ) / 2 =
      (k i : ℝ) * (φ - ψ) / 2 := by ring
  rw [hu, hv]
  calc
    _ = a i ^ 2 *
        ((Real.cos ((k i : ℝ) * φ) - Real.cos ((k i : ℝ) * ψ)) *
          (Real.cos ((k i : ℝ) * φ - (k i : ℝ) * t) -
            Real.cos ((k i : ℝ) * ψ - (k i : ℝ) * t)) +
        (Real.sin ((k i : ℝ) * φ) - Real.sin ((k i : ℝ) * ψ)) *
          (Real.sin ((k i : ℝ) * φ - (k i : ℝ) * t) -
            Real.sin ((k i : ℝ) * ψ - (k i : ℝ) * t))) := by ring
    _ = _ := by rw [planar_chord_dot, hd]; ring
theorem paired_chord_norm_sq (k : ι → ℕ) (a : ι → ℝ) (φ ψ : ℝ) :
    ‖pairedSensor k a φ - pairedSensor k a ψ‖ ^ 2 =
      rowEnergy k a (φ - ψ) := by
  have h := paired_shifted_dot k a φ ψ 0
  simp only [sub_zero, rowCorrelation, mul_zero, Real.cos_zero, mul_one] at h
  rw [EuclideanSpace.real_norm_sq_eq]
  simpa only [PiLp.sub_apply, pow_two, rowEnergy] using h

/-- This is the row Gram matrix of the actual rectangular delay difference. -/
theorem paired_delay_gram (k : ι → ℕ) (a : ι → ℝ) (θ φ ψ : ℝ) :
    let M := delayMatrix k a θ φ - delayMatrix k a θ ψ
    M * Mᴴ = fun i j => if i = j then rowEnergy k a (φ - ψ)
      else rowCorrelation k a θ (φ - ψ) := by
  classical
  dsimp only
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sub_apply,
      delayMatrix, rowEnergy, rowCorrelation, pow_two] using paired_shifted_dot k a φ ψ 0
  · simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sub_apply,
      delayMatrix] using paired_shifted_dot k a φ ψ θ
  · simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sub_apply,
      delayMatrix, mul_comm] using paired_shifted_dot k a φ ψ θ
  · have h := paired_shifted_dot k a (φ - θ) (ψ - θ) 0
    have hd : (φ - θ) - (ψ - θ) = φ - ψ := by ring
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sub_apply,
      delayMatrix, hd, rowEnergy, rowCorrelation, pow_two] using h
private theorem frobenius_sq_eq_gram_trace {m n : Type*} [Fintype m] [Fintype n]
    (M : Matrix m n ℝ) : frobeniusNorm M ^ 2 = ∑ i, (M * Mᴴ) i i := by
  classical
  have hnorm : frobeniusNorm M = Real.sqrt (∑ i, ∑ j, M i j ^ 2) := by
    letI := Matrix.frobeniusNormedAddCommGroup (m := m) (n := n) (α := ℝ)
    change ‖M‖ = Real.sqrt (∑ i, ∑ j, M i j ^ 2)
    rw [Matrix.frobenius_norm_def, Real.sqrt_eq_rpow]
    simp only [Real.rpow_two, Real.norm_eq_abs, sq_abs]
  rw [hnorm, Real.sq_sqrt (by positivity)]
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, pow_two]
theorem paired_frobenius_sq (k : ι → ℕ) (a : ι → ℝ) (θ φ ψ : ℝ) :
    frobeniusNorm (delayMatrix k a θ φ - delayMatrix k a θ ψ) ^ 2 =
      2 * rowEnergy k a (φ - ψ) := by
  rw [frobenius_sq_eq_gram_trace, paired_delay_gram]
  simp [Fin.sum_univ_two, two_mul]

end
end D5.S3.ConceptDynamics.ObservationTopology.HarmonicSensors.PairedDelayGeometry

namespace D5.S3.ConceptDynamics.ObservationTopology.HarmonicSensors.TwoRowSpectralNorm

open PairedDelayGeometry

noncomputable section

/-- The two diagonal entries agree; no eigenvalue or norm formula is assumed. -/
theorem balanced_gram_norm (A B : ℝ) (hA : 0 ≤ A) :
    ‖(Matrix.of (fun i j : Fin 2 => if i = j then A else B))‖ =
      A + |B| := by
  let r : ℝ := (Real.sqrt 2)⁻¹
  have hr : r ^ 2 = 1 / 2 := by
    dsimp [r]
    rw [inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  let U : Matrix (Fin 2) (Fin 2) ℝ := !![r, r; r, -r]
  let D : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![A + B, A - B]
  have hstar : star U = U := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [U, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]
  have hunit : U ∈ unitary (Matrix (Fin 2) (Fin 2) ℝ) := by
    apply Matrix.mem_unitaryGroup_iff.mpr
    rw [hstar]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [U, Matrix.mul_apply, Fin.sum_univ_two] <;> nlinarith [hr]
  have hdiag : U * D * U = Matrix.of (fun i j : Fin 2 => if i = j then A else B) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [U, D, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.diagonal_apply, Matrix.vecMul_diagonal] <;>
      ring_nf <;> norm_num [hr] <;> ring
  rw [← hdiag, CStarRing.norm_mul_mem_unitary _ hunit,
    CStarRing.norm_mem_unitary_mul _ hunit]
  change ‖Matrix.diagonal (![A + B, A - B] : Fin 2 → ℝ)‖ = A + |B|
  rw [Matrix.l2_opNorm_diagonal]
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (add_nonneg hA (abs_nonneg B))).mpr
    intro i
    fin_cases i
    · change |A + B| ≤ A + |B|
      exact abs_le.mpr ⟨by linarith [neg_abs_le B], by linarith [le_abs_self B]⟩
    · change |A - B| ≤ A + |B|
      exact abs_le.mpr ⟨by linarith [le_abs_self B], by linarith [neg_abs_le B]⟩
  · by_cases hB : 0 ≤ B
    · have h := norm_le_pi_norm (![A + B, A - B] : Fin 2 → ℝ) 0
      simpa [Real.norm_eq_abs, abs_of_nonneg hB,
        abs_of_nonneg (add_nonneg hA hB)] using h
    · have hB' : B ≤ 0 := (lt_of_not_ge hB).le
      have h := norm_le_pi_norm (![A + B, A - B] : Fin 2 → ℝ) 1
      simpa [Real.norm_eq_abs, abs_of_nonpos hB',
        abs_of_nonneg (sub_nonneg.mpr (hB'.trans hA))] using h
/-- The actual rectangular matrix is related to its row Gram matrix by the C*-identity. -/
private theorem spectral_sq_of_balanced_gram {n : Type*} [Fintype n]
    (M : Matrix (Fin 2) n ℝ) (A B : ℝ) (hA : 0 ≤ A)
    (hG : M * Mᴴ = Matrix.of (fun i j => if i = j then A else B)) :
    ‖M‖ ^ 2 = A + |B| := by
  classical
  have h := Matrix.l2_opNorm_conjTranspose_mul_self Mᴴ
  rw [Matrix.conjTranspose_conjTranspose, Matrix.l2_opNorm_conjTranspose, hG,
    balanced_gram_norm A B hA] at h
  simpa only [pow_two] using h.symm
theorem paired_spectral_sq {ι : Type*} [Fintype ι]
    (k : ι → ℕ) (a : ι → ℝ) (θ φ ψ : ℝ) :
    ‖Matrix.of (delayMatrix k a θ φ - delayMatrix k a θ ψ)‖ ^ 2 =
      rowEnergy k a (φ - ψ) + |rowCorrelation k a θ (φ - ψ)| := by
  have hA : 0 ≤ rowEnergy k a (φ - ψ) := by
    rw [← paired_chord_norm_sq k a φ ψ]
    positivity
  exact spectral_sq_of_balanced_gram _ _ _ hA (paired_delay_gram k a θ φ ψ)

set_option backward.isDefEq.respectTransparency false in
theorem paired_pointwise_stable_rank {ι : Type*} [Fintype ι]
    (k : ι → ℕ) (a : ι → ℝ) (θ φ ψ : ℝ)
    (hA : 0 < rowEnergy k a (φ - ψ)) :
    matrixStableRank (delayMatrix k a θ φ - delayMatrix k a θ ψ) =
      2 / (1 + |rowCorrelation k a θ (φ - ψ)| / rowEnergy k a (φ - ψ)) := by
  rw [matrixStableRank, paired_frobenius_sq]
  change 2 * rowEnergy k a (φ - ψ) /
      ‖Matrix.of (delayMatrix k a θ φ - delayMatrix k a θ ψ)‖ ^ 2 = _
  rw [paired_spectral_sq]
  have hsum : rowEnergy k a (φ - ψ) + |rowCorrelation k a θ (φ - ψ)| ≠ 0 :=
    ne_of_gt (add_pos_of_pos_of_nonneg hA (abs_nonneg _))
  field_simp [ne_of_gt hA, hsum]
  <;> ring

end
end D5.S3.ConceptDynamics.ObservationTopology.HarmonicSensors.TwoRowSpectralNorm

namespace D5.S3.ConceptDynamics.ObservationTopology.HarmonicSensors.SixDimensionalSharpGeometry

open PairedDelayGeometry TwoRowSpectralNorm

noncomputable section

def normalization (ε : ℝ) : ℝ := 9 + 20 * ε
def frequencies : Fin 3 → ℕ := ![2, 3, 4]

def amplitudes (ε : ℝ) : Fin 3 → ℝ :=
  ![Real.sqrt ε / Real.sqrt (normalization ε),
    1 / Real.sqrt (normalization ε),
    Real.sqrt ε / Real.sqrt (normalization ε)]
def sensor (ε φ : ℝ) : EuclideanSpace ℝ (Fin 3 × Fin 2) :=
  pairedSensor frequencies (amplitudes ε) φ
def chordParameter (φ ψ : ℝ) : ℝ := 4 * Real.cos ((φ - ψ) / 2) ^ 2 - 1
def chordPolynomial (ε q : ℝ) : ℝ := q ^ 2 * (1 + ε * (q - 1)) + 2 * ε
def correlationQuotient (ε q : ℝ) : ℝ :=
  (ε / 2) * |q * (q + 1) * (2 - q)| / chordPolynomial ε q
theorem normalization_pos (ε : ℝ) (hε : 0 < ε) :
    0 < normalization ε := by unfold normalization; linarith

private theorem amplitude_squares (ε : ℝ) (hε : 0 < ε) (i : Fin 3) :
    amplitudes ε i ^ 2 = (![ε / normalization ε, 1 / normalization ε,
      ε / normalization ε] : Fin 3 → ℝ) i := by
  have hZ := normalization_pos ε hε
  fin_cases i <;>
    simp [amplitudes, div_pow, Real.sq_sqrt hε.le, Real.sq_sqrt hZ.le]
private theorem sine_squares_234 (v : ℝ) :
    Real.sin (2 * v) ^ 2 = 4 * Real.sin v ^ 2 * Real.cos v ^ 2 ∧
    Real.sin (3 * v) ^ 2 = Real.sin v ^ 2 * (4 * Real.cos v ^ 2 - 1) ^ 2 ∧
    Real.sin (4 * v) ^ 2 =
      16 * Real.sin v ^ 2 * Real.cos v ^ 2 * (2 * Real.cos v ^ 2 - 1) ^ 2 := by
  have htrig := Real.sin_sq_add_cos_sq v
  have h3 : Real.sin (3 * v) = Real.sin v * (4 * Real.cos v ^ 2 - 1) := by
    rw [Real.sin_three_mul]
    linear_combination (-4 * Real.sin v) * htrig
  refine ⟨by rw [Real.sin_two_mul]; ring, by rw [h3]; ring, ?_⟩
  rw [show 4 * v = 2 * (2 * v) by ring, Real.sin_two_mul,
    Real.sin_two_mul, Real.cos_two_mul]
  ring
theorem chord_parameter_mem (φ ψ : ℝ) : chordParameter φ ψ ∈ Set.Icc (-1) 3 := by
  have hs := sq_nonneg (Real.sin ((φ - ψ) / 2))
  have hc := sq_nonneg (Real.cos ((φ - ψ) / 2))
  have ht := Real.sin_sq_add_cos_sq ((φ - ψ) / 2)
  constructor <;> unfold chordParameter <;> nlinarith
theorem polynomial_pos (ε q : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 2)
    (hq : q ∈ Set.Icc (-1) 3) : 0 < chordPolynomial ε q := by
  have hf : 0 ≤ 1 + ε * (q - 1) := by
    nlinarith [mul_nonneg hε.le (show 0 ≤ q + 1 by linarith [hq.1])]
  have hh := mul_nonneg (sq_nonneg q) hf
  unfold chordPolynomial
  linarith
theorem six_chord_norm_sq (ε φ ψ : ℝ) (hε : 0 < ε) :
    ‖sensor ε φ - sensor ε ψ‖ ^ 2 =
      (4 * Real.sin ((φ - ψ) / 2) ^ 2 / normalization ε) *
        chordPolynomial ε (chordParameter φ ψ) := by
  rw [sensor, sensor, paired_chord_norm_sq]
  unfold rowEnergy
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  simp only [frequencies, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Nat.cast_ofNat, amplitude_squares ε hε]
  have h2 : 2 * (φ - ψ) / 2 = 2 * ((φ - ψ) / 2) := by ring
  have h3 : 3 * (φ - ψ) / 2 = 3 * ((φ - ψ) / 2) := by ring
  have h4 : 4 * (φ - ψ) / 2 = 4 * ((φ - ψ) / 2) := by ring
  rw [h2, h3, h4]
  rcases sine_squares_234 ((φ - ψ) / 2) with ⟨hs2, hs3, hs4⟩
  rw [hs2, hs3, hs4]
  unfold chordPolynomial chordParameter
  ring
theorem six_row_energy (ε d : ℝ) (hε : 0 < ε) :
    rowEnergy frequencies (amplitudes ε) d =
      (4 * Real.sin (d / 2) ^ 2 / normalization ε) *
        chordPolynomial ε (4 * Real.cos (d / 2) ^ 2 - 1) := by
  have h := six_chord_norm_sq ε d 0 hε
  rw [sensor, sensor, paired_chord_norm_sq] at h
  simpa [chordParameter] using h
theorem six_row_correlation (ε d : ℝ) (hε : 0 < ε) :
    rowCorrelation frequencies (amplitudes ε) (Real.pi / 6) d =
      (4 * Real.sin (d / 2) ^ 2 / normalization ε) *
        (ε / 2) *
        ((4 * Real.cos (d / 2) ^ 2 - 1) * (4 * Real.cos (d / 2) ^ 2) *
          (3 - 4 * Real.cos (d / 2) ^ 2)) := by
  unfold rowCorrelation
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  simp only [frequencies, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Nat.cast_ofNat, amplitude_squares ε hε]
  have ht2 : (2 : ℝ) * (Real.pi / 6) = Real.pi / 3 := by ring
  have ht3 : (3 : ℝ) * (Real.pi / 6) = Real.pi / 2 := by ring
  have ht4 : (4 : ℝ) * (Real.pi / 6) = Real.pi - Real.pi / 3 := by ring
  rw [ht2, ht3, ht4, Real.cos_pi_div_three, Real.cos_pi_div_two,
    Real.cos_pi_sub, Real.cos_pi_div_three]
  have h2 : 2 * d / 2 = 2 * (d / 2) := by ring
  have h4 : 4 * d / 2 = 4 * (d / 2) := by ring
  rw [h2, h4]
  rcases sine_squares_234 (d / 2) with ⟨hs2, _, hs4⟩
  rw [hs2, hs4]
  ring

end
end D5.S3.ConceptDynamics.ObservationTopology.HarmonicSensors.SixDimensionalSharpGeometry

namespace D5.S3.ConceptDynamics.ObservationTopology.HarmonicSensors.SixDimensionalSharpGeometry
open PairedDelayGeometry TwoRowSpectralNorm
noncomputable section

theorem separated_third_turn :
    circleState (2 * Real.pi / 3) ≠ circleState 0 := by
  have h : ‖circleState (2 * Real.pi / 3) - circleState 0‖ ^ 2 = 3 := by
    rw [circle_chord_norm_sq]
    have ha : (2 * Real.pi / 3 - 0) / 2 = Real.pi / 3 := by ring
    rw [ha]
    have ht := Real.sin_sq_add_cos_sq (Real.pi / 3)
    rw [Real.cos_pi_div_three] at ht
    nlinarith
  intro heq
  simp [heq] at h

theorem short_states_distinct :
    ∀ᶠ d : ℝ in 𝓝[>] 0, circleState d ≠ circleState 0 := by
  have hup : ∀ᶠ d : ℝ in 𝓝[>] 0, d < 2 * Real.pi :=
    (gt_mem_nhds (by positivity : (0 : ℝ) < 2 * Real.pi)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hup] with d hd0 hdπ
  have hs : 0 < Real.sin (d / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by exact half_pos hd0) (by linarith)
  intro heq
  have h := circle_chord_norm_sq d 0
  simp [heq] at h
  nlinarith

end
end D5.S3.ConceptDynamics.ObservationTopology.HarmonicSensors.SixDimensionalSharpGeometry

namespace D5.S3.ConceptDynamics.ObservationTopology.HarmonicSensors.SixDimensionalSharpGeometry

open PairedDelayGeometry TwoRowSpectralNorm

noncomputable section

def actualRank (ε : ℝ) : ℝ :=
  sensorStableRank frequencies (amplitudes ε) (Real.pi / 6)
private theorem six_energy_pos (ε φ ψ : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 2)
    (hne : circleState φ ≠ circleState ψ) :
    0 < rowEnergy frequencies (amplitudes ε) (φ - ψ) := by
  have hb : 0 < ‖circleState φ - circleState ψ‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hs : 0 < 4 * Real.sin ((φ - ψ) / 2) ^ 2 := by
    rw [← circle_chord_norm_sq φ ψ]
    positivity
  rw [six_row_energy ε _ hε]
  exact mul_pos (div_pos hs (normalization_pos ε hε))
    (polynomial_pos ε _ hε hε' (chord_parameter_mem φ ψ))
theorem six_correlation_ratio (ε φ ψ : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 2)
    (hne : circleState φ ≠ circleState ψ) :
    |rowCorrelation frequencies (amplitudes ε) (Real.pi / 6) (φ - ψ)| /
      rowEnergy frequencies (amplitudes ε) (φ - ψ) =
      correlationQuotient ε (chordParameter φ ψ) := by
  have hP := polynomial_pos ε _ hε hε' (chord_parameter_mem φ ψ)
  have hc : 0 < 4 * Real.sin ((φ - ψ) / 2) ^ 2 / normalization ε := by
    apply div_pos _ (normalization_pos ε hε)
    rw [← circle_chord_norm_sq φ ψ]
    have hp := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    positivity
  have hN :
      (4 * Real.cos ((φ - ψ) / 2) ^ 2 - 1) *
        (4 * Real.cos ((φ - ψ) / 2) ^ 2) *
        (3 - 4 * Real.cos ((φ - ψ) / 2) ^ 2) =
      chordParameter φ ψ * (chordParameter φ ψ + 1) *
        (2 - chordParameter φ ψ) := by unfold chordParameter; ring
  have hratio : |rowCorrelation frequencies (amplitudes ε) (Real.pi / 6) (φ - ψ)| /
      rowEnergy frequencies (amplitudes ε) (φ - ψ) =
      correlationQuotient ε (chordParameter φ ψ) := by
    rw [six_row_energy ε _ hε, six_row_correlation ε _ hε, hN,
      abs_mul, abs_mul, abs_of_pos hc, abs_of_pos (by positivity : 0 < ε / 2)]
    change _ = (ε / 2) *
      |chordParameter φ ψ * (chordParameter φ ψ + 1) * (2 - chordParameter φ ψ)| /
        chordPolynomial ε (chordParameter φ ψ)
    rw [mul_assoc, mul_div_mul_left _ _ hc.ne']
    rfl
  exact hratio
theorem six_actual_pointwise_rank (ε φ ψ : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 2)
    (hne : circleState φ ≠ circleState ψ) :
    matrixStableRank
      (delayMatrix frequencies (amplitudes ε) (Real.pi / 6) φ -
        delayMatrix frequencies (amplitudes ε) (Real.pi / 6) ψ) =
      2 / (1 + correlationQuotient ε (chordParameter φ ψ)) := by
  have hratio := six_correlation_ratio ε φ ψ hε hε' hne
  rw [paired_pointwise_stable_rank _ _ _ _ _ (six_energy_pos ε φ ψ hε hε' hne), hratio]
private theorem quotient_numerator_bound (ε q : ℝ) (hε : 0 < ε)
    (hq : q ∈ Icc (-1) 3) :
    (ε / 2) * |q * (q + 1) * (2 - q)| ≤ 2 * ε * |q| := by
  have hprod := mul_nonneg (sub_nonneg.mpr hq.2)
    (show 0 ≤ q + 2 by linarith [hq.1])
  have hf : |(q + 1) * (2 - q)| ≤ 4 := by
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg (q - 1 / 2)]
  calc
    _ = (ε / 2) * |q| * |(q + 1) * (2 - q)| := by
      rw [show q * (q + 1) * (2 - q) = q * ((q + 1) * (2 - q)) by ring, abs_mul]
      ring
    _ ≤ (ε / 2) * |q| * 4 :=
      mul_le_mul_of_nonneg_left hf (mul_nonneg (by positivity) (abs_nonneg _))
    _ = _ := by ring
private theorem polynomial_quadratic_bound (ε q : ℝ) (hε : 0 < ε)
    (hε' : ε ≤ 1 / 4) (hq : q ∈ Icc (-1) 3) :
    q ^ 2 / 2 + 2 * ε ≤ chordPolynomial ε q := by
  have hf : (1 / 2 : ℝ) ≤ 1 + ε * (q - 1) := by
    nlinarith [mul_nonneg hε.le (show 0 ≤ q + 1 by linarith [hq.1])]
  have h := mul_le_mul_of_nonneg_left hf (sq_nonneg q)
  unfold chordPolynomial
  linarith

theorem quotient_scaled_tail (ε q R : ℝ) (hε : 0 < ε)
    (hε' : ε ≤ 1 / 4) (hq : q ∈ Icc (-1) 3) (hR : 0 < R)
    (htail : R * Real.sqrt ε ≤ |q|) :
    correlationQuotient ε q / Real.sqrt ε ≤ 4 / R := by
  have ht : Real.sqrt ε ^ 2 = ε := Real.sq_sqrt hε.le
  have htR : R * Real.sqrt ε ^ 2 = R * ε := congrArg (fun x : ℝ => R * x) ht
  have hscale : R * ε ≤ Real.sqrt ε * |q| := by
    have h := mul_le_mul_of_nonneg_left htail (Real.sqrt_nonneg ε)
    nlinarith [htR]
  have hD := polynomial_quadratic_bound ε q hε hε' hq
  have hT : R * (2 * ε * |q|) ≤ 4 * Real.sqrt ε * chordPolynomial ε q := by
    calc
      _ = 2 * |q| * (R * ε) := by ring
      _ ≤ 2 * |q| * (Real.sqrt ε * |q|) :=
        mul_le_mul_of_nonneg_left hscale (by positivity)
      _ = 2 * Real.sqrt ε * q ^ 2 := by rw [← sq_abs q]; ring
      _ ≤ _ := by
        have h := mul_le_mul_of_nonneg_left hD (Real.sqrt_nonneg ε)
        have hpos := mul_nonneg (Real.sqrt_nonneg ε) hε.le
        nlinarith
  have hQ : correlationQuotient ε q ≤ (4 / R) * Real.sqrt ε := by
    apply (div_le_iff₀ (polynomial_pos ε q hε (by linarith) hq)).mpr
    calc
      _ ≤ 2 * ε * |q| := quotient_numerator_bound ε q hε hq
      _ ≤ (4 * Real.sqrt ε * chordPolynomial ε q) / R :=
        (le_div_iff₀ hR).mpr (by simpa only [mul_comm] using hT)
      _ = _ := by ring
  exact (div_le_iff₀ (Real.sqrt_pos.2 hε)).mpr hQ

end
end D5.S3.ConceptDynamics.ObservationTopology.HarmonicSensors.SixDimensionalSharpGeometry

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Set
open scoped Topology Matrix.Norms.L2Operator

namespace D5.S3.ConceptDynamics.ObservationTopology.HarmonicSensors.SixDimensionalSharpGeometry

open PairedDelayGeometry

noncomputable section

def actualEta (ε : ℝ) : ℝ := 2 / actualRank ε - 1
def correlationMaximum (ε : ℝ) : ℝ :=
  sSup (correlationQuotient ε '' Icc (-1) 3)
private theorem quotient_continuousAt (ε q : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 2)
    (hq : q ∈ Icc (-1) 3) : ContinuousAt (correlationQuotient ε) q := by
  have hn : ContinuousAt (fun q : ℝ => (ε / 2) * |q * (q + 1) * (2 - q)|) q := by
    fun_prop
  have hd : ContinuousAt (chordPolynomial ε) q := by
    unfold chordPolynomial
    fun_prop
  exact hn.div hd (ne_of_gt (polynomial_pos ε q hε hε' hq))
private theorem quotient_continuousOn (ε : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 2) :
    ContinuousOn (correlationQuotient ε) (Icc (-1) 3) :=
  fun q hq => (quotient_continuousAt ε q hε hε' hq).continuousWithinAt
theorem chord_parameter_explicit (q : ℝ) (hq : q ∈ Ico (-1) 3) :
    let d := 2 * Real.arccos (Real.sqrt ((q + 1) / 4))
    circleState d ≠ circleState 0 ∧ chordParameter d 0 = q := by
  let a := Real.sqrt ((q + 1) / 4)
  let v := Real.arccos a
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have ha2 : a ^ 2 = (q + 1) / 4 := Real.sq_sqrt (by linarith [hq.1])
  have ha1 : a < 1 := by nlinarith [hq.2]
  have hv0 : 0 < v := Real.arccos_pos.mpr ha1
  have hvπ : v < Real.pi := Real.arccos_lt_pi.mpr (by linarith)
  have hcos : Real.cos v = a := Real.cos_arccos (by linarith) ha1.le
  have hsin : 0 < Real.sin v := Real.sin_pos_of_pos_of_lt_pi hv0 hvπ
  change circleState (2 * v) ≠ circleState 0 ∧ chordParameter (2 * v) 0 = q
  constructor
  · intro heq
    have h := circle_chord_norm_sq (2 * v) 0
    rw [heq, sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at h
    rw [show (2 * v - 0) / 2 = v by ring] at h
    nlinarith
  · unfold chordParameter
    rw [show (2 * v - 0) / 2 = v by ring, hcos, ha2]
    ring
theorem chord_parameter_realized (q : ℝ) (hq : q ∈ Ico (-1) 3) :
    ∃ φ ψ : ℝ, circleState φ ≠ circleState ψ ∧ chordParameter φ ψ = q := by
  exact ⟨_, 0, chord_parameter_explicit q hq⟩

theorem short_chord_rank_limit (ε : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 2) :
    Tendsto (fun d : ℝ => matrixStableRank
      (delayMatrix frequencies (amplitudes ε) (Real.pi / 6) d -
        delayMatrix frequencies (amplitudes ε) (Real.pi / 6) 0))
      (𝓝[>] 0) (𝓝 (2 / (1 + correlationQuotient ε 3))) := by
  have hq : ContinuousAt (fun d : ℝ => chordParameter d 0) 0 := by
    unfold chordParameter
    fun_prop
  have hq0 : chordParameter 0 0 = 3 := by norm_num [chordParameter]
  have hQ : ContinuousAt (fun d : ℝ => correlationQuotient ε (chordParameter d 0)) 0 := by
    have houter : ContinuousAt (correlationQuotient ε) (chordParameter 0 0) := by
      rw [hq0]
      exact quotient_continuousAt ε 3 hε hε' ⟨by norm_num, le_rfl⟩
    exact houter.comp (f := fun d : ℝ => chordParameter d 0) hq
  have hQ0 : 0 ≤ correlationQuotient ε 3 := by
    exact div_nonneg (mul_nonneg (by positivity) (abs_nonneg _))
      (polynomial_pos ε 3 hε hε' ⟨by norm_num, le_rfl⟩).le
  have hc : ContinuousAt (fun d : ℝ => 2 / (1 + correlationQuotient ε (chordParameter d 0))) 0 :=
    continuousAt_const.div (continuousAt_const.add hQ) (by rw [hq0]; linarith)
  have ht := hc.tendsto.mono_left (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  simp only [hq0] at ht
  apply ht.congr'
  filter_upwards [short_states_distinct] with d hd
  exact (six_actual_pointwise_rank ε d 0 hε hε' hd).symm
theorem correlation_maximum_spec (ε : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 2) :
    ∃ q ∈ Icc (-1) 3, correlationMaximum ε = correlationQuotient ε q ∧
      ∀ p ∈ Icc (-1) 3, correlationQuotient ε p ≤ correlationMaximum ε := by
  obtain ⟨q, hq, heq, hmax⟩ := isCompact_Icc.exists_sSup_image_eq_and_ge
    (show (Icc (-1 : ℝ) 3).Nonempty from ⟨0, by constructor <;> norm_num⟩)
    (quotient_continuousOn ε hε hε')
  refine ⟨q, hq, heq, ?_⟩
  intro p hp
  change correlationQuotient ε p ≤ sSup (correlationQuotient ε '' Icc (-1) 3)
  rw [heq]
  exact hmax p hp
theorem actual_rank_eq_maximum (ε : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 2) :
    actualRank ε = 2 / (1 + correlationMaximum ε) := by
  obtain ⟨qm, hqm, hm, hmax⟩ := correlation_maximum_spec ε hε hε'
  have hnonneg (q : ℝ) (hq : q ∈ Icc (-1) 3) : 0 ≤ correlationQuotient ε q :=
    div_nonneg (mul_nonneg (by positivity) (abs_nonneg _))
      (polynomial_pos ε q hε hε' hq).le
  have hM : 0 ≤ correlationMaximum ε := by rw [hm]; exact hnonneg qm hqm
  let V := stableRankValues frequencies (amplitudes ε) (Real.pi / 6)
  have hV : V.Nonempty := ⟨_, 2 * Real.pi / 3, 0, separated_third_turn, rfl⟩
  have hlow : ∀ r ∈ V, 2 / (1 + correlationMaximum ε) ≤ r := by
    rintro r ⟨φ, ψ, hne, rfl⟩
    rw [six_actual_pointwise_rank ε φ ψ hε hε' hne]
    have hq := chord_parameter_mem φ ψ
    apply (div_le_div_iff₀ (by linarith) (by linarith [hnonneg _ hq])).mpr
    nlinarith [hmax _ hq]
  have hbd : BddBelow V := ⟨_, hlow⟩
  have hRlow : 2 / (1 + correlationMaximum ε) ≤ actualRank ε := le_csInf hV hlow
  have hpoint (q : ℝ) (hq : q ∈ Ico (-1) 3) :
      actualRank ε ≤ 2 / (1 + correlationQuotient ε q) := by
    obtain ⟨φ, ψ, hne, hparam⟩ := chord_parameter_realized q hq
    have hi := csInf_le hbd (show matrixStableRank
        (delayMatrix frequencies (amplitudes ε) (Real.pi / 6) φ -
          delayMatrix frequencies (amplitudes ε) (Real.pi / 6) ψ) ∈ V from
      ⟨φ, ψ, hne, rfl⟩)
    change actualRank ε ≤ _ at hi
    rw [six_actual_pointwise_rank ε φ ψ hε hε' hne, hparam] at hi
    exact hi
  have hend : actualRank ε ≤ 2 / (1 + correlationQuotient ε 3) := by
    apply ge_of_tendsto (short_chord_rank_limit ε hε hε')
    filter_upwards [short_states_distinct] with d hd
    exact csInf_le hbd ⟨d, 0, hd, rfl⟩
  apply le_antisymm _ hRlow
  rw [hm]
  by_cases hlt : qm < 3
  · exact hpoint qm ⟨hqm.1, hlt⟩
  · have heq : qm = 3 := le_antisymm hqm.2 (le_of_not_gt hlt)
    simpa [heq] using hend
theorem actual_eta_eq_maximum (ε : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 2) :
    actualEta ε = correlationMaximum ε := by
  obtain ⟨q, hq, hm, _⟩ := correlation_maximum_spec ε hε hε'
  have hM : 0 ≤ correlationMaximum ε := by
    rw [hm]
    exact div_nonneg (mul_nonneg (by positivity) (abs_nonneg _))
      (polynomial_pos ε q hε hε' hq).le
  unfold actualEta
  rw [actual_rank_eq_maximum ε hε hε']
  field_simp [show 1 + correlationMaximum ε ≠ 0 by linarith]
  <;> ring

end
end D5.S3.ConceptDynamics.ObservationTopology.HarmonicSensors.SixDimensionalSharpGeometry

namespace D5.S3.ConceptDynamics.ObservationTopology.HarmonicSensors.SixDimensionalSharpGeometry

noncomputable section

def scaledCorrelation (t z : ℝ) : ℝ :=
  (|z * (1 + t * z) * (2 - t * z)| / 2) /
    (z ^ 2 * (1 + t ^ 2 * (t * z - 1)) + 2)
def limitingCorrelation (z : ℝ) : ℝ := |z| / (z ^ 2 + 2)
def boundedError (t R : ℝ) : ℝ :=
  (t * R ^ 2 + t ^ 2 * R ^ 3) / 4 + R ^ 3 * t ^ 2 * (1 + t * R) / 4
private theorem scaled_eq (ε z : ℝ) (hε : 0 < ε) :
    correlationQuotient ε (Real.sqrt ε * z) / Real.sqrt ε =
      scaledCorrelation (Real.sqrt ε) z := by
  let t := Real.sqrt ε
  have ht : t ^ 2 = ε := Real.sq_sqrt hε.le
  have ht0 : 0 < t := Real.sqrt_pos.mpr hε
  have hN : (t * z) * (t * z + 1) * (2 - t * z) =
      t * (z * (1 + t * z) * (2 - t * z)) := by ring
  have hD : (t * z) ^ 2 * (1 + t ^ 2 * (t * z - 1)) + 2 * t ^ 2 =
      t ^ 2 * (z ^ 2 * (1 + t ^ 2 * (t * z - 1)) + 2) := by ring
  change correlationQuotient ε (t * z) / t = scaledCorrelation t z
  rw [congrArg (fun e : ℝ => correlationQuotient e (t * z)) ht.symm]
  unfold correlationQuotient chordPolynomial scaledCorrelation
  rw [hN, abs_mul, abs_of_pos ht0, hD]
  have hcancel : t ^ 2 * t * (t⁻¹) ^ 2 * t⁻¹ = 1 := by
    field_simp [ne_of_gt ht0]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_pow]
  calc
    _ = (t ^ 2 * t * (t⁻¹) ^ 2 * t⁻¹) *
        (|z * (1 + t * z) * (2 - t * z)| * (2 : ℝ)⁻¹ *
          (z ^ 2 * (1 + t ^ 2 * (t * z - 1)) + 2)⁻¹) := by ring
    _ = _ := by rw [hcancel]; ring
private theorem fraction_error (N n D d a b R : ℝ)
    (hD : 2 ≤ D) (hd : 2 ≤ d) (hn : 0 ≤ n) (hnR : n ≤ R)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hN : |N - n| ≤ a) (hDd : |D - d| ≤ b) :
    |N / D - n / d| ≤ a / 2 + R * b / 4 := by
  have hD0 : 0 < D := by linarith
  have hd0 : 0 < d := by linarith
  have hid : N / D - n / d = (N - n) / D + n * (d - D) / (D * d) := by
    field_simp [ne_of_gt hD0, ne_of_gt hd0]
    <;> ring
  have hDD : 4 ≤ D * d := by nlinarith
  have h1 : |(N - n) / D| ≤ a / 2 := by
    rw [abs_div, abs_of_pos hD0]
    apply (div_le_iff₀ hD0).mpr
    have h := mul_le_mul_of_nonneg_left hD (div_nonneg ha (by norm_num : (0 : ℝ) ≤ 2))
    linarith
  have h2 : |n * (d - D) / (D * d)| ≤ R * b / 4 := by
    rw [abs_div, abs_mul, abs_of_nonneg hn, abs_of_pos (mul_pos hD0 hd0), abs_sub_comm]
    have hnum : n * |D - d| ≤ R * b :=
      mul_le_mul hnR hDd (abs_nonneg _) (hn.trans hnR)
    apply (div_le_iff₀ (mul_pos hD0 hd0)).mpr
    have h := mul_le_mul_of_nonneg_left hDD
      (div_nonneg (mul_nonneg (hn.trans hnR) hb) (by norm_num : (0 : ℝ) ≤ 4))
    linarith
  rw [hid]
  exact (abs_add_le _ _).trans (add_le_add h1 h2)
theorem scaled_bounded_uniform (t R z : ℝ) (ht : 0 ≤ t) (hR : 0 ≤ R)
    (hz : |z| ≤ R) (hsmall : t * R ≤ 1) (ht2 : t ^ 2 ≤ 1 / 4) :
    |scaledCorrelation t z - limitingCorrelation z| ≤ boundedError t R := by
  have htz : |t * z| ≤ t * R := by
    rw [abs_mul, abs_of_nonneg ht]
    exact mul_le_mul_of_nonneg_left hz ht
  have htz' := abs_le.mp (htz.trans hsmall)
  have hz2 : z ^ 2 ≤ R ^ 2 := by
    have hh := (sq_le_sq₀ (abs_nonneg z) hR).mpr hz
    simpa only [sq_abs] using hh
  have hz3 : |z| * z ^ 2 ≤ R ^ 3 := by
    have h := mul_le_mul hz hz2 (sq_nonneg z) hR
    nlinarith
  have hcoef : 0 ≤ 1 + t ^ 2 * (t * z - 1) := by
    have h := mul_nonneg (sq_nonneg t) (by linarith [htz'.1] : 0 ≤ t * z + 1)
    nlinarith
  have hden : 2 ≤ z ^ 2 * (1 + t ^ 2 * (t * z - 1)) + 2 := by
    nlinarith [mul_nonneg (sq_nonneg z) hcoef]
  have hN : abs (abs (z * (1 + t * z) * (2 - t * z)) / 2 - abs z) ≤
      (t * R ^ 2 + t ^ 2 * R ^ 3) / 2 := by
    have hpoly : z * (1 + t * z) * (2 - t * z) - 2 * z =
        t * z ^ 2 - t ^ 2 * z ^ 3 := by ring
    have hdiff : abs (abs (z * (1 + t * z) * (2 - t * z)) / 2 - abs z) =
        abs (abs (z * (1 + t * z) * (2 - t * z)) - abs (2 * z)) / 2 := by
      have h2z : |(2 : ℝ) * z| = 2 * |z| := by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      rw [h2z, show |z * (1 + t * z) * (2 - t * z)| / 2 - |z| =
        (|z * (1 + t * z) * (2 - t * z)| - 2 * |z|) / 2 by ring]
      rw [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have hnum : |z * (1 + t * z) * (2 - t * z) - 2 * z| ≤
        t * R ^ 2 + t ^ 2 * R ^ 3 := by
      rw [hpoly]
      calc
        _ ≤ |t * z ^ 2| + |t ^ 2 * z ^ 3| := by
          simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (t * z ^ 2) (-(t ^ 2 * z ^ 3))
        _ = t * z ^ 2 + t ^ 2 * (|z| * z ^ 2) := by
          rw [abs_mul, abs_of_nonneg ht, abs_of_nonneg (sq_nonneg z),
            abs_mul, abs_of_nonneg (sq_nonneg t)]
          congr 1
          rw [show z ^ 3 = z * z ^ 2 by ring, abs_mul,
            abs_of_nonneg (sq_nonneg z)]
        _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hz2 ht)
          (mul_le_mul_of_nonneg_left hz3 (sq_nonneg t))
    rw [hdiff]
    exact div_le_div_of_nonneg_right
      ((abs_abs_sub_abs_le_abs_sub _ _).trans hnum) (by norm_num)
  have hDd : |(z ^ 2 * (1 + t ^ 2 * (t * z - 1)) + 2) - (z ^ 2 + 2)| ≤
      R ^ 2 * t ^ 2 * (1 + t * R) := by
    have hp : |t * z - 1| ≤ 1 + t * R := by
      calc
        _ ≤ |t * z| + |(1 : ℝ)| := by
          simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (t * z) (-(1 : ℝ))
        _ ≤ 1 + t * R := by norm_num at *; linarith
    rw [show (z ^ 2 * (1 + t ^ 2 * (t * z - 1)) + 2) - (z ^ 2 + 2) =
      (z ^ 2 * t ^ 2) * (t * z - 1) by ring,
      abs_mul, abs_of_nonneg (mul_nonneg (sq_nonneg z) (sq_nonneg t))]
    exact mul_le_mul (mul_le_mul_of_nonneg_right hz2 (sq_nonneg t)) hp
      (abs_nonneg _) (by positivity)
  have hf := fraction_error _ |z| _ (z ^ 2 + 2)
    ((t * R ^ 2 + t ^ 2 * R ^ 3) / 2)
    (R ^ 2 * t ^ 2 * (1 + t * R)) R hden (by nlinarith [sq_nonneg z])
    (abs_nonneg z) hz (by positivity) (by positivity) hN hDd
  unfold scaledCorrelation limitingCorrelation boundedError
  convert hf using 1 <;> ring
private theorem bounded_error_tendsto (R : ℝ) :
    Tendsto (fun ε : ℝ => boundedError (Real.sqrt ε) R) (𝓝[>] 0) (𝓝 0) := by
  have hc : ContinuousAt (fun ε : ℝ => boundedError (Real.sqrt ε) R) 0 := by
    unfold boundedError
    fun_prop
  simpa [boundedError] using hc.tendsto.mono_left (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
private theorem limiting_maximum_bound (z : ℝ) :
    limitingCorrelation z ≤ 1 / (2 * Real.sqrt 2) := by
  have hs : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  unfold limitingCorrelation
  apply (div_le_div_iff₀ (by nlinarith [sq_nonneg z]) (by positivity)).mpr
  nlinarith [sq_nonneg (|z| - Real.sqrt 2), sq_abs z]
private theorem limiting_witness :
    limitingCorrelation (Real.sqrt 2) = 1 / (2 * Real.sqrt 2) := by
  have hs : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  unfold limitingCorrelation
  rw [abs_of_pos hs, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  field_simp [ne_of_gt hs]
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
private theorem scaled_witness_tendsto :
    Tendsto (fun ε : ℝ => scaledCorrelation (Real.sqrt ε) (Real.sqrt 2))
      (𝓝[>] 0) (𝓝 (1 / (2 * Real.sqrt 2))) := by
  have hc : ContinuousAt (fun ε : ℝ => scaledCorrelation (Real.sqrt ε) (Real.sqrt 2)) 0 := by
    unfold scaledCorrelation
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · norm_num [Real.sq_sqrt]
  have ht := hc.tendsto.mono_left (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  have hv : scaledCorrelation 0 (Real.sqrt 2) = limitingCorrelation (Real.sqrt 2) := by
    simp [scaledCorrelation, limitingCorrelation]
  simpa only [Real.sqrt_zero, hv, limiting_witness] using ht
theorem actual_eta_scaled_limit :
    Tendsto (fun ε : ℝ => actualEta ε / Real.sqrt ε) (𝓝[>] 0)
      (𝓝 (1 / (2 * Real.sqrt 2))) := by
  have htlim : Tendsto Real.sqrt (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hc : ContinuousAt Real.sqrt 0 := by fun_prop
    simpa using hc.tendsto.mono_left (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  have he : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      0 < ε ∧ ε ≤ 1 / 4 ∧ Real.sqrt ε * 32 ≤ 1 := by
    have hu : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε < 1 / 4 :=
      (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4)).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, hu,
      htlim.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 32)] with ε hε hu ht
    exact ⟨hε, hu.le, by linarith⟩
  have hs0 : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsle : Real.sqrt (2 : ℝ) ≤ 2 := by nlinarith
  have hm0 : (1 / 4 : ℝ) ≤ 1 / (2 * Real.sqrt 2) := by
    apply (le_div_iff₀ (by positivity)).mpr
    linarith
  apply tendsto_order.mpr
  constructor
  · intro a ha
    filter_upwards [he, scaled_witness_tendsto.eventually_const_lt ha] with ε hε hw
    have ht0 : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε.1
    have hq : Real.sqrt ε * Real.sqrt 2 ∈ Icc (-1) 3 := by
      constructor
      · have hp := mul_nonneg ht0.le hs0.le
        linarith
      · have h := mul_le_mul_of_nonneg_left hsle ht0.le
        nlinarith [hε.2.2]
    obtain ⟨_, _, _, hmax⟩ := correlation_maximum_spec ε hε.1 (by linarith [hε.2.1])
    have h := div_le_div_of_nonneg_right (hmax _ hq) ht0.le
    rw [scaled_eq ε (Real.sqrt 2) hε.1] at h
    rw [actual_eta_eq_maximum ε hε.1 (by linarith [hε.2.1])]
    exact hw.trans_le h
  · intro a ha
    filter_upwards [he, (bounded_error_tendsto 32).eventually_lt_const (sub_pos.mpr ha)]
      with ε hε herr
    have ht0 : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε.1
    have ht2 : Real.sqrt ε ^ 2 = ε := Real.sq_sqrt hε.1.le
    obtain ⟨q, hq, hM, _⟩ := correlation_maximum_spec ε hε.1 (by linarith [hε.2.1])
    rw [actual_eta_eq_maximum ε hε.1 (by linarith [hε.2.1]), hM]
    let z := q / Real.sqrt ε
    have htz : Real.sqrt ε * z = q := by
      dsimp [z]
      field_simp [ne_of_gt ht0]
    have hscaled : correlationQuotient ε q / Real.sqrt ε = scaledCorrelation (Real.sqrt ε) z := by
      rw [← htz]
      exact scaled_eq ε z hε.1
    by_cases hz : |z| ≤ 32
    · have hbound := scaled_bounded_uniform (Real.sqrt ε) 32 z ht0.le (by norm_num) hz
        hε.2.2 (by rw [ht2]; exact hε.2.1)
      have hu := (abs_le.mp hbound).2
      rw [hscaled]
      have hm := limiting_maximum_bound z
      linarith
    · have htail : 32 * Real.sqrt ε ≤ |q| := by
        have hz' : 32 < |q| / Real.sqrt ε := by
          simpa only [z, abs_div, abs_of_pos ht0] using lt_of_not_ge hz
        exact ((lt_div_iff₀ ht0).mp hz').le
      have hu := quotient_scaled_tail ε q 32 hε.1 hε.2.1 hq (by norm_num) htail
      have hsmall : (4 / 32 : ℝ) < a := by linarith
      exact hu.trans_lt hsmall
end
end D5.S3.ConceptDynamics.ObservationTopology.HarmonicSensors.SixDimensionalSharpGeometry
namespace D5.S3.ConceptDynamics.ObservationTopology.HarmonicSensors.SixDimensionalSharpGeometry
open PairedDelayGeometry
noncomputable section
/-- Gain uses the original sensor and the Euclidean chord of the physical circle. -/
def chordGain (ε φ ψ : ℝ) : ℝ :=
  ‖sensor ε φ - sensor ε ψ‖ / ‖circleState φ - circleState ψ‖
/-- Every pair of distinct physical states is included, independently of its phase representatives. -/
def gainValues (ε : ℝ) : Set ℝ :=
  {r | ∃ φ ψ : ℝ, circleState φ ≠ circleState ψ ∧ r = chordGain ε φ ψ}
def lowerGain (ε : ℝ) : ℝ := sInf (gainValues ε)
def upperGain (ε : ℝ) : ℝ := sSup (gainValues ε)
/-- The scalar polynomial is proved equal to the squared physical norm ratio. -/
theorem chord_gain_sq (ε φ ψ : ℝ) (hε : 0 < ε)
    (hne : circleState φ ≠ circleState ψ) :
    chordGain ε φ ψ ^ 2 = chordPolynomial ε (chordParameter φ ψ) / normalization ε := by
  have hn : ‖circleState φ - circleState ψ‖ ≠ 0 :=
    (norm_pos_iff.mpr (sub_ne_zero.mpr hne)).ne'
  have hs : 4 * Real.sin ((φ - ψ) / 2) ^ 2 ≠ 0 := by
    rw [← circle_chord_norm_sq φ ψ]
    exact pow_ne_zero _ hn
  have hsin : Real.sin ((φ - ψ) / 2) ≠ 0 := by
    intro hz
    simp [hz] at hs
  rw [chordGain, div_pow, six_chord_norm_sq ε φ ψ hε, circle_chord_norm_sq]
  field_simp [hsin, (normalization_pos ε hε).ne']
  <;> ring
private theorem gain_lower_bound (ε φ ψ : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 2)
    (hne : circleState φ ≠ circleState ψ) :
    Real.sqrt (2 * ε / normalization ε) ≤ chordGain ε φ ψ := by
  have hn : 0 ≤ chordGain ε φ ψ := div_nonneg (norm_nonneg _) (norm_nonneg _)
  have hZ := normalization_pos ε hε
  have hsq := chord_gain_sq ε φ ψ hε hne
  have hq := chord_parameter_mem φ ψ
  have hf : 0 ≤ 1 + ε * (chordParameter φ ψ - 1) := by
    nlinarith [mul_nonneg hε.le (show 0 ≤ chordParameter φ ψ + 1 by linarith [hq.1])]
  have hl : 2 * ε ≤ chordPolynomial ε (chordParameter φ ψ) := by
    have hp := mul_nonneg (sq_nonneg (chordParameter φ ψ)) hf
    unfold chordPolynomial
    linarith
  have hl' : 2 * ε / normalization ε ≤ chordPolynomial ε (chordParameter φ ψ) /
      normalization ε := (div_le_div_iff_of_pos_right hZ).mpr hl
  have hs := Real.sq_sqrt (show 0 ≤ 2 * ε / normalization ε by positivity)
  nlinarith [Real.sqrt_nonneg (2 * ε / normalization ε)]
private theorem gain_values_nonempty (ε : ℝ) : (gainValues ε).Nonempty :=
  ⟨_, 2 * Real.pi / 3, 0, separated_third_turn, rfl⟩
private theorem lower_gain_eq_sqrt (ε : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 2) :
    lowerGain ε = Real.sqrt (2 * ε / normalization ε) := by
  have hl : ∀ r ∈ gainValues ε, Real.sqrt (2 * ε / normalization ε) ≤ r := by
    rintro r ⟨φ, ψ, hne, rfl⟩
    exact gain_lower_bound ε φ ψ hε hε' hne
  have hb : BddBelow (gainValues ε) := ⟨_, hl⟩
  obtain ⟨φ, ψ, hne, hq⟩ := chord_parameter_realized 0 (by constructor <;> norm_num)
  have hs : chordGain ε φ ψ ^ 2 = 2 * ε / normalization ε := by
    rw [chord_gain_sq ε φ ψ hε hne, hq]
    simp [chordPolynomial]
  have he : chordGain ε φ ψ = Real.sqrt (2 * ε / normalization ε) := by
    have hn : 0 ≤ chordGain ε φ ψ := div_nonneg (norm_nonneg _) (norm_nonneg _)
    rw [← hs, Real.sqrt_sq hn]
  apply le_antisymm _ (le_csInf (gain_values_nonempty ε) hl)
  change sInf (gainValues ε) ≤ _
  rw [← he]
  exact csInf_le hb ⟨φ, ψ, hne, rfl⟩
/-- The infimum over all distinct physical states is attained at a third-turn chord. -/
theorem lower_gain_sq (ε : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 2) :
    lowerGain ε ^ 2 = 2 * ε / (9 + 20 * ε) := by
  have hZ := normalization_pos ε hε
  rw [lower_gain_eq_sqrt ε hε hε']
  simpa only [normalization] using
    Real.sq_sqrt (show 0 ≤ 2 * ε / normalization ε by positivity)
private theorem positive_small : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε ∧ ε ≤ 1 / 2 := by
  have hu : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε < 1 / 2 :=
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hu] with ε hε hu
  exact ⟨hε, hu.le⟩
private theorem sqrt_parameter_limit : Tendsto Real.sqrt (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hc : ContinuousAt Real.sqrt 0 := by fun_prop
  simpa using hc.tendsto.mono_left
    (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
private theorem actual_eta_limit : Tendsto actualEta (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have ht := actual_eta_scaled_limit.mul sqrt_parameter_limit
  simp only [mul_zero] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact div_mul_cancel₀ _ (Real.sqrt_pos.mpr hε).ne'
private theorem actual_rank_defect_eq (ε : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 2) :
    2 - actualRank ε = 2 * actualEta ε / (1 + actualEta ε) := by
  obtain ⟨q, hq, hm, _⟩ := correlation_maximum_spec ε hε hε'
  have hM : 0 ≤ correlationMaximum ε := by
    rw [hm]
    exact div_nonneg (mul_nonneg (by positivity) (abs_nonneg _))
      (polynomial_pos ε q hε hε' hq).le
  rw [actual_rank_eq_maximum ε hε hε', actual_eta_eq_maximum ε hε hε']
  field_simp [show 1 + correlationMaximum ε ≠ 0 by linarith]
  <;> ring
/-- Rank defect on its original physical scale, through strictly positive epsilon. -/
theorem actual_rank_defect_scaled_limit :
    Tendsto (fun ε : ℝ => (2 - actualRank ε) / Real.sqrt (ε / 2))
      (𝓝[>] 0) (𝓝 1) := by
  have hs : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hden : Tendsto (fun ε : ℝ => 1 + actualEta ε) (𝓝[>] 0) (𝓝 1) := by
    simpa using tendsto_const_nhds.add actual_eta_limit
  have ht := (actual_eta_scaled_limit.const_mul (2 * Real.sqrt 2)).div hden
    (by norm_num : (1 : ℝ) ≠ 0)
  have hv : (2 * Real.sqrt 2) * (1 / (2 * Real.sqrt 2)) / 1 = 1 := by
    field_simp [hs.ne']
  rw [hv] at ht
  apply ht.congr'
  filter_upwards [positive_small] with ε hε
  change (2 * Real.sqrt 2) * (actualEta ε / Real.sqrt ε) / (1 + actualEta ε) =
    (2 - actualRank ε) / Real.sqrt (ε / 2)
  rw [actual_rank_defect_eq ε hε.1 hε.2, Real.sqrt_div hε.1.le]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring
/-- The physical lower gain has the square-root scale required by the defect-to-gain limit. -/
private theorem lower_gain_scaled_limit :
    Tendsto (fun ε : ℝ => lowerGain ε / Real.sqrt ε) (𝓝[>] 0)
      (𝓝 (Real.sqrt 2 / 3)) := by
  have hc : ContinuousAt (fun ε : ℝ => Real.sqrt (2 / normalization ε)) 0 := by
    apply ContinuousAt.sqrt
    apply ContinuousAt.div continuousAt_const
    · unfold normalization
      fun_prop
    · norm_num [normalization]
  have ht := hc.tendsto.mono_left
    (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  have hv : Real.sqrt (2 / normalization (0 : ℝ)) = Real.sqrt 2 / 3 := by
    norm_num [normalization, Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 2)]
  rw [hv] at ht
  apply ht.congr'
  filter_upwards [positive_small] with ε hε
  have hn : 0 ≤ lowerGain ε := by
    rw [lower_gain_eq_sqrt ε hε.1 hε.2]
    positivity
  have hs : (lowerGain ε / Real.sqrt ε) ^ 2 = 2 / normalization ε := by
    rw [div_pow, lower_gain_sq ε hε.1 hε.2, Real.sq_sqrt hε.1.le]
    change (2 * ε / normalization ε) / ε = 2 / normalization ε
    field_simp [hε.1.ne', (normalization_pos ε hε.1).ne']
  rw [← hs, Real.sqrt_sq (div_nonneg hn (Real.sqrt_nonneg ε))]
/-- The rank defect divided by the infimal physical chord gain tends to three halves. -/
theorem actual_rank_defect_lower_gain_limit :
    Tendsto (fun ε : ℝ => (2 - actualRank ε) / lowerGain ε)
      (𝓝[>] 0) (𝓝 (3 / 2)) := by
  have hs : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have ht := (actual_rank_defect_scaled_limit.div lower_gain_scaled_limit
    (by positivity : Real.sqrt (2 : ℝ) / 3 ≠ 0)).div_const (Real.sqrt 2)
  have hv : ((1 : ℝ) / (Real.sqrt 2 / 3)) / Real.sqrt 2 = 3 / 2 := by
    field_simp [hs.ne']
    nlinarith [hs2]
  rw [hv] at ht
  apply ht.congr'
  filter_upwards [positive_small] with ε hε
  change ((2 - actualRank ε) / Real.sqrt (ε / 2)) /
    (lowerGain ε / Real.sqrt ε) / Real.sqrt 2 = (2 - actualRank ε) / lowerGain ε
  rw [Real.sqrt_div hε.1.le]
  have hroot := (Real.sqrt_pos.mpr hε.1).ne'
  have hgain : lowerGain ε ≠ 0 := by
    rw [lower_gain_eq_sqrt ε hε.1 hε.2]
    exact (Real.sqrt_pos.mpr (div_pos (mul_pos (by norm_num) hε.1)
      (normalization_pos ε hε.1))).ne'
  field_simp [hroot, hs.ne', hgain]
  <;> ring
end
end D5.S3.ConceptDynamics.ObservationTopology.HarmonicSensors.SixDimensionalSharpGeometry
