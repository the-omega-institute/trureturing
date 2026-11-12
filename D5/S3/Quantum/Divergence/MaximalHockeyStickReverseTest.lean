/- GID: D5/S3/Quantum/Divergence/MaximalHockeyStickReverseTest
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/MaximalHockeyStickReverseTest
   mirror-E: none(waiver:finite-matrix-proof)
   anchors: []
   utility: none
   digest: Actual finite CPTP reverse preparations and their feasible hockey overlaps. -/

import D5.S3.Quantum.Foundation.FinitePreparationChannel
import D5.S3.Quantum.Divergence.MaximalHockeyStickProfile
import D5.S3.Quantum.Divergence.MaximalHockeyStickQuadratic
import Mathlib.Data.EReal.Basic
import Mathlib.Tactic

/-! Finite reverse tests use actual density matrices and arbitrary finite alphabets. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator CStarAlgebra
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FinitePreparationChannel
open D5.S3.Quantum.Divergence.MaximalHockeyStickOverlap
open D5.S3.Quantum.Divergence.MaximalHockeyStickProfile
open D5.S3.Quantum.Divergence.MaximalHockeyStickQuadratic

namespace D5.S3.Quantum.Divergence.MaximalHockeyStickReverseTest

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A finite reverse preparation, with no trace-one requirement on its two
classical inputs. Every label prepares an existing `DensityState`. -/
structure ReverseTest (A B : Matrix n n ℂ) (k : ℕ) where
  p : Fin k → ℝ
  q : Fin k → ℝ
  p_nonneg : ∀ i, 0 ≤ p i
  q_nonneg : ∀ i, 0 ≤ q i
  state : Fin k → DensityState n
  prepares_left : ∑ i, p i • CStarMatrix.ofMatrix.symm (state i).1 = A
  prepares_right : ∑ i, q i • CStarMatrix.ofMatrix.symm (state i).1 = B

namespace ReverseTest

variable {A B : Matrix n n ℂ} {k : ℕ} (R : ReverseTest A B k)

/-- The output matrix of one preparation label. -/
def stateMatrix (i : Fin k) : Matrix n n ℂ := CStarMatrix.ofMatrix.symm (R.state i).1

private theorem state_pos (i : Fin k) : (R.stateMatrix i).PosSemidef := by
  exact (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm (R.state i).2.1).posSemidef

private theorem state_trace (i : Fin k) : (R.stateMatrix i).trace = 1 := (R.state i).2.2

/-- This finite test is realized by a CPTP map on the whole input algebra. -/
theorem cptp_realization : ∃ channel : QuantumChannel (Fin k) n,
    CStarMatrix.ofMatrix.symm
      (channel.toCompletelyPositiveMap (CStarMatrix.ofMatrix (diagonal (fun i => (R.p i : ℂ))))) = A ∧
    CStarMatrix.ofMatrix.symm
      (channel.toCompletelyPositiveMap (CStarMatrix.ofMatrix (diagonal (fun i => (R.q i : ℂ))))) = B := by
  obtain ⟨channel, hchannel⟩ := finite_preparation_quantum_channel R.state
  refine ⟨channel, ?_, ?_⟩
  · rw [hchannel]
    convert R.prepares_left using 1
    ext a b
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.diagonal_apply_eq,
      smul_eq_mul, Complex.real_smul]
  · rw [hchannel]
    convert R.prepares_right using 1
    ext a b
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.diagonal_apply_eq,
      smul_eq_mul, Complex.real_smul]

/-- The classical overlap prepared by the same CPTP test. -/
def preparedOverlap (t : ℝ) : Matrix n n ℂ :=
  ∑ i, min (R.p i) (t * R.q i) • R.stateMatrix i

/-- Positive-orientation classical hockey profile of the actual test. -/
def hockey (t : ℝ) : ℝ := ∑ i, max (R.p i - t * R.q i) 0

/-- The classical overlap is an actual quantum-feasible overlap. -/
theorem overlap_feasible (t : ℝ) (ht : 0 ≤ t) :
    R.preparedOverlap t ∈ positiveOverlaps A (t • B) := by
  have h0 : (R.preparedOverlap t).PosSemidef := by
    apply Matrix.posSemidef_sum
    intro i _
    exact (R.state_pos i).smul (le_min (R.p_nonneg i) (mul_nonneg ht (R.q_nonneg i)))
  have hleft : A - R.preparedOverlap t =
      ∑ i, (R.p i - min (R.p i) (t * R.q i)) • R.stateMatrix i := by
    conv_lhs => arg 1; rw [← R.prepares_left]
    simp only [preparedOverlap, sub_smul, Finset.sum_sub_distrib, stateMatrix]
  have hright : t • B - R.preparedOverlap t =
      ∑ i, (t * R.q i - min (R.p i) (t * R.q i)) • R.stateMatrix i := by
    conv_lhs => arg 1; rw [← R.prepares_right]
    simp only [preparedOverlap, sub_smul, Finset.sum_sub_distrib, Finset.smul_sum,
      mul_smul, stateMatrix]
  refine ⟨h0.nonneg, Matrix.le_iff.mpr ?_, Matrix.le_iff.mpr ?_⟩
  · rw [hleft]
    apply Matrix.posSemidef_sum
    intro i _
    exact (R.state_pos i).smul (sub_nonneg.mpr (min_le_left _ _))
  · rw [hright]
    apply Matrix.posSemidef_sum
    intro i _
    exact (R.state_pos i).smul (sub_nonneg.mpr (min_le_right _ _))

private theorem trace_prepared_left : A.trace.re = ∑ i, R.p i := by
  conv_lhs => rw [← R.prepares_left]
  change (∑ i, R.p i • R.stateMatrix i).trace.re = _
  simp only [Matrix.trace_sum, Matrix.trace_smul, R.state_trace,
    Complex.real_smul, mul_one, Complex.re_sum, Complex.ofReal_re]

private theorem trace_prepared_overlap (t : ℝ) :
    (R.preparedOverlap t).trace.re = ∑ i, min (R.p i) (t * R.q i) := by
  simp only [preparedOverlap, Matrix.trace_sum, Matrix.trace_smul,
    R.state_trace, Complex.real_smul, mul_one, Complex.re_sum, Complex.ofReal_re]

/-- The test profile dominates the actual maximal hockey profile at every
nonnegative threshold, including singular quantum supports. -/
theorem maximal_hockey_le (t : ℝ) (ht : 0 ≤ t) : maximalHockey A B t ≤ R.hockey t := by
  have hle := feasible_le_value (R.overlap_feasible t ht)
  have he : R.hockey t = A.trace.re - (R.preparedOverlap t).trace.re := by
    change (∑ i, max (R.p i - t * R.q i) 0) = _
    rw [R.trace_prepared_left, R.trace_prepared_overlap, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rcases le_total (R.p i) (t * R.q i) with h | h
    · rw [min_eq_left h, sub_self, max_eq_right (sub_nonpos.mpr h)]
    · rw [min_eq_right h, max_eq_left (sub_nonneg.mpr h)]
  rw [he]
  exact sub_le_sub_left hle _

/-- The actual scalar perspective cost for the fixed quadratic generator. -/
def starCost : ℝ := ∑ i, starPerspective (R.p i) (R.q i)

end ReverseTest

/-- Infimum over every finite alphabet and every actual reverse preparation
for the fixed quadratic generator. Values lie in the extended real line. -/
def maximalQuadratic (A B : Matrix n n ℂ) : EReal :=
  sInf {z : EReal | ∃ k : ℕ, ∃ R : ReverseTest A B k, z = (R.starCost : EReal)}

/-- Every actual finite preparation supplies the defining infimum upper bound. -/
theorem maximal_quadratic_le_test {A B : Matrix n n ℂ} {k : ℕ}
    (R : ReverseTest A B k) : maximalQuadratic A B ≤ (R.starCost : EReal) := by
  exact sInf_le ⟨k, R, rfl⟩

end D5.S3.Quantum.Divergence.MaximalHockeyStickReverseTest
