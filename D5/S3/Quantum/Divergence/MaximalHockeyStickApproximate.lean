/- GID: D5/S3/Quantum/Divergence/MaximalHockeyStickApproximate
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/MaximalHockeyStickApproximate
   mirror-E: none(waiver:finite-matrix-proof)
   anchors: []
   utility: none
   digest: Actual finite reverse-test hockey gaps are bounded and uniformly Lipschitz on positive thresholds.
 -/

import D5.S3.Analytic.Measure.FullSupportProfileTransfer
import D5.S3.Quantum.Divergence.MaximalHockeyStickReverseTest
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Filter Matrix MeasureTheory Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator CStarAlgebra Topology
open D5.S3.Analytic.Measure.FullSupportProfileTransfer
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Divergence.MaximalHockeyStickOverlap
open D5.S3.Quantum.Divergence.MaximalHockeyStickProfile
open D5.S3.Quantum.Divergence.MaximalHockeyStickReverseTest
open D5.S3.Quantum.Divergence.MaximalHockeyStickReverseTest.ReverseTest

namespace D5.S3.Quantum.Divergence.MaximalHockeyStickApproximate

variable {n : Type*} [Fintype n] [DecidableEq n]

abbrev PositiveThreshold := {t : ℝ // 0 < t}

/-- The nonnegative-threshold gap of one actual finite reverse test. -/
def gap {A B : Matrix n n ℂ} {k : ℕ} (R : ReverseTest A B k)
    (t : PositiveThreshold) : ℝ :=
  R.hockey t - maximalHockey A B t

private theorem state_matrix_trace {A B : Matrix n n ℂ} {k : ℕ}
    (R : ReverseTest A B k) (i : Fin k) : (R.stateMatrix i).trace = 1 :=
  (R.state i).2.2

private theorem left_mass {A B : Matrix n n ℂ} {k : ℕ}
    (R : ReverseTest A B k) : A.trace.re = ∑ i, R.p i := by
  conv_lhs => rw [← R.prepares_left]
  change (∑ i, R.p i • R.stateMatrix i).trace.re = _
  simp only [Matrix.trace_sum, Matrix.trace_smul, state_matrix_trace,
    Complex.real_smul, mul_one, Complex.re_sum, Complex.ofReal_re]

private theorem right_mass {A B : Matrix n n ℂ} {k : ℕ}
    (R : ReverseTest A B k) : B.trace.re = ∑ i, R.q i := by
  conv_lhs => rw [← R.prepares_right]
  change (∑ i, R.q i • R.stateMatrix i).trace.re = _
  simp only [Matrix.trace_sum, Matrix.trace_smul, state_matrix_trace,
    Complex.real_smul, mul_one, Complex.re_sum, Complex.ofReal_re]

private theorem maximal_hockey_nonneg {A B : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ maximalHockey A B t := by
  have htB : (t • B).PosSemidef := hB.smul ht
  have hnonempty : (positiveOverlaps A (t • B)).Nonempty :=
    ⟨0, le_rfl, hA.nonneg, htB.nonneg⟩
  have hvalue : overlapValue A (t • B) ≤ A.trace.re := by
    unfold overlapValue
    apply csSup_le
    · exact hnonempty.image _
    · rintro _ ⟨X, hX, rfl⟩
      have hdiff : 0 ≤ (A - X).trace.re :=
        (Complex.nonneg_iff.mp (Matrix.le_iff.mp hX.2.1).trace_nonneg).1
      simpa only [Matrix.trace_sub, Complex.sub_re, sub_nonneg] using hdiff
  unfold maximalHockey
  linarith

private theorem hockey_le_trace {A B : Matrix n n ℂ} {k : ℕ}
    (R : ReverseTest A B k) {t : ℝ} (ht : 0 ≤ t) :
    R.hockey t ≤ A.trace.re := by
  unfold ReverseTest.hockey
  rw [left_mass R]
  apply Finset.sum_le_sum
  intro i _
  exact max_le (sub_le_self _ (mul_nonneg ht (R.q_nonneg i))) (R.p_nonneg i)

private theorem hockey_lipschitz {A B : Matrix n n ℂ} {k : ℕ}
    (R : ReverseTest A B k) (s t : ℝ) :
    |R.hockey t - R.hockey s| ≤ |t - s| * B.trace.re := by
  have hterm (i : Fin k) :
      |max (R.p i - t * R.q i) 0 - max (R.p i - s * R.q i) 0| ≤
        |t - s| * R.q i := by
    calc
      _ ≤ |(R.p i - t * R.q i) - (R.p i - s * R.q i)| :=
        abs_max_sub_max_le_abs _ _ _
      _ = |t - s| * R.q i := by
        rw [show (R.p i - t * R.q i) - (R.p i - s * R.q i) = (s - t) * R.q i by ring,
          abs_mul, abs_of_nonneg (R.q_nonneg i), abs_sub_comm]
  calc
    |R.hockey t - R.hockey s| ≤
        ∑ i, |max (R.p i - t * R.q i) 0 - max (R.p i - s * R.q i) 0| := by
      unfold ReverseTest.hockey
      rw [← Finset.sum_sub_distrib]
      simpa using
        (Finset.abs_sum_le_sum_abs
          (fun i : Fin k => max (R.p i - t * R.q i) 0 - max (R.p i - s * R.q i) 0)
          Finset.univ)
    _ ≤ ∑ i, (|t - s| * R.q i) := Finset.sum_le_sum (fun i _ => hterm i)
    _ = |t - s| * B.trace.re := by
      rw [← Finset.mul_sum, right_mass R]

private theorem gap_lipschitz_bound {A B : Matrix n n ℂ} {k : ℕ}
    (R : ReverseTest A B k) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (s t : PositiveThreshold) :
    |gap R t - gap R s| ≤ (2 * B.trace.re) * dist t s := by
  have hq : 0 ≤ B.trace.re := (Complex.nonneg_iff.mp hB.trace_nonneg).1
  have hR : |R.hockey t - R.hockey s| ≤ |(t : ℝ) - s| * B.trace.re :=
    hockey_lipschitz R _ _
  have hO := overlap_lipschitz A B hA hB (t : ℝ) (s : ℝ) t.2.le s.2.le
  have hO' :
      |maximalHockey A B (t : ℝ) - maximalHockey A B (s : ℝ)| ≤
        |(t : ℝ) - s| * B.trace.re := by
    calc
      _ = |overlapValue A ((s : ℝ) • B) - overlapValue A ((t : ℝ) • B)| := by
        unfold maximalHockey
        congr 1 <;> ring
      _ = |overlapValue A ((t : ℝ) • B) - overlapValue A ((s : ℝ) • B)| :=
        abs_sub_comm _ _
      _ ≤ _ := by simpa only [abs_sub_comm] using hO
  calc
    |gap R t - gap R s| =
        |(R.hockey (t : ℝ) - R.hockey (s : ℝ)) -
          (maximalHockey A B (t : ℝ) - maximalHockey A B (s : ℝ))| := by
      unfold gap
      congr 1 <;> ring
    _ ≤ |R.hockey (t : ℝ) - R.hockey (s : ℝ)| +
        |maximalHockey A B (t : ℝ) - maximalHockey A B (s : ℝ)| :=
      by simpa only [sub_eq_add_neg, abs_neg] using
        (abs_add_le (R.hockey (t : ℝ) - R.hockey (s : ℝ))
          (-(maximalHockey A B (t : ℝ) - maximalHockey A B (s : ℝ))))
    _ ≤ 2 * (|(t : ℝ) - s| * B.trace.re) := by
      simpa only [two_mul] using add_le_add hR hO'
    _ = (2 * B.trace.re) * dist t s := by
      change 2 * (|(t : ℝ) - (s : ℝ)| * B.trace.re) =
        (2 * B.trace.re) * |(t : ℝ) - (s : ℝ)|
      ring

/-!
The actual finite test supplies every hypothesis of the abstract transfer
except the vanishing curvature integral.  The latter is intentionally an
explicit input: this module does not smuggle in the scalar Stieltjes identity
or finite-cost approximation.
-/
theorem actual_gap_profile_data {A B : Matrix n n ℂ} {k : ℕ}
    (R : ReverseTest A B k) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (∀ t : PositiveThreshold, 0 ≤ gap R t ∧ gap R t ≤ A.trace.re) ∧
      LipschitzWith (Real.toNNReal (2 * B.trace.re)) (gap R) := by
  have hAtr : 0 ≤ A.trace.re := (Complex.nonneg_iff.mp hA.trace_nonneg).1
  have hBtr : 0 ≤ B.trace.re := (Complex.nonneg_iff.mp hB.trace_nonneg).1
  have hgap_nonneg (t : PositiveThreshold) : 0 ≤ gap R t := by
    exact sub_nonneg.mpr (R.maximal_hockey_le t t.2.le)
  have hgap_le (t : PositiveThreshold) : gap R t ≤ A.trace.re := by
    have hmax := maximal_hockey_nonneg hA hB t.2.le
    exact (sub_le_iff_le_add).2 (by
      have hh := hockey_le_trace R t.2.le
      linarith)
  refine ⟨fun t => ⟨hgap_nonneg t, hgap_le t⟩, ?_⟩
  apply LipschitzWith.of_dist_le_mul
  intro s t
  have h := gap_lipschitz_bound R hA hB s t
  simpa only [Real.dist_eq, Real.coe_toNNReal', max_eq_left (by positivity : 0 ≤ 2 * B.trace.re),
    abs_sub_comm, dist_comm] using h

/--
An arbitrary sequence of actual finite reverse tests can be fed directly to
the analytic transfer.  The only analytic input left to a consuming theorem
is the vanishing integral against the full-support curvature measure; no
optimizer or scalar Stieltjes representation is hidden here.
-/
theorem actual_tests_full_support_transfer
    {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (μ ν : Measure PositiveThreshold)
    [μ.IsOpenPosMeasure] [IsLocallyFiniteMeasure μ]
    (tests : ∀ j : ℕ, Σ k : ℕ, ReverseTest A B k)
    (g : ℕ → PositiveThreshold → ℝ)
    (hgap : ∀ j t, g j t = gap (tests j).2 t)
    (hint : ∀ j, Integrable (g j) μ)
    (hμlim : Tendsto (fun j => ∫ t, g j t ∂μ) atTop (𝓝 0))
    (hνfin : ν Set.univ < ⊤) :
    (∀ t, Tendsto (fun j => g j t) atTop (𝓝 0)) ∧
      Tendsto (fun j => ∫ t, g j t ∂ν) atTop (𝓝 0) := by
  have hAtr : 0 ≤ A.trace.re := (Complex.nonneg_iff.mp hA.trace_nonneg).1
  have hBtr : 0 ≤ B.trace.re := (Complex.nonneg_iff.mp hB.trace_nonneg).1
  apply tendsto_zero_of_full_support_integral μ ν A.trace.re (2 * B.trace.re)
    hAtr (by linarith)
  · intro j
    have heq : g j = gap (tests j).2 := funext (hgap j)
    rw [heq]
    exact (actual_gap_profile_data (tests j).2 hA hB).2.continuous
  · intro j t
    rw [hgap j]
    exact (actual_gap_profile_data (tests j).2 hA hB).1 t |>.1
  · intro j t
    rw [hgap j]
    exact (actual_gap_profile_data (tests j).2 hA hB).1 t |>.2
  · intro j
    have heq : g j = gap (tests j).2 := funext (hgap j)
    rw [heq]
    exact (actual_gap_profile_data (tests j).2 hA hB).2
  · exact hint
  · exact hμlim
  · exact hνfin

end D5.S3.Quantum.Divergence.MaximalHockeyStickApproximate
