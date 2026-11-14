/- GID: D5/S3/Quantum/Divergence/MaximalHockeyStickProfile
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/MaximalHockeyStickProfile
   mirror-E: none(waiver:finite-matrix-proof)
   anchors: []
   utility: none
   digest: Exact trace bounds and Lipschitz continuity of the maximal overlap profile. -/

import D5.S3.Quantum.Divergence.MaximalHockeyStickOverlap
import Mathlib.Tactic

/-! Scaling actual positive-overlap maximizers controls every threshold increment. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open D5.S3.Quantum.Divergence.MaximalHockeyStickOverlap

namespace D5.S3.Quantum.Divergence.MaximalHockeyStickProfile

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem trace_mono {X Y : Matrix n n ℂ} (hXY : X ≤ Y) :
    X.trace.re ≤ Y.trace.re := by
  have h := (Complex.nonneg_iff.mp (Matrix.le_iff.mp hXY).trace_nonneg).1
  simpa only [Matrix.trace_sub, Complex.sub_re, sub_nonneg] using h

/-- Every actual feasible overlap is bounded by the trace supremum. -/
theorem feasible_le_value {A B X : Matrix n n ℂ}
    (hX : X ∈ positiveOverlaps A B) : X.trace.re ≤ overlapValue A B := by
  apply le_csSup
  · refine ⟨A.trace.re, ?_⟩
    rintro _ ⟨Y, hY, rfl⟩
    exact trace_mono hY.2.1
  · exact ⟨X, hX, rfl⟩

private theorem value_le_right (A B : Matrix n n ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) : overlapValue A B ≤ B.trace.re := by
  obtain ⟨X, hX, he⟩ := overlap_attained A B hA hB
  rw [← he]
  exact trace_mono hX.2.2

/-- For `0 ≤ s ≤ t`, increasing the threshold increases the overlap by at
most `(t-s) Tr B`. The optimizer at `t` supplies the feasible scaled point
at `s`; no differentiability or fixed rank of an optimizer is assumed. -/
theorem overlap_increment (A B : Matrix n n ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
    0 ≤ overlapValue A (t • B) - overlapValue A (s • B) ∧
      overlapValue A (t • B) - overlapValue A (s • B) ≤ (t - s) * B.trace.re := by
  have ht : 0 ≤ t := hs.trans hst
  have hsB : (s • B).PosSemidef := hB.smul hs
  have htB : (t • B).PosSemidef := hB.smul ht
  have hmono : overlapValue A (s • B) ≤ overlapValue A (t • B) := by
    obtain ⟨X, hX, he⟩ := overlap_attained A (s • B) hA hsB
    rw [← he]
    apply feasible_le_value
    exact ⟨hX.1, hX.2.1,
      hX.2.2.trans (smul_le_smul_of_nonneg_right hst hB.nonneg)⟩
  refine ⟨sub_nonneg.mpr hmono, ?_⟩
  by_cases ht0 : t = 0
  · have hs0 : s = 0 := le_antisymm (ht0 ▸ hst) hs
    simp only [ht0, hs0, sub_self, zero_mul, le_refl]
  have htp : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
  let c := s / t
  have hc : 0 ≤ c := div_nonneg hs ht
  have hc1 : c ≤ 1 := (div_le_one htp).mpr hst
  obtain ⟨X, hX, he⟩ := overlap_attained A (t • B) hA htB
  have hscaled : c * overlapValue A (t • B) ≤ overlapValue A (s • B) := by
    have hfeas : c • X ∈ positiveOverlaps A (s • B) := by
      refine ⟨smul_nonneg hc hX.1, ?_, ?_⟩
      · calc
          c • X ≤ (1 : ℝ) • X := smul_le_smul_of_nonneg_right hc1 hX.1
          _ = X := one_smul ℝ X
          _ ≤ A := hX.2.1
      · calc
          c • X ≤ c • (t • B) := smul_le_smul_of_nonneg_left hX.2.2 hc
          _ = s • B := by rw [smul_smul]; dsimp [c]; field_simp
    have hv := feasible_le_value hfeas
    simpa only [Matrix.trace_smul, Complex.real_smul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, he] using hv
  have hupper : overlapValue A (t • B) ≤ t * B.trace.re := by
    simpa only [Matrix.trace_smul, Complex.real_smul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using
      value_le_right A (t • B) hA htB
  calc
    _ ≤ (1 - c) * overlapValue A (t • B) := by nlinarith
    _ ≤ (1 - c) * (t * B.trace.re) :=
      mul_le_mul_of_nonneg_left hupper (sub_nonneg.mpr hc1)
    _ = (t - s) * B.trace.re := by dsimp [c]; field_simp

/-- A global Lipschitz estimate for the actual PSD-overlap profile on
nonnegative thresholds. It includes changes of the optimizer's rank. -/
theorem overlap_lipschitz (A B : Matrix n n ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef)
    (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    |overlapValue A (t • B) - overlapValue A (s • B)| ≤ |t - s| * B.trace.re := by
  rcases le_total s t with hst | hts
  · obtain ⟨hlo, hhi⟩ := overlap_increment A B hA hB s t hs hst
    simpa only [abs_of_nonneg hlo, abs_of_nonneg (sub_nonneg.mpr hst)] using hhi
  · obtain ⟨hlo, hhi⟩ := overlap_increment A B hA hB t s ht hts
    rw [abs_sub_comm (overlapValue A (t • B)), abs_sub_comm t]
    simpa only [abs_of_nonneg hlo, abs_of_nonneg (sub_nonneg.mpr hts)] using hhi

end D5.S3.Quantum.Divergence.MaximalHockeyStickProfile
