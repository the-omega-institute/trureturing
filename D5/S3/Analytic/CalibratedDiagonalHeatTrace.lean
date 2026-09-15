/- GID: D5/S3/Analytic/CalibratedDiagonalHeatTrace
   generality: G
   mirror-B: D5/B/S3/Analytic/CalibratedDiagonalHeatTrace
   mirror-E: none(waiver:exact-finite-matrix-spectrum)
   anchors: []
   utility: none
   digest: One noisy complete heat-trace observation excludes the actual low spectrum of a band-calibrated finite diagonal matrix. -/

import D5.S3.Analytic.CalibratedLaplaceBand
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# A calibrated heat-trace certificate for an actual matrix

The observed quantity is Matrix.trace of NormedSpace.exp, and the conclusion
uses Mathlib's spectrum. Both identifications are proved using the pinned
matrix exponential and diagonal spectrum theorems. This is a finite diagonal
matrix theorem with a supplied upper spectral-band calibration. It is not a
construction of a quantum field theory, a vacuum, or an infinite-volume limit.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Analytic.CalibratedDiagonalHeatTrace

open scoped BigOperators NNReal
open D5.S3.Analytic.CalibratedLaplaceBand

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The complete heat trace of the actual real diagonal energy matrix. -/
def diagonalHeatTrace (energy : ι → ℝ≥0) (t : ℝ) : ℝ :=
  Matrix.trace (NormedSpace.exp
    ((-t) • Matrix.diagonal (fun i => (energy i : ℝ))))

/-- The actual matrix exponential trace agrees with the finite Laplace sum. -/
theorem diagonalHeatTrace_eq (energy : ι → ℝ≥0) (t : ℝ) :
    diagonalHeatTrace energy t = ∑ i, Real.exp (-t * (energy i : ℝ)) := by
  have hdiag : (-t) • Matrix.diagonal (fun i => (energy i : ℝ)) =
      Matrix.diagonal (fun i => -t * (energy i : ℝ)) := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.diagonal, hij]
  unfold diagonalHeatTrace
  rw [hdiag, Matrix.exp_diagonal]
  simp [Matrix.trace, Pi.exp_def, ← Real.exp_eq_exp_ℝ]

/-- Each mode contributes at least 1/4 at the calibrated time; a low mode
contributes at least 1/2. A noisy upper bound below (dimension+1)/4 therefore
excludes the actual spectrum on (-infinity,r]. Full trace and band calibration
are essential hypotheses; a single arbitrary vector correlation is insufficient. -/
theorem calibrated_diagonal_spectrum_exclusion
    (energy : ι → ℝ≥0) (r : ℝ≥0) (hr : 0 < (r : ℝ))
    (hband : ∀ i, energy i ≤ 2 * r) (y δ : ℝ)
    (hnoise : |y - diagonalHeatTrace energy (halfBandTime r)| ≤ δ)
    (hcut : y + δ < ((Fintype.card ι : ℝ) + 1) / 4) :
    spectrum ℝ (Matrix.diagonal (fun i => (energy i : ℝ))) ⊆ Set.Ioi (r : ℝ) := by
  obtain ⟨ht, hfirst, hsecond⟩ := halfBandTime_spec r hr
  have hbase (i : ι) : (1 / 4 : ℝ) ≤
      Real.exp (-halfBandTime r * (energy i : ℝ)) := by
    rw [← hsecond]
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left
      (show (energy i : ℝ) ≤ ((2 * r : ℝ≥0) : ℝ) from hband i)
      (neg_nonpos.mpr ht)
  have hupper : diagonalHeatTrace energy (halfBandTime r) <
      ((Fintype.card ι : ℝ) + 1) / 4 := by
    have hlo := (abs_le.mp hnoise).1
    linarith
  intro E hE
  rw [spectrum_diagonal] at hE
  rcases hE with ⟨i, rfl⟩
  change (r : ℝ) < (energy i : ℝ)
  by_contra hnot
  have hilow : (energy i : ℝ) ≤ (r : ℝ) := le_of_not_gt hnot
  have hlower : (1 / 2 : ℝ) ≤
      Real.exp (-halfBandTime r * (energy i : ℝ)) := by
    rw [← hfirst]
    exact Real.exp_le_exp.mpr
      (mul_le_mul_of_nonpos_left hilow (neg_nonpos.mpr ht))
  have hsingle : Real.exp (-halfBandTime r * (energy i : ℝ)) - (1 / 4 : ℝ) ≤
      ∑ j, (Real.exp (-halfBandTime r * (energy j : ℝ)) - (1 / 4 : ℝ)) :=
    Finset.single_le_sum (fun j _ => sub_nonneg.mpr (hbase j)) (Finset.mem_univ i)
  have hsum : (∑ j, (Real.exp (-halfBandTime r * (energy j : ℝ)) - (1 / 4 : ℝ))) =
      diagonalHeatTrace energy (halfBandTime r) - (Fintype.card ι : ℝ) / 4 := by
    rw [diagonalHeatTrace_eq, Finset.sum_sub_distrib]
    simp [div_eq_mul_inv]
  rw [hsum] at hsingle
  linarith

#print axioms diagonalHeatTrace
#print axioms diagonalHeatTrace_eq
#print axioms calibrated_diagonal_spectrum_exclusion

end D5.S3.Analytic.CalibratedDiagonalHeatTrace
