/- GID: D5/S3/Weil/GoldenCriticalSpectrum/GoldenShellMomentBounds
   generality: I
   mirror-B: D5/B/S3/Weil/GoldenCriticalSpectrum/GoldenShellMomentBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Golden shell membership gives two-sided bounds for nonnegative transverse moments. -/

import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
The golden shell scale is `omega n = (1 / 2) * phi ^ (-2 * n)`.  Shell charges
are arbitrary nonnegative extended-real multiplicities, so the moment bounds
remain meaningful without a finiteness or convergence assumption.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.GoldenCriticalSpectrum.GoldenShellMomentBounds

open scoped ENNReal

/-- The ratio `phi ^ (-2)` between consecutive golden shells. -/
def goldenShellStep : ℝ≥0∞ :=
  (ENNReal.ofReal Real.goldenRatio)⁻¹ ^ 2

/-- The golden shell scale `omega n = (1 / 2) * phi ^ (-2 * n)`. -/
def goldenShellScale (n : ℕ) : ℝ≥0∞ :=
  (2 : ℝ≥0∞)⁻¹ * goldenShellStep ^ n

/-- Total multiplicity assigned to a golden shell. -/
def goldenShellCharge {I : Type*} (shell : I → ℕ) (multiplicity : I → ℝ≥0∞)
    (n : ℕ) : ℝ≥0∞ :=
  ∑' i : shell ⁻¹' {n}, multiplicity i

/-- Moment reconstructed by replacing every defect with its containing shell scale. -/
def goldenTranscriptMoment {I : Type*} (shell : I → ℕ) (multiplicity : I → ℝ≥0∞)
    (s : ℝ) : ℝ≥0∞ :=
  ∑' i, multiplicity i * goldenShellScale (shell i) ^ s

/-- Moment of the actual transverse defects. -/
def transverseDefectMoment {I : Type*} (multiplicity defect : I → ℝ≥0∞)
    (s : ℝ) : ℝ≥0∞ :=
  ∑' i, multiplicity i * defect i ^ s

/-- The golden shell ratio is strictly between zero and one. -/
theorem golden_shell_step_pos :
    0 < goldenShellStep := by
  unfold goldenShellStep
  exact ENNReal.pow_pos (ENNReal.inv_pos.mpr ENNReal.ofReal_ne_top) _

theorem golden_shell_step_lt_one :
    goldenShellStep < 1 := by
  have hPhi : (1 : ℝ≥0∞) < ENNReal.ofReal Real.goldenRatio := by
    rw [← ENNReal.ofReal_one, ENNReal.ofReal_lt_ofReal_iff Real.goldenRatio_pos]
    exact Real.one_lt_goldenRatio
  exact pow_lt_one₀ zero_le (ENNReal.inv_lt_one.mpr hPhi) (by norm_num)

/-- Consecutive shell scales differ by exactly one golden step. -/
theorem golden_shell_scale_succ (n : ℕ) :
    goldenShellScale (n + 1) = goldenShellStep * goldenShellScale n := by
  simp only [goldenShellScale, pow_succ]
  ac_rfl

/-- Grouping the transcript by shell recovers the shell-charge formula. -/
theorem golden_transcript_moment_eq_shell_sum {I : Type*} (shell : I → ℕ)
    (multiplicity : I → ℝ≥0∞) (s : ℝ) :
    goldenTranscriptMoment shell multiplicity s =
      ∑' n, goldenShellCharge shell multiplicity n * goldenShellScale n ^ s := by
  unfold goldenTranscriptMoment goldenShellCharge
  rw [← ENNReal.tsum_fiberwise
    (fun i ↦ multiplicity i * goldenShellScale (shell i) ^ s) shell]
  apply tsum_congr
  intro n
  rw [← ENNReal.tsum_mul_right]
  apply tsum_congr
  intro i
  have hiMem : shell i ∈ ({n} : Set ℕ) := i.property
  have hi : shell i = n := Set.mem_singleton_iff.mp hiMem
  rw [hi]

/-- Golden shell membership gives the two-sided transverse moment estimate. -/
theorem golden_shell_moment_bounds {I : Type*} (shell : I → ℕ)
    (multiplicity defect : I → ℝ≥0∞) (s : ℝ) (hs : 0 ≤ s)
    (hShell : ∀ i, goldenShellScale (shell i + 1) < defect i ∧
      defect i ≤ goldenShellScale (shell i)) :
    goldenShellStep ^ s * goldenTranscriptMoment shell multiplicity s ≤
        transverseDefectMoment multiplicity defect s ∧
      transverseDefectMoment multiplicity defect s ≤
        goldenTranscriptMoment shell multiplicity s := by
  unfold goldenTranscriptMoment transverseDefectMoment
  constructor
  · rw [← ENNReal.tsum_mul_left]
    apply ENNReal.tsum_le_tsum
    intro i
    calc
      goldenShellStep ^ s *
          (multiplicity i * goldenShellScale (shell i) ^ s) =
          multiplicity i * (goldenShellStep * goldenShellScale (shell i)) ^ s := by
            rw [ENNReal.mul_rpow_of_nonneg _ _ hs]
            ac_rfl
      _ = multiplicity i * goldenShellScale (shell i + 1) ^ s := by
        rw [golden_shell_scale_succ]
      _ ≤ multiplicity i * defect i ^ s :=
        mul_le_mul_right (ENNReal.rpow_le_rpow (hShell i).1.le hs) _
  · apply ENNReal.tsum_le_tsum
    intro i
    exact mul_le_mul_right (ENNReal.rpow_le_rpow (hShell i).2 hs) _

/-- A singleton in shell zero realizes both moments as the concrete value `1 / 4`. -/
theorem golden_shell_moment_valid_witness :
    let shell : Fin 1 → ℕ := fun _ ↦ 0
    let multiplicity : Fin 1 → ℝ≥0∞ := fun _ ↦ 1
    let defect : Fin 1 → ℝ≥0∞ := fun _ ↦ (2 : ℝ≥0∞)⁻¹
    (∀ i, goldenShellScale (shell i + 1) < defect i ∧
        defect i ≤ goldenShellScale (shell i)) ∧
      goldenTranscriptMoment shell multiplicity 2 = (4 : ℝ≥0∞)⁻¹ ∧
      transverseDefectMoment multiplicity defect 2 = (4 : ℝ≥0∞)⁻¹ := by
  dsimp
  constructor
  · intro i
    fin_cases i
    constructor
    · rw [golden_shell_scale_succ]
      simpa [goldenShellScale] using ENNReal.mul_lt_mul_left
        (a := (2 : ℝ≥0∞)⁻¹) (by norm_num) (by norm_num) golden_shell_step_lt_one
    · simp [goldenShellScale]
  · simp [goldenTranscriptMoment, transverseDefectMoment, goldenShellScale,
      ENNReal.rpow_two]
    rw [← ENNReal.inv_pow]
    norm_num

/-- Moving the singleton defect outside shell zero makes the upper bound numerically false. -/
theorem golden_shell_moment_outside_shell_witness :
    let shell : Fin 1 → ℕ := fun _ ↦ 0
    let multiplicity : Fin 1 → ℝ≥0∞ := fun _ ↦ 1
    let defect : Fin 1 → ℝ≥0∞ := fun _ ↦ 2
    ¬(∀ i, goldenShellScale (shell i + 1) < defect i ∧
        defect i ≤ goldenShellScale (shell i)) ∧
      goldenTranscriptMoment shell multiplicity 1 = (2 : ℝ≥0∞)⁻¹ ∧
      transverseDefectMoment multiplicity defect 1 = 2 ∧
      ¬ transverseDefectMoment multiplicity defect 1 ≤
        goldenTranscriptMoment shell multiplicity 1 := by
  dsimp
  simp [goldenTranscriptMoment, transverseDefectMoment, goldenShellScale]

#print axioms golden_shell_step_pos
#print axioms golden_shell_step_lt_one
#print axioms golden_shell_scale_succ
#print axioms golden_transcript_moment_eq_shell_sum
#print axioms golden_shell_moment_bounds
#print axioms golden_shell_moment_valid_witness
#print axioms golden_shell_moment_outside_shell_witness

end D5.S3.Weil.GoldenCriticalSpectrum.GoldenShellMomentBounds
