/- GID: D5/S3/Observer/GoldenCoding/ZeckendorfRealThread
   generality: I
   mirror-B: D5/B/S3/Observer/GoldenCoding/ZeckendorfRealThread
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The complete Zeckendorf thread reconstructs a nonnegative real number. -/

import D5.S0.Conventions.WDigits
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

/- Library-search audit trail (2026-09-03):
   * Current-tree statement and body-shape searches found no frozen theorem for
     injectivity of all golden-power natural floors or their W encodings.
   * The generic state-thread separation theorem assumes the separation that is
     proved here and therefore is not an exact hit.
   * Pinned Mathlib and LeanSearch supplied floor bounds and golden-power
     divergence, but no exact reconstruction theorem was found. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter

namespace D5.S3.Observer.GoldenCoding.ZeckendorfRealThread

open D5.S0.Conventions

/-- The level-`N` quantization of a nonnegative real number. -/
def goldenQuantization (level : ℕ) (x : NNReal) : ℕ :=
  ⌊Real.goldenRatio ^ level * (x : ℝ)⌋₊

/-- The complete thread of canonical W encodings of the golden quantizations. -/
def zeckendorfRealThread (x : NNReal) : ℕ → WDigitString :=
  fun level => wEncoding (goldenQuantization level x)

/-- Equality of every canonical Zeckendorf thread coordinate reconstructs the
nonnegative real number. -/
theorem zeckendorf_real_thread_injective :
    Function.Injective zeckendorfRealThread := by
  have hle :
      ∀ {a b : NNReal}, zeckendorfRealThread a = zeckendorfRealThread b →
        (a : ℝ) ≤ (b : ℝ) := by
    intro a b hThread
    by_contra hNotLe
    have hba : (b : ℝ) < (a : ℝ) := lt_of_not_ge hNotLe
    have hgap : 0 < (a : ℝ) - (b : ℝ) := sub_pos.mpr hba
    have hGrowth :
        Tendsto
          (fun level : ℕ =>
            Real.goldenRatio ^ level * ((a : ℝ) - (b : ℝ)))
          atTop atTop :=
      (tendsto_pow_atTop_atTop_of_one_lt Real.one_lt_goldenRatio).atTop_mul_const hgap
    have hEventually :
        ∀ᶠ level : ℕ in atTop,
          (2 : ℝ) ≤
            Real.goldenRatio ^ level * ((a : ℝ) - (b : ℝ)) :=
      hGrowth (eventually_ge_atTop 2)
    obtain ⟨level, hLevel⟩ := hEventually.exists
    have hQuantization :
        goldenQuantization level a = goldenQuantization level b :=
      wEncoding.injective (congrFun hThread level)
    have haUpper :
        Real.goldenRatio ^ level * (a : ℝ) <
          (goldenQuantization level a : ℝ) + 1 := by
      exact Nat.lt_floor_add_one _
    have hbLower :
        (goldenQuantization level b : ℝ) ≤
          Real.goldenRatio ^ level * (b : ℝ) := by
      exact Nat.floor_le (by positivity)
    rw [hQuantization] at haUpper
    have hWidth :
        Real.goldenRatio ^ level * ((a : ℝ) - (b : ℝ)) < 1 := by
      rw [mul_sub]
      linarith
    linarith
  intro x y hThread
  apply Subtype.ext
  exact le_antisymm (hle hThread) (hle hThread.symm)

/-- The source carrier and its thread are inhabited. -/
example : zeckendorfRealThread 0 0 = wEncoding 0 := by
  simp [zeckendorfRealThread, goldenQuantization]

#print axioms goldenQuantization
#print axioms zeckendorfRealThread
#print axioms zeckendorf_real_thread_injective

end D5.S3.Observer.GoldenCoding.ZeckendorfRealThread
