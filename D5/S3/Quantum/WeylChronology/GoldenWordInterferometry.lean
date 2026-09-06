/- GID: D5/S3/Quantum/WeylChronology/GoldenWordInterferometry
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:concrete-function-realization)
   anchors: []
   digest: A word and its reverse have identical displacement and an exact Magnus Ramsey phase. -/

import D5.S3.Quantum.WeylChronology.RamseyPhaseReadout
import D5.S3.Observer.GoldenChronology.GoldenMagnusParityRecovery
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Ordered displacement histories and a reference-arm readout

True/long is a real displacement a; false/short is an imaginary displacement
ib. The list head acts first, so operator multiplication reverses list order.
The existing Parikh/Magnus integer m=2P-rz is reused without a second counter.
The exact word phase is ab*m. Comparing the word with its reversal doubles
that phase to 2ab*m while cancelling their endpoint displacement difference.
This does not implement antiunitary time reversal, nor indefinite causal order.

This is a continuous representation adapter for the #5567 candidate owner.
It deliberately does not identify finite ZMod clock/shift displacement with
arbitrary real oscillator translations. Source: Fluehmann and Home, PRL
125,043602 (2020), eq. (3), gives the physical phase-setting readout;
Razian et al., arXiv:2604.06565v1, eqs. (4)-(5), gives an adjacent ancilla
phase protocol. Neither work is claimed to have used this golden-word code.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.WeylChronology.GoldenWordInterferometry

open D5.S3.Quantum.WeylChronology.SchrodingerDisplacement
open D5.S3.Quantum.WeylChronology.RamseyPhaseReadout
open D5.S3.Observer.GoldenChronology.BinaryParikhStepTwoBridge
open D5.S3.Observer.GoldenChronology.GoldenMagnusParityRecovery
open MeasureTheory

noncomputable section

/-- The actual displacement used for a letter; the time order is in `runWord`. -/
def letterAction (a b : ℝ) : Bool → (ℝ → ℂ) → (ℝ → ℂ)
  | true => displacement a 0
  | false => displacement 0 b

/-- Execute a finite chronological word, with its head acting first. -/
def runWord (a b : ℝ) : List Bool → (ℝ → ℂ) → (ℝ → ℂ)
  | [], f => f
  | letter :: tail, f => runWord a b tail (letterAction a b letter f)

private theorem center_cons_true (word : List Bool) :
    magnusCenter (true :: word) = magnusCenter word + (word.count false : ℤ) := by
  rw [magnus_center_formula, magnus_center_formula]
  simp [scatteredTrueFalseCount] <;> ring

private theorem center_cons_false (word : List Bool) :
    magnusCenter (false :: word) = magnusCenter word - (word.count true : ℤ) := by
  rw [magnus_center_formula, magnus_center_formula]
  simp [scatteredTrueFalseCount] <;> ring

private theorem phase_product (s t : ℝ) :
    Complex.exp ((s : ℂ) * Complex.I) * Complex.exp ((t : ℂ) * Complex.I) =
      Complex.exp (((s + t : ℝ) : ℂ) * Complex.I) := by
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Exact normal form of an arbitrary binary word in the concrete Weyl action. -/
theorem run_word_normal_form (a b : ℝ) (word : List Bool) (f : ℝ → ℂ) :
    runWord a b word f =
      Complex.exp ((((a * b * (magnusCenter word : ℝ)) : ℝ) : ℂ) * Complex.I) •
        displacement (a * word.count true) (b * word.count false) f := by
  induction word generalizing f with
  | nil =>
      simp [runWord, magnus_center_formula, scatteredTrueFalseCount, displacement]
  | cons letter tail ih =>
      cases letter
      · rw [runWord, letterAction, ih, displacement_comp]
        rw [smul_smul, phase_product]
        have hc : (magnusCenter (false :: tail) : ℝ) =
            (magnusCenter tail : ℝ) - (tail.count true : ℝ) := by
          exact_mod_cast center_cons_false tail
        rw [hc]
        have ht : (false :: tail).count true = tail.count true := by simp
        have hf : (false :: tail).count false = tail.count false + 1 := by simp
        rw [ht, hf]
        simp only [Nat.cast_add, Nat.cast_one, mul_zero, zero_mul, zero_sub, add_zero]
        have he : a * b * (magnusCenter tail : ℝ) + -(a * (tail.count true : ℝ) * b) =
            a * b * ((magnusCenter tail : ℝ) - (tail.count true : ℝ)) := by ring
        have hy : b * (tail.count false : ℝ) + b = b * ((tail.count false : ℝ) + 1) := by ring
        rw [he, hy]
      · rw [runWord, letterAction, ih, displacement_comp]
        rw [smul_smul, phase_product]
        have hc : (magnusCenter (true :: tail) : ℝ) =
            (magnusCenter tail : ℝ) + (tail.count false : ℝ) := by
          exact_mod_cast center_cons_true tail
        rw [hc]
        have ht : (true :: tail).count true = tail.count true + 1 := by simp
        have hf : (true :: tail).count false = tail.count false := by simp
        rw [ht, hf]
        simp only [Nat.cast_add, Nat.cast_one, mul_zero, zero_mul, sub_zero, add_zero]
        have he : a * b * (magnusCenter tail : ℝ) + b * (tail.count false : ℝ) * a =
            a * b * ((magnusCenter tail : ℝ) + (tail.count false : ℝ)) := by ring
        have hx : a * (tail.count true : ℝ) + a = a * ((tail.count true : ℝ) + 1) := by ring
        rw [he, hx]

/-- A shared endpoint displacement leaves a state-independent word/reversal phase. -/
theorem word_reverse_relative_phase (a b : ℝ) (word : List Bool) (f : ℝ → ℂ) :
    runWord a b word f =
      Complex.exp ((((2 * a * b * (magnusCenter word : ℝ)) : ℝ) : ℂ) * Complex.I) •
        runWord a b word.reverse f := by
  rw [run_word_normal_form a b word f, run_word_normal_form a b word.reverse f]
  simp only [magnus_center_reverse, Int.cast_neg, List.count_reverse]
  rw [smul_smul, phase_product]
  have he : 2 * a * b * (magnusCenter word : ℝ) +
      a * b * -(magnusCenter word : ℝ) = a * b * (magnusCenter word : ℝ) := by ring
  rw [he]

/-- Before interference, the two histories have identical pointwise intensity. -/
theorem word_reverse_intensity_blind (a b q : ℝ) (word : List Bool) (f : ℝ → ℂ) :
    Complex.normSq (runWord a b word f q) =
      Complex.normSq (runWord a b word.reverse f q) := by
  rw [word_reverse_relative_phase a b word f]
  exact phase_intensity_invisible (2 * a * b * (magnusCenter word : ℝ))
    (runWord a b word.reverse f q)

/-- The plus output of an ideal split-path interferometer. Both split/recombine
amplitudes are included, hence the factor 1/2. -/
def plusOutput (θ a b : ℝ) (word : List Bool) (f : ℝ → ℂ) : ℝ → ℂ :=
  fun q => (runWord a b word.reverse f q +
    Complex.exp (((-θ : ℝ) : ℂ) * Complex.I) * runWord a b word f q) / 2

/-- Recombination makes the previously invisible chronology phase observable. -/
theorem plus_output_factorization (θ a b : ℝ) (word : List Bool) (f : ℝ → ℂ) :
    plusOutput θ a b word f =
      plusAmplitude θ (2 * a * b * (magnusCenter word : ℝ)) •
        runWord a b word.reverse f := by
  funext q
  unfold plusOutput
  rw [word_reverse_relative_phase a b word f]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← mul_assoc, phase_product]
  have hangle : -θ + 2 * a * b * (magnusCenter word : ℝ) =
      2 * a * b * (magnusCenter word : ℝ) - θ := by ring
  rw [hangle]
  unfold plusAmplitude
  ring

/-- The detected density is a Ramsey fringe times the shared reference density. -/
theorem plus_output_intensity (θ a b q : ℝ) (word : List Bool) (f : ℝ → ℂ) :
    Complex.normSq (plusOutput θ a b word f q) =
      plusProbability θ (2 * a * b * (magnusCenter word : ℝ)) *
        Complex.normSq (runWord a b word.reverse f q) := by
  rw [plus_output_factorization]
  exact Complex.normSq_mul _ _

/-- Integrating a normalized reference arm yields the actual output probability.
The explicit normalization is of the reference wavefunction, not of the target
fringe. No assumptions about the unknown motional state's shape are used. -/
theorem normalized_output_probability (θ a b : ℝ) (word : List Bool) (f : ℝ → ℂ)
    (hnorm : (∫ q : ℝ, Complex.normSq (runWord a b word.reverse f q)) = 1) :
    (∫ q : ℝ, Complex.normSq (plusOutput θ a b word f q)) =
      (1 + Real.cos (2 * a * b * (magnusCenter word : ℝ) - θ)) / 2 := by
  simp_rw [plus_output_intensity]
  rw [integral_const_mul, hnorm, mul_one, plus_probability_formula]

/-- Endpoint compensation depends only on the two letter counts. It can
therefore be prepared without knowing the order inside the signal history. -/
def endpointCompensatedWord (a b : ℝ) (word : List Bool) (f : ℝ → ℂ) : ℝ → ℂ :=
  displacement (-(a * word.count true)) (-(b * word.count false)) (runWord a b word f)

/-- Count-only compensation returns the motional state exactly and retains
its chronology as a scalar phase. Reading that phase still requires a reference. -/
theorem endpoint_compensated_word_phase (a b : ℝ) (word : List Bool) (f : ℝ → ℂ) :
    endpointCompensatedWord a b word f =
      Complex.exp (((a * b * (magnusCenter word : ℝ) : ℝ) : ℂ) * Complex.I) • f := by
  unfold endpointCompensatedWord
  rw [run_word_normal_form, displacement_smul,
    (displacement_inverse (a * word.count true) (b * word.count false) f).1]

/-- Interfere the count-compensated signal with the unchanged input state.
Unlike reversal comparison, this reference does not replay the unknown word. -/
def compensatedPlusOutput (θ a b : ℝ) (word : List Bool) (f : ℝ → ℂ) : ℝ → ℂ :=
  fun q => (f q + Complex.exp (((-θ : ℝ) : ℂ) * Complex.I) *
    endpointCompensatedWord a b word f q) / 2

/-- The count-only reference gives phase ab*m, half the reversal-reference phase. -/
theorem compensated_plus_factorization (θ a b : ℝ) (word : List Bool) (f : ℝ → ℂ) :
    compensatedPlusOutput θ a b word f =
      plusAmplitude θ (a * b * (magnusCenter word : ℝ)) • f := by
  funext q
  unfold compensatedPlusOutput
  rw [endpoint_compensated_word_phase]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← mul_assoc, phase_product]
  have hangle : -θ + a * b * (magnusCenter word : ℝ) =
      a * b * (magnusCenter word : ℝ) - θ := by ring
  rw [hangle]
  unfold plusAmplitude
  ring

/-- Normalized input alone supplies the compensated interferometer's output
probability. No prior normalization of an evolved state is required. -/
theorem normalized_compensated_probability (θ a b : ℝ) (word : List Bool) (f : ℝ → ℂ)
    (hnorm : (∫ q : ℝ, Complex.normSq (f q)) = 1) :
    (∫ q : ℝ, Complex.normSq (compensatedPlusOutput θ a b word f q)) =
      plusProbability θ (a * b * (magnusCenter word : ℝ)) := by
  rw [compensated_plus_factorization]
  simp only [Pi.smul_apply, smul_eq_mul, Complex.normSq_mul]
  simpa only [integral_const_mul, hnorm, mul_one, plusProbability]

#print axioms run_word_normal_form
#print axioms word_reverse_relative_phase
#print axioms word_reverse_intensity_blind
#print axioms normalized_output_probability
#print axioms endpoint_compensated_word_phase
#print axioms normalized_compensated_probability

end
end D5.S3.Quantum.WeylChronology.GoldenWordInterferometry
