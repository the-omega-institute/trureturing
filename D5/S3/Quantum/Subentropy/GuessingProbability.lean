/- GID: D5/S3/Quantum/Subentropy/GuessingProbability
   generality: G
   mirror-B: D5/B/S3/Quantum/Subentropy/GuessingProbability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Log.Basic]
   utility: none
   digest: Faithful finite-POVM guessing probability and supremum comparison bounds. -/

import D5.S3.Quantum.Foundation.FiniteStateChannel
import D5.S3.Quantum.Information.OrthogonalRecordEntropy
import D5.S3.Weil.ZetaLinear.RankTrace
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! The finite-POVM success set and its positive bounded supremum. -/

noncomputable section
set_option autoImplicit false
open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder
namespace D5.S3.Quantum.Subentropy.GuessingProbability
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel
open _root_.D5.S3.Quantum.Information.PartialTraceMutualInformation

variable {X B : Type*} [Fintype X] [Fintype B] [DecidableEq B]

/-- Probability of correctly guessing the classical label using the indicated measurement. -/
def successProbability (p : X → ℝ) (rho : X → DensityState B)
    (M : X → Matrix B B ℂ) : ℝ :=
  ∑ x, p x * (trace (M x * CStarMatrix.ofMatrix.symm (rho x).1)).re

/-- Success probabilities of all positive, identity-summing POVMs with the ensemble labels. -/
def successProbabilitySet (p : X → ℝ) (rho : X → DensityState B) : Set ℝ :=
  {a | ∃ M : X → Matrix B B ℂ,
    (∀ x, (M x).PosSemidef) ∧ ∑ x, M x = 1 ∧ a = successProbability p rho M}

/-- Optimal finite-POVM guessing probability, defined by its genuine success-probability set. -/
def pGuess (p : X → ℝ) (rho : X → DensityState B) : ℝ :=
  sSup (successProbabilitySet p rho)

/-- A measurement summing to the identity has total trace pairing one on a trace-one matrix. -/
theorem measurement_trace_sum
    (R : Matrix B B ℂ) (hR : Matrix.trace R = 1)
    (M : X → Matrix B B ℂ) (hsM : ∑ x, M x = 1) :
    ∑ x, (Matrix.trace (M x * R)).re = 1 := by
  rw [← Complex.re_sum, ← Matrix.trace_sum, ← Matrix.sum_mul, hsM, Matrix.one_mul]
  exact congrArg Complex.re hR

theorem success_bounds (p : X → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hs : ∑ x, p x = 1) (rho : X → DensityState B)
    (M : X → Matrix B B ℂ) (hM : ∀ x, (M x).PosSemidef)
    (hsM : ∑ x, M x = 1) : 0 ≤ successProbability p rho M ∧
      successProbability p rho M ≤ 1 := by
  have he (x y : X) : 0 ≤ (trace (M y * CStarMatrix.ofMatrix.symm (rho x).1)).re :=
    RHLinalg.trace_mul_nonneg_of_posSemidef (hM y) (density_posSemidef (rho x))
  have hsum (x : X) :
      ∑ y, (trace (M y * CStarMatrix.ofMatrix.symm (rho x).1)).re = 1 :=
    measurement_trace_sum _ (rho x).2.2 M hsM
  have hle (x : X) : (trace (M x * CStarMatrix.ofMatrix.symm (rho x).1)).re ≤ 1 := by
    rw [← hsum x]
    exact Finset.single_le_sum (fun y _ => he x y) (Finset.mem_univ x)
  constructor
  · exact Finset.sum_nonneg fun x _ => mul_nonneg (hp x) (he x x)
  · calc
      _ ≤ ∑ x, p x * 1 := Finset.sum_le_sum fun x _ =>
        mul_le_mul_of_nonneg_left (hle x) (hp x)
      _ = 1 := by simp [hs]

private theorem point_guess_mem (p : X → ℝ) (rho : X → DensityState B) (x : X) :
    p x ∈ successProbabilitySet p rho := by
  classical
  let M : X → Matrix B B ℂ := fun y => if y = x then 1 else 0
  refine ⟨M, ?_, ?_, ?_⟩
  · intro y
    dsimp [M]
    split_ifs
    · exact Matrix.PosSemidef.one
    · exact Matrix.PosSemidef.zero
  · simp [M]
  · have ht : (trace (CStarMatrix.ofMatrix.symm (rho x).1)).re = 1 :=
      congrArg Complex.re (rho x).2.2
    unfold successProbability
    rw [Finset.sum_eq_single x]
    · simp [M, ht]
    · intro y _ hy
      simp [M, hy]
    · simp

/-- The success set is nonempty and bounded, and its supremum is a probability strictly above zero.
The ensemble normalization itself supplies a positive-probability label. -/
theorem pGuess_bounds (p : X → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hs : ∑ x, p x = 1) (rho : X → DensityState B) :
    (successProbabilitySet p rho).Nonempty ∧ BddAbove (successProbabilitySet p rho) ∧
      0 < pGuess p rho ∧ pGuess p rho ≤ 1 ∧
      1 - pGuess p rho ≤ -Real.log (pGuess p rho) ∧
      ∀ q : ℝ, (∀ M : X → Matrix B B ℂ,
        (∀ x, (M x).PosSemidef) → ∑ x, M x = 1 →
          q ≤ 1 - successProbability p rho M) → q ≤ 1 - pGuess p rho := by
  have hex : ∃ x, 0 < p x := by
    by_contra h
    push Not at h
    have hsum := Finset.sum_nonpos (fun x (_ : x ∈ Finset.univ) => h x)
    rw [hs] at hsum
    norm_num at hsum
  obtain ⟨x, hx⟩ := hex
  have hne : (successProbabilitySet p rho).Nonempty := ⟨p x, point_guess_mem p rho x⟩
  have hu : ∀ a ∈ successProbabilitySet p rho, a ≤ 1 := by
    rintro a ⟨M, hM, hsM, rfl⟩
    exact (success_bounds p hp hs rho M hM hsM).2
  have hb : BddAbove (successProbabilitySet p rho) := ⟨1, hu⟩
  have hpos : 0 < pGuess p rho := hx.trans_le (le_csSup hb (point_guess_mem p rho x))
  have hlog := Real.log_le_sub_one_of_pos hpos
  refine ⟨hne, hb, hpos, csSup_le hne hu, by linarith, ?_⟩
  intro q hq
  have hsup : pGuess p rho ≤ 1 - q := by
    apply csSup_le hne
    rintro a ⟨M, hM, hsM, rfl⟩
    linarith [hq M hM hsM]
  linarith

end D5.S3.Quantum.Subentropy.GuessingProbability
