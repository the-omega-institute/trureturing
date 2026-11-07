/- GID: D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Independent-coordinate phase character cancellation for the noisy-GHZ finite witness.

   This module records the finite phase identity needed by the full matrix
   ensemble.  The character is indexed by the whole phase vector
   `(Fin d → ZMod 3)`, so equal scalar differences are never used to identify
   distinct ordered pairs.
-/

import Mathlib.Analysis.Fourier.ZMod
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.Tactic

open scoped BigOperators

namespace D5.S3.Quantum.Entanglement.Witness.NoisyGhzExactRoof

noncomputable section

/-! The phase character associated with a coefficient vector. -/

def phaseCharacter {d : ℕ} (v θ : Fin d → ZMod 3) : ℂ :=
  ZMod.stdAddChar (∑ j, v j * θ j)

private lemma phaseCharacter_prod {d : ℕ} (v θ : Fin d → ZMod 3) :
    phaseCharacter v θ = ∏ j, ZMod.stdAddChar (v j * θ j) := by
  unfold phaseCharacter
  exact congrArg Additive.toMul
      (map_sum ZMod.stdAddChar.toAddMonoidHom (fun j : Fin d => v j * θ j) Finset.univ) |>.trans
    (toMul_sum _ _)

/-- Averaging an arbitrary coefficient character over all independent phases.

The zero coefficient vector is the only surviving mode.  This is the
coordinate-wise orthogonality statement used for the phase part of the full
finite noisy-GHZ matrix ensemble.
-/
theorem phaseCharacter_sum {d : ℕ} (v : Fin d → ZMod 3) :
    (∑ θ : Fin d → ZMod 3, phaseCharacter v θ) =
      if v = 0 then (3 ^ d : ℕ) else 0 := by
  classical
  simp_rw [phaseCharacter_prod]
  rw [← Fintype.prod_sum (fun j (a : ZMod 3) => ZMod.stdAddChar (v j * a))]
  have hs (j : Fin d) :
      (∑ a : ZMod 3, ZMod.stdAddChar (v j * a)) =
        if v j = 0 then (3 : ℂ) else 0 := by
    simpa [ZMod.card, mul_comm] using
      (AddChar.sum_mulShift (ψ := ZMod.stdAddChar) (v j)
        (ZMod.isPrimitive_stdAddChar 3))
  simp_rw [hs]
  by_cases hv : v = 0
  · simp [hv]
  · rw [if_neg hv]
    obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
      by_contra h
      apply hv
      funext j
      exact not_ne_iff.mp (not_exists.mp h j)
    have hzero : (∏ x : Fin d, if v x = 0 then (3 : ℂ) else 0) = 0 := by
      refine Finset.prod_eq_zero (s := (Finset.univ : Finset (Fin d)))
        (f := fun x => if v x = 0 then (3 : ℂ) else 0) (Finset.mem_univ j) ?_
      simp [hj]
    simpa only [Nat.cast_zero] using hzero

/-- The coefficient vector for the ordered pair `(i,j)`. -/
def pairCoefficient {d : ℕ} (i j : Fin d) : Fin d → ZMod 3 :=
  fun k => (if k = i then 1 else 0) - (if k = j then 1 else 0)

/-! Source parameter functions used by the exact two-mean and noisy-state
    formulas.  They are kept as natural/real functions so their domains are
    visible in the checked declarations. -/

def wordCount (n d : ℕ) : ℕ := d ^ n

def cutCount (n : ℕ) : ℕ := 2 ^ (n - 1) - 1

def supportRank (n d : ℕ) : ℕ := d + cutCount n * d * (d - 1)

def witnessSlope (n d : ℕ) : ℝ :=
  (d - 1 : ℝ) / d + ((supportRank n d : ℝ) / d - 1) / wordCount n d

def witnessZeroProbability (n d : ℕ) : ℝ :=
  ((d - 1 : ℝ) / d) / witnessSlope n d

def twoMeanValue (d : ℕ) (f y : ℝ) : ℝ :=
  (y + (d - 2 : ℝ) * f - 2 * Real.sqrt ((d - 1 : ℝ) * f * (y - f))) / d

theorem qutrit_source_arithmetic :
    wordCount 3 3 = 27 ∧ cutCount 3 = 3 ∧ supportRank 3 3 = 21 ∧
      witnessSlope 3 3 = 8 / 9 ∧ witnessZeroProbability 3 3 = 3 / 4 := by
  norm_num [wordCount, cutCount, supportRank, witnessSlope, witnessZeroProbability]

theorem qutrit_two_mean_value :
    twoMeanValue 3 (23 / 36) (11 / 12) = (14 - Real.sqrt 115) / 27 := by
  unfold twoMeanValue
  have hs : Real.sqrt ((2 : ℝ) * (23 / 36) * (11 / 12 - 23 / 36)) =
      Real.sqrt 115 / 18 := by
    have h : (2 : ℝ) * (23 / 36) * (11 / 12 - 23 / 36) = 115 / 324 := by norm_num
    rw [h, Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 115)]
    norm_num
  have hs' : Real.sqrt (((3 : ℝ) - 1) * (23 / 36) * (11 / 12 - 23 / 36)) =
      Real.sqrt 115 / 18 := by
    convert hs using 1 <;> norm_num
  norm_num [hs']
  ring

theorem pairCoefficient_eq_zero_iff {d : ℕ} (i j : Fin d) :
    pairCoefficient i j = 0 ↔ i = j := by
  constructor
  · intro h
    by_contra hij
    have hi : pairCoefficient i j i = (1 : ZMod 3) := by
      simp [pairCoefficient, hij]
    have hz : pairCoefficient i j i = 0 := by simpa [h] using congrFun h i
    rw [hi] at hz
    norm_num at hz
  · intro h
    rcases h with rfl
    funext k
    simp [pairCoefficient]

theorem pair_phase_sum {d : ℕ} (i j : Fin d) :
    (∑ θ : Fin d → ZMod 3, phaseCharacter (pairCoefficient i j) θ) =
      if i = j then (3 ^ d : ℕ) else 0 := by
  rw [phaseCharacter_sum]
  simp [pairCoefficient_eq_zero_iff]

end
end D5.S3.Quantum.Entanglement.Witness.NoisyGhzExactRoof
