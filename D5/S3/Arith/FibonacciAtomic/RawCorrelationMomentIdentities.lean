/- GID: D5/S3/Arith/FibonacciAtomic/RawCorrelationMomentIdentities
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/RawCorrelationMomentIdentities
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: The heterogeneous first-window parameters have legal Bernoulli laws and the exact finite disagreement and norm-gap identities used by raw correlation. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Arith.FibonacciAtomic.RawCorrelationMomentIdentities

open scoped BigOperators

def hOne (ρ : ℝ) : ℝ := 1 - 3 * ρ

def hTwo (ρ : ℝ) : ℝ := 2 * ρ

def bernoulliMass (p : ℝ) (b : Bool) : ℝ := if b then p else 1 - p

def productExpectation (p q r : ℝ) (f : Bool → Bool → Bool → ℝ) : ℝ :=
  ∑ x : Bool, ∑ y : Bool, ∑ z : Bool,
    bernoulliMass p x * bernoulliMass q y * bernoulliMass r z * f x y z

def disagreementIndicator : Bool → Bool → Bool → ℝ := fun x y z =>
  if x = y then 0 else if z then 1 else 0

def disagreementMass (ρ : ℝ) : ℝ :=
  productExpectation (hOne ρ) (hTwo ρ) (hTwo ρ) disagreementIndicator

def normGap (ρ : ℝ) : ℝ := hTwo ρ * hTwo ρ - hOne ρ * hTwo ρ

def channelBase (c y : Fin 3) : ℝ :=
  if c = 0 then if y = 0 then 1 / 2 else 1 / 4
  else if c = 1 then if y = 1 then 1 / 4 else 3 / 8
  else if y = 2 then 1 / 2 else 1 / 4

def channelMass (α : ℝ) (c y : Fin 3) : ℝ :=
  α * channelBase c y + (1 - α) / 3

def candidateClass (h l b c : Bool) : Fin 3 :=
  if h && l then 1 else if b && c then 2 else 0

def zScore (y : Fin 3) : ℝ := if y = 2 then 1 else if y = 0 then -1 else 0

def classOffset (c : Fin 3) : ℝ := (c.val : ℝ) - 1

def rawDifference (h₁ h₂ h₃ l₃ l₄ : Bool) : ℝ :=
  classOffset (candidateClass h₁ l₃ h₃ l₄) - classOffset (candidateClass h₂ l₃ h₃ l₄)

def scoreMean (α ρ : ℝ) : ℝ :=
  ∑ h₁ : Bool, ∑ h₂ : Bool, ∑ h₃ : Bool, ∑ l₃ : Bool, ∑ l₄ : Bool,
    ∑ y : Fin 3,
      bernoulliMass (hOne ρ) h₁ * bernoulliMass (hTwo ρ) h₂ *
        bernoulliMass (hTwo ρ) h₃ * bernoulliMass (hTwo ρ) l₃ *
        bernoulliMass (hTwo ρ) l₄ * channelMass α (candidateClass h₁ l₃ h₃ l₄) y *
        zScore y * rawDifference h₁ h₂ h₃ l₃ l₄

def kappa (α : ℝ) : ℝ := (8 + α) / 12

def rawSecondMoment (α ρ : ℝ) : ℝ :=
  ∑ h₁ : Bool, ∑ h₂ : Bool, ∑ h₃ : Bool, ∑ l₃ : Bool, ∑ l₄ : Bool,
    ∑ y : Fin 3,
      bernoulliMass (hOne ρ) h₁ * bernoulliMass (hTwo ρ) h₂ *
        bernoulliMass (hTwo ρ) h₃ * bernoulliMass (hTwo ρ) l₃ *
        bernoulliMass (hTwo ρ) l₄ * channelMass α (candidateClass h₁ l₃ h₃ l₄) y *
        (zScore y * rawDifference h₁ h₂ h₃ l₃ l₄) ^ 2

def scoreVariance (α ρ : ℝ) : ℝ := rawSecondMoment α ρ - scoreMean α ρ ^ 2

/-- The legal parameter range and the exact finite product-law calculation behind
the heterogeneous first-window disagreement term.  The expectation is expanded
over all eight Bool triples, so the identity is a genuine finite-law computation.
-/
theorem result (ρ α : ℝ) (hρ : 0 < ρ) (hρ8 : ρ ≤ 1 / 8) (hα : 0 < α) :
    0 ≤ hOne ρ ∧ hOne ρ ≤ 1 ∧
    0 ≤ hTwo ρ ∧ hTwo ρ ≤ 1 ∧
    0 ≤ hTwo ρ ∧ hTwo ρ ≤ 1 ∧
    disagreementMass ρ = 2 * ρ * (1 - 5 * ρ + 12 * ρ ^ 2) ∧
    normGap ρ = -2 * ρ + 10 * ρ ^ 2 ∧
    scoreMean α ρ = α / 8 * (disagreementMass ρ + normGap ρ) ∧
    scoreMean α ρ = 3 * α * ρ ^ 3 ∧
    scoreVariance α ρ = kappa α * disagreementMass ρ - 9 * α ^ 2 * ρ ^ 6 ∧
    0 < scoreMean α ρ := by
  have hρ0 : 0 ≤ ρ := le_of_lt hρ
  have hρ3 : 3 * ρ ≤ 1 := by linarith
  have hρ2 : 2 * ρ ≤ 1 := by linarith
  have hD : disagreementMass ρ =
      hTwo ρ * (hOne ρ * (1 - hTwo ρ) + hTwo ρ * (1 - hOne ρ)) := by
    classical
    simp [disagreementMass, productExpectation, disagreementIndicator,
      bernoulliMass, hOne, hTwo]
    ring
  have hScore : scoreMean α ρ = 3 * α * ρ ^ 3 := by
    classical
    simp [scoreMean, channelMass, channelBase, candidateClass, zScore,
      classOffset, rawDifference, bernoulliMass, hOne, hTwo,
      Fin.sum_univ_three]
    ring
  have hSecond : rawSecondMoment α ρ = kappa α * disagreementMass ρ := by
    classical
    simp [rawSecondMoment, kappa, channelMass, channelBase, candidateClass,
      zScore, classOffset, rawDifference, bernoulliMass, hOne, hTwo,
      disagreementMass, productExpectation, disagreementIndicator,
      Fin.sum_univ_three]
    ring
  have hVariance : scoreVariance α ρ =
      kappa α * disagreementMass ρ - 9 * α ^ 2 * ρ ^ 6 := by
    rw [scoreVariance, hSecond, hScore]
    ring
  have hScoreFormula : scoreMean α ρ =
      α / 8 * (disagreementMass ρ + normGap ρ) := by
    rw [hScore, hD]
    simp [normGap, hOne, hTwo]
    ring
  have hScorePos : 0 < scoreMean α ρ := by
    rw [hScore]
    positivity
  refine ⟨by dsimp [hOne]; linarith, by dsimp [hOne]; linarith,
    by dsimp [hTwo]; linarith, by dsimp [hTwo]; linarith,
    by dsimp [hTwo]; linarith, by dsimp [hTwo]; linarith, ?_, ?_,
    hScoreFormula, hScore, hVariance, hScorePos⟩
  · rw [hD]
    dsimp [hOne, hTwo]
    ring
  · simp [normGap, hOne, hTwo]
    ring

end D5.S3.Arith.FibonacciAtomic.RawCorrelationMomentIdentities
