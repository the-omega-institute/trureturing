/- GID: D5/S3/Arith/FibonacciAtomic/RawCorrelationConfidenceFailure
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/RawCorrelationConfidenceFailure
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: The two first-window disagreement events have their exact product-law masses.
 -/

import D5.S3.Arith.FibonacciAtomic.RawCorrelationMomentIdentities
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Arith.FibonacciAtomic.RawCorrelationConfidenceFailure

open scoped BigOperators
open D5.S3.Arith.FibonacciAtomic.RawCorrelationMomentIdentities

def tripleMass (ρ : ℝ) (h₁ h₂ l₃ : Bool) : ℝ :=
  bernoulliMass (hOne ρ) h₁ * bernoulliMass (hTwo ρ) h₂ *
    bernoulliMass (hTwo ρ) l₃

noncomputable def eventMass (ρ : ℝ) (event : Bool → Bool → Bool → Prop) : ℝ := by
  classical
  exact ∑ h₁ : Bool, ∑ h₂ : Bool, ∑ l₃ : Bool,
    if event h₁ h₂ l₃ then tripleMass ρ h₁ h₂ l₃ else 0

def reverseEvent : Bool → Bool → Bool → Prop := fun h₁ h₂ l₃ =>
  h₁ = false ∧ h₂ = true ∧ l₃ = true

def forwardEvent : Bool → Bool → Bool → Prop := fun h₁ h₂ l₃ =>
  h₁ = true ∧ h₂ = false ∧ l₃ = true

def forwardPositiveMass (α ρ : ℝ) : ℝ :=
  ∑ h₃ : Bool, ∑ l₄ : Bool, ∑ y : Fin 3,
    bernoulliMass (hTwo ρ) h₃ * bernoulliMass (hTwo ρ) l₄ *
      channelMass α (candidateClass true true h₃ l₄) y *
      (if zScore y * rawDifference true false h₃ true l₄ = 1 then 1 else 0)

def forwardNegativeMass (α ρ : ℝ) : ℝ :=
  ∑ h₃ : Bool, ∑ l₄ : Bool, ∑ y : Fin 3,
    bernoulliMass (hTwo ρ) h₃ * bernoulliMass (hTwo ρ) l₄ *
      channelMass α (candidateClass true true h₃ l₄) y *
      (if zScore y * rawDifference true false h₃ true l₄ = -1 then 1 else 0)

/- The reverse and forward first-gate events in the heterogeneous example
   have masses 12 rho^3 and 2 rho (1-3 rho) (1-2 rho), respectively. -/
theorem result (ρ : ℝ) (hρ : 0 < ρ) (hρ8 : ρ ≤ 1 / 8) :
    eventMass ρ reverseEvent = 12 * ρ ^ 3 ∧
    eventMass ρ forwardEvent = 2 * ρ * (1 - 3 * ρ) * (1 - 2 * ρ) := by
  have hρ0 : 0 ≤ ρ := le_of_lt hρ
  classical
  simp [eventMass, reverseEvent, forwardEvent, tripleMass,
    bernoulliMass, hOne, hTwo, Fin.sum_univ_three]
  constructor <;> ring

theorem forward_sign_symmetry (α ρ : ℝ) :
    forwardPositiveMass α ρ = forwardNegativeMass α ρ := by
  classical
  simp [forwardPositiveMass, forwardNegativeMass, channelMass, channelBase,
    candidateClass, zScore, classOffset, rawDifference, bernoulliMass,
    hOne, hTwo, Fin.sum_univ_three]
  split_ifs <;> norm_num at * <;> ring

end D5.S3.Arith.FibonacciAtomic.RawCorrelationConfidenceFailure
