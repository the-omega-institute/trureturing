/- GID: D5/S3/Arith/FibonacciAtomic/RawCorrelationMomentIdentities
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/RawCorrelationMomentIdentities
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: The heterogeneous first-window parameters have legal Bernoulli laws and the exact finite disagreement and norm-gap identities used by raw correlation.
   proof_shape: unsure
   admission_basis: escape-witness
   registration: deferred(CLAUDE.md 3.9)
   escape_witness: finite three-coordinate product expectation is evaluated by an explicit Bool enumeration
   frozen_deps: []
   -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Arith.FibonacciAtomic.RawCorrelationMomentIdentities

open scoped BigOperators

def hOne (ρ : ℝ) : ℝ := 1 - 3 * ρ

def hTwo (ρ : ℝ) : ℝ := 2 * ρ

def ellThree (ρ : ℝ) : ℝ := 2 * ρ

def bernoulliMass (p : ℝ) (b : Bool) : ℝ := if b then p else 1 - p

def productExpectation (p q r : ℝ) (f : Bool → Bool → Bool → ℝ) : ℝ :=
  ∑ x : Bool, ∑ y : Bool, ∑ z : Bool,
    bernoulliMass p x * bernoulliMass q y * bernoulliMass r z * f x y z

def disagreementIndicator : Bool → Bool → Bool → ℝ := fun x y z =>
  if x = y then 0 else if z then 1 else 0

def disagreementMass (ρ : ℝ) : ℝ :=
  productExpectation (hOne ρ) (hTwo ρ) (ellThree ρ) disagreementIndicator

def normGap (ρ : ℝ) : ℝ := hTwo ρ * ellThree ρ - hOne ρ * ellThree ρ

def scoreMean (α ρ : ℝ) : ℝ := α / 8 * (disagreementMass ρ + normGap ρ)

/-- The legal parameter range and the exact finite product-law calculation behind
the heterogeneous first-window disagreement term.  The expectation is expanded
over all eight Bool triples, so the identity is a genuine finite-law computation.
-/
theorem result (ρ α : ℝ) (hρ : 0 < ρ) (hρ8 : ρ ≤ 1 / 8) (hα : 0 < α) :
    0 ≤ hOne ρ ∧ hOne ρ ≤ 1 ∧
    0 ≤ hTwo ρ ∧ hTwo ρ ≤ 1 ∧
    0 ≤ ellThree ρ ∧ ellThree ρ ≤ 1 ∧
    disagreementMass ρ = 2 * ρ * (1 - 5 * ρ + 12 * ρ ^ 2) ∧
    normGap ρ = -2 * ρ + 10 * ρ ^ 2 ∧
    scoreMean α ρ = 3 * α * ρ ^ 3 ∧
    0 < scoreMean α ρ := by
  have hρ0 : 0 ≤ ρ := le_of_lt hρ
  have hρ3 : 3 * ρ ≤ 1 := by linarith
  have hρ2 : 2 * ρ ≤ 1 := by linarith
  have hD : disagreementMass ρ =
      ellThree ρ * (hOne ρ * (1 - hTwo ρ) + hTwo ρ * (1 - hOne ρ)) := by
    classical
    simp [disagreementMass, productExpectation, disagreementIndicator,
      bernoulliMass, hOne, hTwo, ellThree]
    ring
  have hScore : scoreMean α ρ = 3 * α * ρ ^ 3 := by
    rw [scoreMean, hD]
    simp [normGap, hOne, hTwo, ellThree]
    ring
  have hScorePos : 0 < scoreMean α ρ := by
    rw [hScore]
    positivity
  refine ⟨by dsimp [hOne]; linarith, by dsimp [hOne]; linarith,
    by dsimp [hTwo]; linarith, by dsimp [hTwo]; linarith,
    by dsimp [ellThree]; linarith, by dsimp [ellThree]; linarith, ?_, ?_,
    hScore, hScorePos⟩
  · rw [hD]
    dsimp [hOne, hTwo, ellThree]
    ring
  · simp [normGap, hOne, hTwo, ellThree]
    ring

end D5.S3.Arith.FibonacciAtomic.RawCorrelationMomentIdentities
