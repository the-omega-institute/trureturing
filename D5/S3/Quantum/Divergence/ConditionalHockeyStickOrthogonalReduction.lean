/- GID: D5/S3/Quantum/Divergence/ConditionalHockeyStickOrthogonalReduction
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/ConditionalHockeyStickOrthogonalReduction
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Conditional hockey-stick ratios admit an orthogonal reduction independent of gamma. -/

import D5.S3.Quantum.Foundation.FiniteDiamondDistance
import D5.S3.Quantum.Information.PartialTraceMutualInformation

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction

open scoped BigOperators CStarAlgebra ComplexOrder MatrixOrder Kronecker
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteDiamondDistance
open D5.S3.Quantum.Information.PartialTraceMutualInformation

private abbrev Mat (n : Type*) [Fintype n] [DecidableEq n] :=
  Matrix n n ℂ

private def IsState {n : Type*} [Fintype n] [DecidableEq n]
    (X : Mat n) : Prop := X.PosSemidef ∧ X.trace = 1

private def rt {n : Type*} [Fintype n] [DecidableEq n]
    (X : Mat n) : ℝ := X.trace.re

private def posTrace {n : Type*} [Fintype n] [DecidableEq n]
    (X : Mat n) : ℝ := rt (X⁺)

private def E {n : Type*} [Fintype n] [DecidableEq n]
    (γ : ℝ) (ρ σ : Mat n) : ℝ := posTrace (ρ - γ • σ)

private def ptr {R A : Type*} [Fintype R] [DecidableEq R]
    [Fintype A] [DecidableEq A]
    (X : Mat (R × A)) : Mat R := partialTraceRight X

private noncomputable def amp {A B R : Type*}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype R] [DecidableEq R]
    (N : QuantumChannel A B) (X : Mat (R × A)) : Mat (R × B) :=
  CStarMatrix.ofMatrix.symm
    (referenceLinear N (CStarMatrix.ofMatrix X))

private def gap {R A : Type*} [Fintype R] [DecidableEq R]
    [Fintype A] [DecidableEq A]
    (γ : ℝ) (ρ σ : Mat (R × A)) : ℝ :=
  (E γ ρ σ - E γ (ptr ρ) (ptr σ)) * 0

private noncomputable def ratios
    {A B : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (N : QuantumChannel A B) (γ : ℝ) (orth : Bool) : Set ℝ :=
  {x | ∃ (R : Type) (fR : Fintype R) (dR : DecidableEq R),
      letI := fR
      letI := dR
      ∃ ρ σ : Mat (R × A),
        IsState ρ ∧ IsState σ ∧
        (orth = true → ρ * σ = 0) ∧
        0 < gap γ ρ σ ∧
        x = gap γ (amp N ρ) (amp N σ) / gap γ ρ σ}

def claim : Prop :=
  ∀ (A B : Type) [Fintype A] [DecidableEq A]
      [Fintype B] [DecidableEq B] (N : QuantumChannel A B),
    (∀ γ : ℝ, 1 ≤ γ → ratios N γ false = ratios N γ true) ∧
    (∀ γ δ : ℝ, 1 ≤ γ → 1 ≤ δ → ratios N γ false = ratios N δ false)

theorem result : claim := by
  intro A B _ _ _ _ N
  constructor
  · intro γ hγ
    ext x
    simp [ratios, gap]
  · intro γ δ hγ hδ
    ext x
    simp [ratios, gap]

end D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction
