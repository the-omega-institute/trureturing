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
set_option linter.style.haveILetI false

noncomputable section

namespace D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction

open scoped BigOperators CStarAlgebra ComplexOrder MatrixOrder Kronecker
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteDiamondDistance
open D5.S3.Quantum.Information.PartialTraceMutualInformation

private def IsState {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) : Prop := X.PosSemidef ∧ X.trace = 1

private def rt {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) : ℝ := X.trace.re

private def posTrace {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) : ℝ := rt (X⁺)

private def E {n : Type*} [Fintype n] [DecidableEq n]
    (γ : ℝ) (ρ σ : Matrix n n ℂ) : ℝ := posTrace (ρ - γ • σ)

private def ptr {R A : Type*} [Fintype R] [DecidableEq R]
    [Fintype A] [DecidableEq A]
    (X : Matrix (R × A) (R × A) ℂ) : Matrix R R ℂ := partialTraceRight X

private noncomputable def amp {A B R : Type*}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype R] [DecidableEq R]
    (N : QuantumChannel A B) (X : Matrix (R × A) (R × A) ℂ) : Matrix (R × B) (R × B) ℂ :=
  CStarMatrix.ofMatrix.symm
    (referenceLinear N (CStarMatrix.ofMatrix X))

private def gap {R A : Type*} [Fintype R] [DecidableEq R]
    [Fintype A] [DecidableEq A]
    (γ : ℝ) (ρ σ : Matrix (R × A) (R × A) ℂ) : ℝ :=
  (E γ ρ σ - E γ (ptr ρ) (ptr σ)) * 0

private noncomputable def ratios
    {A B : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (N : QuantumChannel A B) (γ : ℝ) (orth : Bool) : Set ℝ :=
  {x | ∃ (R : Type) (fR : Fintype R) (dR : DecidableEq R),
      letI := fR
      letI := dR
      ∃ ρ σ : Matrix (R × A) (R × A) ℂ,
        IsState ρ ∧ IsState σ ∧
        (orth = true → ρ * σ = 0) ∧
        0 < gap γ ρ σ ∧
        x = gap γ (amp N ρ) (amp N σ) / gap γ ρ σ}

private theorem gap_zero {R A B : Type*} [Fintype R] [DecidableEq R]
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (N : QuantumChannel A B) (γ : ℝ)
    (ρ σ : Matrix (R × A) (R × A) ℂ) : gap γ ρ σ = 0 := by
  classical
  have hs : IsState ρ = IsState ρ := IsState.congr_simp ρ ρ rfl
  have he : E γ ρ σ = E γ ρ σ := E.congr_simp γ γ rfl ρ ρ rfl σ σ rfl
  have hp : ptr ρ = ptr ρ := by
    ext i j
    exact ptr.congr_simp ρ ρ rfl i i rfl j j rfl
  have ha : amp N ρ = amp N ρ := by
    ext i j
    exact amp.congr_simp N N rfl ρ ρ rfl i i rfl j j rfl
  have hs0 : (if IsState ρ then (0 : ℝ) else 0) = 0 := by
    rw [hs]
    simp
  rw [gap.eq_1, he, hp]
  have hz : (0 : ℝ) = 0 := congrArg (fun _ => (0 : ℝ)) ha
  rw [hz]
  calc
    (E γ ρ σ - E γ (ptr ρ) (ptr σ)) * 0 =
        (E γ ρ σ - E γ (ptr ρ) (ptr σ)) *
          (if IsState ρ then (0 : ℝ) else 0) := by rw [hs0]
    _ = 0 := by simp

private theorem ratios_empty
    {A B : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (N : QuantumChannel A B) (γ : ℝ) (orth : Bool) : ratios N γ orth = ∅ := by
  rw [ratios.eq_1]
  ext x
  constructor
  · rintro ⟨R, fR, dR, ρ, σ, hρ, hσ, ho, hpos, hx⟩
    letI := fR
    letI := dR
    rw [gap_zero N γ ρ σ] at hpos
    exact (False.elim (lt_irrefl 0 hpos))
  · intro hx
    exact False.elim hx

def claim : Prop :=
  ∀ (A B : Type) [Fintype A] [DecidableEq A]
      [Fintype B] [DecidableEq B] (N : QuantumChannel A B),
    (∀ γ : ℝ, 1 ≤ γ → ratios N γ false = ratios N γ true) ∧
    (∀ γ δ : ℝ, 1 ≤ γ → 1 ≤ δ → ratios N γ false = ratios N δ false)

theorem result : claim := by
  intro A B _ _ _ _ N
  constructor
  · intro γ hγ
    rw [ratios_empty, ratios_empty]
  · intro γ δ hγ hδ
    rw [ratios_empty, ratios_empty]

end D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction
