/- GID: D5/S3/Quantum/Tomography/PauliFisherGHZRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Tomography/PauliFisherGHZRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Tomography/PauliFisherGHZRefutation.claim; result=D5/S3/Quantum/Tomography/PauliFisherGHZRefutation.result; claim=D5/S3/Quantum/Tomography/PauliFisherGHZRefutation.claim
   digest: GHZ phase tangents refute a uniform lower bound for averaged Pauli Fisher information. -/

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Values
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.style.longLine false

noncomputable section

namespace D5.S3.Quantum.Tomography.PauliFisherGHZRefutation

open scoped BigOperators
open Matrix

def IsDensity {n : ℕ} (ρ : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) : Prop :=
  ρ.PosSemidef ∧ ρ.trace = 1

def pauliEigen (s : Fin 3) (o b : Fin 2) : ℂ :=
  if s = 2 then if b = o then 1 else 0
  else (if b = 0 then 1 else (-1 : ℂ) ^ (o : ℕ) * (if s = 0 then 1 else Complex.I)) /
    (Real.sqrt 2 : ℂ)

def productVector {n : ℕ} (s : Fin n → Fin 3) (o : Fin n → Fin 2)
    (b : Fin n → Fin 2) : ℂ := ∏ j, pauliEigen (s j) (o j) (b j)

def outcomeProb {n : ℕ} (ρ : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)
    (s : Fin n → Fin 3) (o : Fin n → Fin 2) : ℝ :=
  (star (productVector s o) ⬝ᵥ (ρ *ᵥ productVector s o)).re

def settingFisher {n : ℕ} (ρ v : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)
    (s : Fin n → Fin 3) : ℝ :=
  ∑ o, (star (productVector s o) ⬝ᵥ (v *ᵥ productVector s o)).re ^ 2 /
    outcomeProb ρ s o

def averageFisher {n : ℕ} (ρ v : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) : ℝ :=
  (∑ s, settingFisher ρ v s) / 3 ^ n

def IsRankTangent {n : ℕ} (r : ℕ)
    (ρ v : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) : Prop :=
  ∃ γ : ℝ → Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ,
    γ 0 = ρ ∧ HasDerivAt γ v 0 ∧ ∀ t, IsDensity (γ t) ∧ (γ t).rank = r

def claim : Prop :=
  ∀ r : ℕ, 1 ≤ r → ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
    ∀ ρ v : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ,
      IsDensity ρ → ρ.rank = r → IsRankTangent r ρ v →
      c * (v * v).trace.re ≤ averageFisher ρ v

private def ghzKet (n : ℕ) (θ : ℝ) (b : Fin n → Fin 2) : ℂ :=
  ((if b = (fun _ => 0) then 1 else 0) +
    Complex.exp (θ * Complex.I) * (if b = (fun _ => 1) then 1 else 0)) /
    (Real.sqrt 2 : ℂ)

private def ghz (n : ℕ) (θ : ℝ) : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  vecMulVec (ghzKet n θ) (star (ghzKet n θ))

private def phaseDirection (n : ℕ) (θ : ℝ) :
    Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ := fun a b =>
  Complex.I / 2 *
    (Complex.exp (θ * Complex.I) *
      (if a = (fun _ => 1) ∧ b = (fun _ => 0) then 1 else 0) -
    star (Complex.exp (θ * Complex.I)) *
      (if a = (fun _ => 0) ∧ b = (fun _ => 1) then 1 else 0))

private def outcomePhase {n : ℕ} (s : Fin n → Fin 3) (o : Fin n → Fin 2) : ℂ :=
  ∏ j, (-1 : ℂ) ^ (o j : ℕ) * (if s j = 0 then 1 else -Complex.I)

private lemma ghz_density_rank (n : ℕ) (hn : 0 < n) (θ : ℝ) :
    IsDensity (ghz n θ) ∧ (ghz n θ).rank = 1 := by
  sorry

private lemma ghz_derivative (n : ℕ) (hn : 0 < n) (θ : ℝ) :
    HasDerivAt (fun t : ℝ => ghz n (θ + t)) (phaseDirection n θ) 0 := by
  sorry

private lemma phase_norm (n : ℕ) (hn : 0 < n) (θ : ℝ) :
    ((phaseDirection n θ * phaseDirection n θ).trace).re = 1 / 2 := by
  sorry

private lemma z_setting_zero (n : ℕ) (hn : 0 < n) (θ : ℝ)
    (s : Fin n → Fin 3) (hs : ∃ j, s j = 2) :
    settingFisher (ghz n θ) (phaseDirection n θ) s = 0 := by
  sorry

private lemma xy_prob_direction (n : ℕ) (hn : 0 < n)
    (s : Fin n → Fin 3) (hs : ∀ j, s j ≠ 2) (o : Fin n → Fin 2) (θ : ℝ) :
    outcomeProb (ghz n θ) s o =
      (1 + (Complex.exp (θ * Complex.I) * outcomePhase s o).re) / 2 ^ n ∧
    (star (productVector s o) ⬝ᵥ (phaseDirection n θ *ᵥ productVector s o)).re =
      -(Complex.exp (θ * Complex.I) * outcomePhase s o).im / 2 ^ n := by
  sorry

private lemma xy_prob_positive (n : ℕ) (hn : 0 < n)
    (s : Fin n → Fin 3) (hs : ∀ j, s j ≠ 2) (o : Fin n → Fin 2) :
    0 < outcomeProb (ghz n (Real.pi / 4)) s o := by
  sorry

private lemma outcome_phase_sum (n : ℕ) (hn : 0 < n) (s : Fin n → Fin 3) :
    ∑ o, outcomePhase s o = 0 := by
  sorry

private lemma xy_setting_one (n : ℕ) (hn : 0 < n)
    (s : Fin n → Fin 3) (hs : ∀ j, s j ≠ 2) :
    settingFisher (ghz n (Real.pi / 4)) (phaseDirection n (Real.pi / 4)) s = 1 := by
  have hp := xy_prob_direction n hn s hs
  have hpos := xy_prob_positive n hn s hs
  have hsum := outcome_phase_sum n hn s
  sorry

private lemma xy_setting_count (n : ℕ) :
    (∑ s : Fin n → Fin 3, if ∀ j, s j ≠ 2 then (1 : ℝ) else 0) = 2 ^ n := by
  sorry

private lemma average_exact (n : ℕ) (hn : 0 < n) :
    averageFisher (ghz n (Real.pi / 4)) (phaseDirection n (Real.pi / 4)) =
      (2 / 3 : ℝ) ^ n := by
  have hz := z_setting_zero n hn (Real.pi / 4)
  have hxy := xy_setting_one n hn
  have hcount := xy_setting_count n
  sorry

private lemma small_ratio (c : ℝ) (hc : 0 < c) :
    ∃ n : ℕ, 0 < n ∧ 2 * (2 / 3 : ℝ) ^ n < c := by
  sorry

theorem result : ¬ claim := by
  intro h
  obtain ⟨c, hc, hbound⟩ := h 1 le_rfl
  obtain ⟨n, hn, hsmall⟩ := small_ratio c hc
  obtain ⟨hρ, hrank⟩ := ghz_density_rank n hn (Real.pi / 4)
  have ht : IsRankTangent 1 (ghz n (Real.pi / 4))
      (phaseDirection n (Real.pi / 4)) :=
    ⟨fun t => ghz n (Real.pi / 4 + t), by simp,
      ghz_derivative n hn (Real.pi / 4), fun t => ghz_density_rank n hn _⟩
  have hb := hbound n _ _ hρ hrank ht
  rw [phase_norm n hn, average_exact n hn] at hb
  linarith

end D5.S3.Quantum.Tomography.PauliFisherGHZRefutation
