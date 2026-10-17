/- GID: D5/S3/Quantum/Measurement/ThreeCoherenceRamseyThreshold
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/ThreeCoherenceRamseyThreshold
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The exact three-coherence Ramsey third-moment threshold. -/

module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # The sharp three-coherence Ramsey threshold -/

public section

noncomputable section

open Complex Real MeasureTheory Finset
open scoped BigOperators

namespace D5.S3.Quantum.Measurement.ThreeCoherenceRamseyThreshold

/-- The probability of a rank-one Ramsey measurement with integer energy labels. -/
def signal {d : ℕ} (n : Fin d → ℤ) (χ ψ : Fin d → ℂ) (t : ℝ) : ℝ :=
  Complex.normSq (∑ j, star (χ j) * Complex.exp (-(n j : ℂ) * t * I) * ψ j)

/-- A finite probabilistic mixture of pure Ramsey signals. -/
def mixedSignal {d L : ℕ} (n : Fin d → ℤ) (χ : Fin d → ℂ)
    (ψ : Fin L → Fin d → ℂ) (w : Fin L → ℝ) (t : ℝ) : ℝ :=
  ∑ l, w l * signal n χ (ψ l) t

/-- The normalized integral of a power over one period. -/
def moment (q : ℕ) (p : ℝ → ℝ) : ℝ :=
  (1 / (2 * π)) * ∫ t in (0)..(2 * π), p t ^ q

/-- The third moment divided by the square of the first moment. -/
def ratio3 (p : ℝ → ℝ) : ℝ := moment 3 p / moment 1 p ^ 2

/-- At most three coordinates are nonzero. -/
def IsThreeSparse {d : ℕ} (ψ : Fin d → ℂ) : Prop :=
  (Function.support ψ).ncard ≤ 3

/-- The squared amplitudes sum to one. -/
def IsUnitVector {d : ℕ} (ψ : Fin d → ℂ) : Prop :=
  ∑ j, Complex.normSq (ψ j) = 1

/-- All third-moment ratios from finite mixtures of unit three-sparse vectors. -/
def admissibleValues : Set ℝ :=
  {v | ∃ (d L : ℕ) (n : Fin d → ℤ) (χ : Fin d → ℂ)
      (ψ : Fin L → Fin d → ℂ) (w : Fin L → ℝ),
    IsUnitVector χ ∧ (∀ l, IsUnitVector (ψ l) ∧ IsThreeSparse (ψ l)) ∧
    (∀ l, 0 ≤ w l) ∧ (∑ l, w l) = 1 ∧
    0 < moment 1 (mixedSignal n χ ψ w) ∧ v = ratio3 (mixedSignal n χ ψ w)}

def thresholdN (r : ℝ) : ℝ := r ^ 6 + 30 * r ^ 4 + 90 * r ^ 2 + 20

def thresholdD (r : ℝ) : ℝ := (r + 2) ^ 2 * (r ^ 2 + 2) ^ 2

def thresholdP (r : ℝ) : ℝ :=
  r ^ 7 - 13 * r ^ 6 + 6 * r ^ 5 - 60 * r ^ 4 + 30 * r ^ 3 -
    30 * r ^ 2 + 140 * r - 20

/-- The isolated algebraic value is the greatest physically admissible ratio. -/
def claim : Prop := ∃ α : ℝ,
  6169 / 5000 < α ∧ α < 12339 / 10000 ∧ thresholdP α = 0 ∧
  IsGreatest admissibleValues (thresholdN α / thresholdD α)

private theorem root_exists : ∃ α : ℝ,
    6169 / 5000 < α ∧ α < 12339 / 10000 ∧ thresholdP α = 0 := by
  have hlow : 0 < thresholdP (6169 / 5000) := by norm_num [thresholdP]
  have hhigh : thresholdP (12339 / 10000) < 0 := by norm_num [thresholdP]
  have hcont : Continuous thresholdP := by unfold thresholdP; fun_prop
  obtain ⟨α, hα, hzero⟩ := intermediate_value_Icc'
    (by norm_num : (6169 / 5000 : ℝ) ≤ 12339 / 10000) hcont.continuousOn
    (show (0 : ℝ) ∈ Set.Icc (thresholdP (12339 / 10000))
      (thresholdP (6169 / 5000)) from ⟨hhigh.le, hlow.le⟩)
  refine ⟨α, lt_of_le_of_ne hα.1 ?_, lt_of_le_of_ne hα.2 ?_, hzero⟩
  · intro h; subst α; linarith
  · intro h; subst α; linarith

private theorem threshold_bound (α : ℝ) (hl : 6169 / 5000 < α)
    (hh : α < 12339 / 10000) (hp : thresholdP α = 0) :
    5 / 4 < thresholdN α / thresholdD α ∧
    ∀ r : ℝ, 0 ≤ r → thresholdN r / thresholdD r ≤ thresholdN α / thresholdD α := by
  sorry

private theorem signal_bound (T : ℝ) (hT : 5 / 4 < T)
    (hsym : ∀ r : ℝ, 0 ≤ r → thresholdN r / thresholdD r ≤ T)
    {d L : ℕ} (n : Fin d → ℤ) (χ : Fin d → ℂ) (ψ : Fin L → Fin d → ℂ)
    (w : Fin L → ℝ) (hχ : IsUnitVector χ)
    (hψ : ∀ l, IsUnitVector (ψ l) ∧ IsThreeSparse (ψ l))
    (hw : ∀ l, 0 ≤ w l) (hwone : ∑ l, w l = 1)
    (hm : 0 < moment 1 (mixedSignal n χ ψ w)) :
    ratio3 (mixedSignal n χ ψ w) ≤ T := by
  sorry

private theorem threshold_attained (α : ℝ) (hα : 0 ≤ α) :
    thresholdN α / thresholdD α ∈ admissibleValues := by
  sorry

/-- The sharp three-coherence threshold, including arbitrary integer spectra and mixtures. -/
theorem result : claim := by
  obtain ⟨α, hl, hh, hp⟩ := root_exists
  obtain ⟨hT, hsym⟩ := threshold_bound α hl hh hp
  refine ⟨α, hl, hh, hp, threshold_attained α (by linarith), ?_⟩
  rintro v ⟨d, L, n, χ, ψ, w, hχ, hψ, hw, hwone, hm, rfl⟩
  exact signal_bound _ hT hsym n χ ψ w hχ hψ hw hwone hm

end D5.S3.Quantum.Measurement.ThreeCoherenceRamseyThreshold
