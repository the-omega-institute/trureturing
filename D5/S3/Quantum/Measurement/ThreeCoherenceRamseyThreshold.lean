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

private theorem denominator_positive (r : ℝ) (hr : 0 ≤ r) : 0 < thresholdD r := by
  unfold thresholdD
  positivity

private theorem threshold_bound (α : ℝ) (hl : 6169 / 5000 < α)
    (hh : α < 12339 / 10000) (hp : thresholdP α = 0) :
    5 / 4 < thresholdN α / thresholdD α ∧
    ∀ r : ℝ, 0 ≤ r → thresholdN r / thresholdD r ≤ thresholdN α / thresholdD α := by
  have ha : (123 / 100 : ℝ) < α := by linarith
  have hb : α < (31 / 25 : ℝ) := by linarith
  have hapos : 0 ≤ α := by linarith
  have hd := denominator_positive α hapos
  let T := thresholdN α / thresholdD α
  have hnlo : thresholdN (6169 / 5000) ≤ thresholdN α := by
    unfold thresholdN
    gcongr <;> linarith
  have hdhi : thresholdD α ≤ thresholdD (12339 / 10000) := by
    unfold thresholdD
    gcongr <;> linarith
  have hnum : (177 / 100 : ℝ) * thresholdD (12339 / 10000) <
      thresholdN (6169 / 5000) := by norm_num [thresholdN, thresholdD]
  have ht : (177 / 100 : ℝ) < T := by
    apply (lt_div_iff₀ hd).2
    linarith
  have hv : T * thresholdD α - thresholdN α = 0 := by
    dsimp [T]
    rw [div_mul_cancel₀ _ hd.ne', sub_self]
  have hs : (α + 2) * (α ^ 2 + 2) *
      (T * (6 * α ^ 5 + 20 * α ^ 4 + 32 * α ^ 3 + 48 * α ^ 2 + 40 * α + 16) -
        (6 * α ^ 5 + 120 * α ^ 3 + 180 * α)) = 0 := by
    unfold thresholdD thresholdN at hv
    unfold thresholdP at hp
    linear_combination (6 * α ^ 2 + 8 * α + 4) * hv - 4 * hp
  have hstat : T * (6 * α ^ 5 + 20 * α ^ 4 + 32 * α ^ 3 + 48 * α ^ 2 + 40 * α + 16) -
      (6 * α ^ 5 + 120 * α ^ 3 + 180 * α) = 0 :=
    (mul_eq_zero.mp hs).resolve_left (by positivity)
  have hq4 : 0 < T - 1 := by linarith
  have hq3 : 0 < 4 * T + 2 * α * (T - 1) := by positivity
  have hq2 : 0 < 8 * T - 30 + 8 * α * T + 3 * α ^ 2 * (T - 1) := by
    have hbound : 8 * (177 / 100 : ℝ) + 8 * (123 / 100) * (177 / 100) +
        3 * (123 / 100) ^ 2 * (77 / 100) ≤
        8 * T + 8 * α * T + 3 * α ^ 2 * (T - 1) := by
      gcongr <;> linarith
    linarith
  have hq1 : 0 < 16 * T + 16 * α * T - 60 * α +
      12 * α ^ 2 * T + 4 * α ^ 3 * (T - 1) := by
    have hbound : 16 * (177 / 100 : ℝ) + 16 * (123 / 100) * (177 / 100) +
        12 * (123 / 100) ^ 2 * (177 / 100) + 4 * (123 / 100) ^ 3 * (77 / 100) ≤
        16 * T + 16 * α * T + 12 * α ^ 2 * T + 4 * α ^ 3 * (T - 1) := by
      gcongr <;> linarith
    linarith
  have hq0 : 0 < 20 * T - 90 + 32 * α * T + (24 * T - 90) * α ^ 2 +
      16 * T * α ^ 3 + 5 * (T - 1) * α ^ 4 := by
    have hbound : 20 * (177 / 100 : ℝ) + 32 * (123 / 100) * (177 / 100) +
        24 * (177 / 100) * (123 / 100) ^ 2 + 16 * (177 / 100) * (123 / 100) ^ 3 +
        5 * (77 / 100) * (123 / 100) ^ 4 ≤
        20 * T + 32 * α * T + 24 * T * α ^ 2 + 16 * T * α ^ 3 +
        5 * (T - 1) * α ^ 4 := by
      gcongr <;> linarith
    have hsquare : α ^ 2 ≤ (31 / 25 : ℝ) ^ 2 := by gcongr <;> linarith
    nlinarith only [hbound, hsquare]
  refine ⟨by dsimp [T] at ht; linarith, ?_⟩
  intro r hr
  have hidentity : T * thresholdD r - thresholdN r = (r - α) ^ 2 *
      ((T - 1) * r ^ 4 + (4 * T + 2 * α * (T - 1)) * r ^ 3 +
       (8 * T - 30 + 8 * α * T + 3 * α ^ 2 * (T - 1)) * r ^ 2 +
       (16 * T + 16 * α * T - 60 * α + 12 * α ^ 2 * T +
         4 * α ^ 3 * (T - 1)) * r +
       (20 * T - 90 + 32 * α * T + (24 * T - 90) * α ^ 2 +
         16 * T * α ^ 3 + 5 * (T - 1) * α ^ 4)) := by
    unfold thresholdD thresholdN at hv ⊢
    linear_combination hv + (r - α) * hstat
  apply (div_le_iff₀ (denominator_positive r hr)).2
  have hquartic : 0 ≤
      (T - 1) * r ^ 4 + (4 * T + 2 * α * (T - 1)) * r ^ 3 +
      (8 * T - 30 + 8 * α * T + 3 * α ^ 2 * (T - 1)) * r ^ 2 +
      (16 * T + 16 * α * T - 60 * α + 12 * α ^ 2 * T + 4 * α ^ 3 * (T - 1)) * r +
      (20 * T - 90 + 32 * α * T + (24 * T - 90) * α ^ 2 +
        16 * T * α ^ 3 + 5 * (T - 1) * α ^ 4) := by positivity
  nlinarith only [hidentity, mul_nonneg (sq_nonneg (r - α)) hquartic]

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
