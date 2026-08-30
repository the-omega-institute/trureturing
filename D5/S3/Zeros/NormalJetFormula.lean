/- GID: D5/S3/Zeros/NormalJetFormula
   generality: G
   mirror-B: D5/B/S3/Zeros/NormalJetFormula
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Compute every even normal jet from the two conjugate Taylor channels. -/

import Mathlib.Data.Complex.BigOperators
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.RingTheory.PowerSeries.Derivative

noncomputable section

namespace D5.S3.Zeros.NormalJetFormula

open scoped PowerSeries

/-- The formal Taylor channel obtained by moving in one complex normal direction. -/
def normalTaylorChannel (Xi : ℝ → ℝ) (t : ℝ) (direction : ℂ) : ℂ⟦X⟧ :=
  PowerSeries.mk fun n =>
    ((iteratedDeriv n Xi t : ℝ) : ℂ) * direction ^ n / (n.factorial : ℂ)

/-- The normal intensity is the Cauchy product of the two opposite Taylor channels. -/
def normalIntensitySeries (Xi : ℝ → ℝ) (t : ℝ) : ℂ⟦X⟧ :=
  normalTaylorChannel Xi t (-Complex.I) * normalTaylorChannel Xi t Complex.I

/-- The normal jet of depth `m` is the real even coefficient of the intensity series. -/
def normalJet (Xi : ℝ → ℝ) (t : ℝ) (m : ℕ) : ℝ :=
  (PowerSeries.coeff (2 * m) (normalIntensitySeries Xi t)).re

private lemma phase_product (m j : ℕ) (hj : j ≤ 2 * m) :
    (-Complex.I) ^ j * Complex.I ^ (2 * m - j) =
      (-1 : ℂ) ^ (m + j) := by
  calc
    (-Complex.I) ^ j * Complex.I ^ (2 * m - j) =
        ((-1 : ℂ) * Complex.I) ^ j * Complex.I ^ (2 * m - j) := by ring
    _ = (-1 : ℂ) ^ j *
        (Complex.I ^ j * Complex.I ^ (2 * m - j)) := by rw [mul_pow]; ring
    _ = (-1 : ℂ) ^ j * Complex.I ^ (j + (2 * m - j)) := by rw [pow_add]
    _ = (-1 : ℂ) ^ j * Complex.I ^ (2 * m) := by rw [Nat.add_sub_of_le hj]
    _ = (-1 : ℂ) ^ j * (Complex.I ^ 2) ^ m := by rw [pow_mul]
    _ = (-1 : ℂ) ^ j * (-1 : ℂ) ^ m := by rw [Complex.I_sq]
    _ = (-1 : ℂ) ^ (m + j) := by rw [← pow_add, Nat.add_comm]

private theorem even_coefficient_formula (Xi : ℝ → ℝ) (t : ℝ) (m : ℕ) :
    PowerSeries.coeff (2 * m) (normalIntensitySeries Xi t) =
      ∑ j ∈ Finset.range (2 * m + 1),
        (((-1 : ℝ) ^ (m + j) /
              ((j.factorial : ℝ) * ((2 * m - j).factorial : ℝ)) *
            iteratedDeriv j Xi t * iteratedDeriv (2 * m - j) Xi t : ℝ) : ℂ) := by
  rw [normalIntensitySeries, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [normalTaylorChannel, PowerSeries.coeff_mk]
  rw [Nat.succ_eq_add_one]
  apply Finset.sum_congr rfl
  intro j hj
  have hjle : j ≤ 2 * m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  push_cast
  rw [← phase_product m j hjle]
  ring

/-- Every even normal coefficient is the signed derivative convolution; the first
three jets and the second normal derivative are its explicit initial consequences. -/
theorem normal_jet_formula (Xi : ℝ → ℝ) (t : ℝ) :
    (∀ m : ℕ,
      normalJet Xi t m =
        ∑ j ∈ Finset.range (2 * m + 1),
          (-1 : ℝ) ^ (m + j) /
              ((j.factorial : ℝ) * ((2 * m - j).factorial : ℝ)) *
            iteratedDeriv j Xi t * iteratedDeriv (2 * m - j) Xi t) ∧
    normalJet Xi t 0 = Xi t ^ 2 ∧
    normalJet Xi t 1 =
      iteratedDeriv 1 Xi t ^ 2 - Xi t * iteratedDeriv 2 Xi t ∧
    normalJet Xi t 2 =
      (1 / 4 : ℝ) * iteratedDeriv 2 Xi t ^ 2 -
        (1 / 3 : ℝ) * iteratedDeriv 1 Xi t * iteratedDeriv 3 Xi t +
          (1 / 12 : ℝ) * Xi t * iteratedDeriv 4 Xi t ∧
    (PowerSeries.coeff 0
        (PowerSeries.derivative ℂ
          (PowerSeries.derivative ℂ (normalIntensitySeries Xi t)))).re / 2 =
      iteratedDeriv 1 Xi t ^ 2 - Xi t * iteratedDeriv 2 Xi t := by
  have hformula : ∀ m : ℕ,
      normalJet Xi t m =
        ∑ j ∈ Finset.range (2 * m + 1),
          (-1 : ℝ) ^ (m + j) /
              ((j.factorial : ℝ) * ((2 * m - j).factorial : ℝ)) *
            iteratedDeriv j Xi t * iteratedDeriv (2 * m - j) Xi t := by
    intro m
    unfold normalJet
    rw [even_coefficient_formula]
    simp only [Complex.re_sum, Complex.ofReal_re]
  refine ⟨hformula, ?_, ?_, ?_, ?_⟩
  · simpa [pow_two] using hformula 0
  · have h := hformula 1
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    simp only [iteratedDeriv_one] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := hformula 2
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    simp only [iteratedDeriv_one] at h ⊢
    ring_nf at h ⊢
    exact h
  · rw [PowerSeries.coeff_derivative, PowerSeries.coeff_derivative]
    norm_num
    have h := hformula 1
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    ring_nf at h ⊢
    simpa [normalJet] using h

end D5.S3.Zeros.NormalJetFormula
