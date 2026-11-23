/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/MiddleTailBernstein
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Bernstein comparison after eliminating the central upper gap. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.MiddleTailGapElimination
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.ShortGapSeries
import Mathlib.Tactic.ComputeDegree

/-! The coefficient signs certify the original mixed derivative on the full gap band. -/

open Polynomial

namespace RefinedBMV.PositiveCenter

open D5.S3.Analytic.SeriesInequalities.LorentzLowDegreeCoefficientRemainder

open private geometricValue geometricDerivative lossValue lossDerivative from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.MiddleTailJointScore

/-- Upper bound for the slope used to transport the gap to the unit interval. -/
noncomputable def middleTailSlopeCutoff (h : ℝ) : ℝ := 4 / 13 - h / 2 + 13 * h ^ 2 / 48

private noncomputable def constant (x : ℝ) : ℂ[X] := Polynomial.C (x : ℂ)

/-- Polynomials in the slope rescaled to the unit interval. -/
noncomputable def middleTailBernsteinPolynomials (h u : ℝ) : ℂ[X] × ℂ[X] × ℂ[X] × ℂ[X] :=
  let F := upperTailGap h u
  let x := Real.exp (-u)
  let n := 3 + h
  let k := 3 + 2 * h
  let c := n * k / 2
  let W := shortGapWeight h u
  let S := 2 * F * W
  let H := (1 + h) * F * (k * F - 4) + 2 - 2 * (F + 1) * Real.exp (-(k * u))
  let q := constant (middleTailSlopeCutoff h) * X
  let r := constant h + q
  let A := constant n + constant (k * F - 1) * q
  let R := 1 + constant F * q
  let ρ := constant x * R
  let ell := 1 - q
  let η := q * r
  let Z := (2 + h) * S - H
  let M := (constant Z + q * constant S) * constant (lossValue h u) +
    constant (S * lossDerivative h u)
  let U := constant (Z * geometricValue h u + S * geometricDerivative h u) - r * M
  let V := η * (M + r * constant (S * lossValue h u))
  let C := constant H * (1 - ρ) ^ 2 - ell * constant S * (1 - ρ ^ 2)
  let T := constant c * R * U - A * V
  let P := (constant c * R - A * (1 + r)) * C +
    A * η * (constant S * (1 - ρ ^ 2) -
      constant (2 * F * x) * (constant H * (1 - ρ) - constant S * ell * ρ))
  let β := (31 / 800 : ℝ) * (13 / 4) ^ 4
  let N := constant c * P - constant (2 * β) * q ^ 5 * T + constant (c * S / 2000) * A
  (-C, U, T, -N)

private theorem middleTailBernstein_degrees (h u : ℝ) :
    let P := middleTailBernsteinPolynomials h u
    P.1.natDegree ≤ 3 ∧ P.2.1.natDegree ≤ 2 ∧
      P.2.2.1.natDegree ≤ 4 ∧ P.2.2.2.natDegree ≤ 9 := by
  dsimp only [middleTailBernsteinPolynomials, constant]
  constructor
  · compute_degree
  constructor
  · compute_degree
  constructor <;> compute_degree

private theorem middleTailBernstein_values (h u s : ℝ) :
    let P := middleTailBernsteinPolynomials h u
    let B := middleTailGapPolynomials h u (middleTailSlopeCutoff h * s)
    (P.1.eval (s : ℂ)).re = -B.upperSlopeCoefficient ∧
      (P.2.1.eval (s : ℂ)).re = B.linearLoss ∧
      (P.2.2.1.eval (s : ℂ)).re = B.decayCoefficient ∧
      (P.2.2.2.eval (s : ℂ)).re = -B.numerator := by
  simp only [middleTailBernsteinPolynomials, middleTailGapPolynomials, constant,
    eval_add, eval_sub, eval_mul, eval_pow, eval_neg, eval_one, eval_C, eval_X,
    ← Complex.ofReal_one, ← Complex.ofReal_add, ← Complex.ofReal_sub, ← Complex.ofReal_mul,
    ← Complex.ofReal_neg, ← Complex.ofReal_pow, Complex.ofReal_re]
  exact ⟨trivial, trivial, by ring, by ring⟩

/-- A common positive lower bound on the four Bernstein coefficient lists
implies the exact real signs. -/
theorem middleTailGap_signs_of_bernstein {h u q eps : ℝ}
    (hq₀ : 0 ≤ q) (hq₁ : q ≤ middleTailSlopeCutoff h) (hQ : 0 < middleTailSlopeCutoff h)
    (he : 0 < eps)
    (hcoeff :
      let P := middleTailBernsteinPolynomials h u
      (∀ i ≤ 3, eps ≤ (bernsteinCoefficient 3 i P.1).re) ∧
      (∀ i ≤ 2, eps ≤ (bernsteinCoefficient 2 i P.2.1).re) ∧
      (∀ i ≤ 4, eps ≤ (bernsteinCoefficient 4 i P.2.2.1).re) ∧
      (∀ i ≤ 9, eps ≤ (bernsteinCoefficient 9 i P.2.2.2).re)) :
    let B := middleTailGapPolynomials h u q
    B.upperSlopeCoefficient < 0 ∧ 0 < B.linearLoss ∧
      0 < B.decayCoefficient ∧ B.numerator < 0 := by
  let s := q / middleTailSlopeCutoff h
  have hs₀ : 0 ≤ s := div_nonneg hq₀ hQ.le
  have hs₁ : s ≤ 1 := (div_le_iff₀ hQ).mpr (by simpa using hq₁)
  have hqs : middleTailSlopeCutoff h * s = q := by
    dsimp only [s]
    field_simp [hQ.ne']
  obtain ⟨hC, hU, hT, hN⟩ := middleTailBernstein_degrees h u
  obtain ⟨hc, hu, ht, hn⟩ := hcoeff
  obtain ⟨vC,vU,vT,vN⟩ := middleTailBernstein_values h u s
  rw [hqs] at vC vU vT vN
  have bC := bernstein_eval_re_lower hC hs₀ hs₁ hc
  have bU := bernstein_eval_re_lower hU hs₀ hs₁ hu
  have bT := bernstein_eval_re_lower hT hs₀ hs₁ ht
  have bN := bernstein_eval_re_lower hN hs₀ hs₁ hn
  rw [vC] at bC
  rw [vU] at bU
  rw [vT] at bT
  rw [vN] at bN
  exact ⟨by linarith only [bC, he], he.trans_le bU, he.trans_le bT, by linarith only [bN, he]⟩

end RefinedBMV.PositiveCenter
