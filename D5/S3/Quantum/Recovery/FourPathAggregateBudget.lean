/- GID: D5/S3/Quantum/Recovery/FourPathAggregateBudget
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/FourPathAggregateBudget
   mirror-E: none(waiver:aggregate-budget)
   anchors: []
   utility: none
   digest: Aggregate certificate and trace-defect budgets for the four-path stability argument. -/

import D5.S3.Quantum.Recovery.FourPathNearestRayComparison
import D5.S3.Quantum.Recovery.FourPathQuadraticMajorant
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

noncomputable section
open scoped BigOperators

namespace D5.S3.Quantum.Recovery.FourPathAggregateBudget
set_option autoImplicit false
set_option linter.style.whitespace false
set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.unusedSimpArgs false

/-- A pointwise certificate gap controls the squared distance to the selected ray. -/
theorem certificate_distance_budget
    {J : Type*} [Fintype J]
    (p q δ : J → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hq : ∀ j, 0 ≤ q j)
    (hδ : ∀ j, min (p j) (q j) ≤ 1600 * δ j) :
    ∑ j, min (p j) (q j) ≤ 1600 * ∑ j, δ j := by
  calc
    ∑ j, min (p j) (q j) ≤ ∑ j, (1600 * δ j) := by
      exact Finset.sum_le_sum (fun j _ => hδ j)
    _ = 1600 * ∑ j, δ j := by rw [Finset.mul_sum]

/-- Under a complete two-coordinate resolution, the quartic ray distance obeys
    the same certificate budget as the quadratic distance. -/
theorem quartic_distance_budget
    {J : Type*} [Fintype J]
    (p q δ : J → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hq : ∀ j, 0 ≤ q j)
    (hsumP : ∑ j, p j = 1) (hsumQ : ∑ j, q j = 1)
    (hδ : ∀ j, min (p j) (q j) ≤ 1600 * δ j) :
    ∑ j, (min (p j) (q j)) ^ 2 ≤ 1600 * ∑ j, δ j := by
  have hple : ∀ j, p j ≤ 1 := by
    intro j
    have h := Finset.single_le_sum (s := Finset.univ) (f := p)
      (fun i _ => hp i) (Finset.mem_univ j)
    simpa [hsumP] using h
  have hqle : ∀ j, q j ≤ 1 := by
    intro j
    have h := Finset.single_le_sum (s := Finset.univ) (f := q)
      (fun i _ => hq i) (Finset.mem_univ j)
    simpa [hsumQ] using h
  have hpoint : ∀ j, (min (p j) (q j)) ^ 2 ≤ min (p j) (q j) := by
    intro j
    have hnon : 0 ≤ min (p j) (q j) := le_min (hp j) (hq j)
    have hle : min (p j) (q j) ≤ 1 := min_le_iff.mpr (Or.inl (hple j))
    nlinarith
  calc
    ∑ j, (min (p j) (q j)) ^ 2 ≤ ∑ j, min (p j) (q j) :=
      Finset.sum_le_sum (fun j _ => hpoint j)
    _ ≤ 1600 * ∑ j, δ j := certificate_distance_budget p q δ hp hq hδ

/-- The two defect budgets imply the numerical square-root budget used by the
    padded Kraus comparison.  This is the exact constant propagation in the
    quantitative stability argument. -/
theorem square_root_budget
    (S_cert S_tr M X ε : ℝ)
    (hcert : 0 ≤ S_cert) (htr : 0 ≤ S_tr) (heps : 0 ≤ ε)
    (hM : M ≤ 1600 * S_cert)
    (hX : X ≤ 4 * S_tr + 9 * M)
    (hbudget : S_cert + S_tr ≤ 8 * ε) :
    2 * Real.sqrt X ≤ 480 * Real.sqrt 2 * Real.sqrt ε := by
  have hXbound : X ≤ 14400 * (S_cert + S_tr) := by
    nlinarith [hM, hX]
  have hfinal : X ≤ 115200 * ε := by nlinarith [hbudget, hXbound]
  have hsqrt : Real.sqrt X ≤ Real.sqrt (115200 * ε) :=
    Real.sqrt_le_sqrt hfinal
  have hconst : Real.sqrt (115200 * ε) = 240 * Real.sqrt 2 * Real.sqrt ε := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 115200)]
    have h115200 : Real.sqrt (115200 : ℝ) = 240 * Real.sqrt 2 := by
      rw [show (115200 : ℝ) = (240 : ℝ)^2 * 2 by norm_num]
      rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (240 : ℝ)^2)]
      simp [Real.sqrt_sq_eq_abs]
    rw [h115200]
  rw [hconst] at hsqrt
  nlinarith

end D5.S3.Quantum.Recovery.FourPathAggregateBudget
