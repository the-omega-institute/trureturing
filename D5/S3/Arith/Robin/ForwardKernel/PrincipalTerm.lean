/- GID: D5/S3/Arith/Robin/ForwardKernel/PrincipalTerm
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrincipalTerm
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The signed principal Mellin kernel has the classical logarithmic-derivative value. -/

import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

namespace D5.S3.Arith.Robin.ForwardKernel.PrincipalTerm

open Set MeasureTheory Filter
open scoped Topology

noncomputable section

/-- The principal triangular coefficient contributes the full Mangoldt
logarithmic derivative and the subtracted Lebesgue density. -/
theorem principal_signed_tendsto {s : ℂ} (hs : 1 / 2 < s.re) :
    Tendsto (fun b : ℝ =>
      (∑ n ∈ Finset.Icc 0 ⌊b⌋₊,
        (ArithmeticFunction.vonMangoldt n : ℂ) *
          ((1 / 2 : ℂ) * (n : ℂ) ^ (-s - 1 / 2))) -
        ∫ t in (1 : ℝ)..b, (1 / 2 : ℂ) * (t : ℂ) ^ (-s - 1 / 2)) atTop
      (𝓝 (-(1 / 2 : ℂ) *
        (deriv riemannZeta (s + 1 / 2) / riemannZeta (s + 1 / 2)) -
          1 / (2 * (s - 1 / 2)))) := by
  have hs' : 1 < (s + 1 / 2).re := by simp only [Complex.add_re]; norm_num; linarith
  have hsum := (ArithmeticFunction.LSeriesSummable_vonMangoldt hs').hasSum
  have hval := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs'
  let f : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ) *
    ((1 / 2 : ℂ) * (n : ℂ) ^ (-s - 1 / 2))
  have hterm (n : ℕ) :
      (1 / 2 : ℂ) * LSeries.term
          (fun k : ℕ => (ArithmeticFunction.vonMangoldt k : ℂ)) (s + 1 / 2) n = f n := by
    rw [LSeries.term_def₀ (by simp)]
    dsimp [f]
    rw [show -(s + 1 / 2) = -s - 1 / 2 by ring]
    ring
  have hf : HasSum f (-(1 / 2 : ℂ) *
      (deriv riemannZeta (s + 1 / 2) / riemannZeta (s + 1 / 2))) := by
    have h := hsum.mul_left (1 / 2 : ℂ)
    change HasSum _ ((1 / 2 : ℂ) * LSeries
      (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) (s + 1 / 2)) at h
    rw [hval] at h
    convert h.congr_fun (fun n => (hterm n).symm) using 1 <;> ring
  have hnat : Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 0 N, f n) atTop
      (𝓝 (-(1 / 2 : ℂ) *
        (deriv riemannZeta (s + 1 / 2) / riemannZeta (s + 1 / 2)))) := by
    simpa only [Function.comp_def, Nat.range_succ_eq_Icc_zero] using
      hf.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have hp : (-s - 1 / 2).re < -1 := by norm_num; linarith
  have hi := (integrableOn_Ioi_cpow_of_lt hp (by norm_num : (0 : ℝ) < 1)).const_mul
    (1 / 2 : ℂ)
  have hint : (∫ t in Ioi (1 : ℝ), (1 / 2 : ℂ) * (t : ℂ) ^ (-s - 1 / 2)) =
      1 / (2 * (s - 1 / 2)) := by
    rw [integral_const_mul, integral_Ioi_cpow_of_lt hp (by norm_num)]
    have hne : s - 1 / 2 ≠ 0 := by
      intro h
      have he := congrArg Complex.re h
      norm_num at he
      linarith
    have hne' : -s - 1 / 2 + 1 ≠ 0 := by
      have : -s - 1 / 2 + 1 = -(s - 1 / 2) := by ring
      rw [this]
      exact neg_ne_zero.mpr hne
    simp only [Complex.ofReal_one, Complex.one_cpow]
    rw [show -s - 1 / 2 + 1 = -(s - 1 / 2) by ring]
    field_simp [hne]
    <;> ring
  have hlim := intervalIntegral_tendsto_integral_Ioi (1 : ℝ) hi tendsto_id
  rw [hint] at hlim
  exact (hnat.comp tendsto_nat_floor_atTop).sub hlim

#print axioms principal_signed_tendsto

end
end D5.S3.Arith.Robin.ForwardKernel.PrincipalTerm
