/- GID: D5/S3/Analytic/MultivariateEnergy/Result
   generality: G
   mirror-B: D5/B/S3/Analytic/MultivariateEnergy/Result
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A cubic spherical family refutes the averaged-kernel characterization. -/

import D5.S3.Analytic.MultivariateEnergy.Energy

/-! A positive averaged kernel can coexist with a lower Dirac energy. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open MeasureTheory Matrix
open scoped BigOperators Matrix.Norms.Elementwise

namespace D5.S3.Analytic.MultivariateEnergy.Result
open Defs Moments Energy

private lemma energy_sigma (d : ℕ) [NeZero d] (β : ℝ) :
    energy (familyKernel d β) (sigma d) = 0 := by
  rw [energy_family_eq]
  simp [Q, integral_A_eq_zero]

private lemma energy_dirac (d : ℕ) [NeZero d] (β : ℝ) (e : S d) :
    energy (familyKernel d β) (Measure.dirac e) =
      ((d : ℝ) - 1) / d * (β - ((d : ℝ) - 2) / d) := by
  have hd : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  have hQ : Q (Measure.dirac e) = A e := by
    exact integral_dirac A e
  rw [energy_family_eq, hQ]
  change β * L e e - T e e e = _
  have hn : ‖e.val‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using e.property
  rw [L_eq, T_eq]
  simp only [real_inner_self_eq_norm_sq, hn, one_pow, mul_one]
  field_simp
  ring

/-- In every dimension at least three, the cubic family has a positive averaged kernel
while normalized surface measure fails to minimize the energy. -/
theorem family_refutes (d : ℕ) (hd : 3 ≤ d) (β : ℝ)
    (hβ : 0 < β) (hβupper : β < ((d : ℝ) - 2) / d) :
    IsAdmissible (familyKernel d β) ∧
      IsCondPosDef (avgKernel (familyKernel d β)) ∧
      ¬ IsMinimizer (familyKernel d β) (sigma d) := by
  haveI : NeZero d := ⟨by omega⟩
  refine ⟨isAdmissible_familyKernel_three d β,
    isCondPosDef_family d β hβ.le, ?_⟩
  intro hmin
  obtain ⟨e, he⟩ := (NormedSpace.sphere_nonempty
    (E := EuclideanSpace ℝ (Fin d)) (x := 0)).mpr (by norm_num : (0 : ℝ) ≤ 1)
  let x : S d := ⟨e, he⟩
  have h := hmin (Measure.dirac x) inferInstance
  rw [energy_sigma, energy_dirac] at h
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hp : 0 < ((d : ℝ) - 1) / d := div_pos (by linarith) hdR
  have hn := mul_neg_of_pos_of_neg hp (sub_neg.mpr hβupper)
  linarith

/-- The averaged-kernel characterization fails already for three inputs in dimension three. -/
theorem result : ¬ claim := by
  intro hclaim
  obtain ⟨ha, hc, hn⟩ := family_refutes 3 (by omega) (1 / 10) (by norm_num) (by norm_num)
  exact hn ((hclaim 3 (by omega) 0 (familyKernel 3 (1 / 10)) ha).mpr hc)

end D5.S3.Analytic.MultivariateEnergy.Result
