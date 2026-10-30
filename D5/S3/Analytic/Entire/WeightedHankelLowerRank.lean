/- GID: D5/S3/Analytic/Entire/WeightedHankelLowerRank
   generality: G
   mirror-B: D5/B/S3/Analytic/Entire/WeightedHankelLowerRank
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Three nearby evaluation points exclude rank below three for every nonzero continuous weighted Hankel kernel. -/

import D5.S3.Analytic.Entire.WeightedHankel
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! A three-point analytic obstruction and the two explicit equality profiles. -/

noncomputable section
open scoped BigOperators
open Filter Topology

namespace D5.S3.Analytic.Entire

private theorem weighted_hankel_symmetric (f : ℂ → ℂ) (z w : ℂ) :
    weightedHankel f z w = weightedHankel f w z := by
  simp only [weightedHankel, add_comm z w]
  ring

private theorem separated_two_evaluation_det {F : ℂ → ℂ → ℂ}
    (hF : SeparatedLE 2 F) (u : Fin 3 → ℂ) :
    Matrix.det (fun i j : Fin 3 => F (u i) (u j)) = 0 := by
  obtain ⟨g, h, _, _, hsep⟩ := hF
  let M : Matrix (Fin 3) (Fin 3) ℂ := fun i j => F (u i) (u j)
  have hm (i j : Fin 3) : M i j = ∑ a, g a (u i) * h a (u j) := hsep _ _
  change M.det = 0
  rw [Matrix.det_fin_three]
  simp only [hm, Fin.sum_univ_two]
  ring

/-- Three nearby evaluations give a nonsingular minor for every nonzero
continuous function, with no growth or polynomial-presentation hypothesis. -/
theorem weighted_hankel_three_point_minor {f : ℂ → ℂ}
    (hf : Continuous f) (hf0 : f ≠ 0) :
    ∃ u : Fin 3 → ℂ,
      (Matrix.of (fun i j => weightedHankel f (u i) (u j))).det ≠ 0 := by
  classical
  obtain ⟨a, ha⟩ : ∃ a : ℂ, f a ≠ 0 := by
    by_contra h
    push_neg at h
    apply hf0
    exact funext h
  let x : ℂ := a / 2
  have hx : f (x + x) ≠ 0 := by
    simpa only [show x + x = a by dsimp [x]; ring] using ha
  have hp : ∀ᶠ t : ℂ in 𝓝 0, f (x + (x + t)) ≠ 0 := by
    apply ContinuousAt.eventually_ne
    · exact hf.continuousAt.comp (continuousAt_const.add
        (continuousAt_const.add continuousAt_id))
    · simpa only [add_zero] using hx
  have hm : ∀ᶠ t : ℂ in 𝓝 0, f (x + (x - t)) ≠ 0 := by
    apply ContinuousAt.eventually_ne
    · exact hf.continuousAt.comp (continuousAt_const.add
        (continuousAt_const.sub continuousAt_id))
    · simpa only [sub_zero] using hx
  have he : ∀ᶠ t : ℂ in 𝓝[≠] 0,
      f (x + (x + t)) ≠ 0 ∧ f (x + (x - t)) ≠ 0 ∧ t ≠ 0 := by
    filter_upwards [hp.filter_mono nhdsWithin_le_nhds,
      hm.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht₁ ht₂ ht₃
    exact ⟨ht₁, ht₂, ht₃⟩
  obtain ⟨t, ht₁, ht₂, ht⟩ := he.exists
  let u : Fin 3 → ℂ := ![x, x + t, x - t]
  let M : Matrix (Fin 3) (Fin 3) ℂ := fun i j => weightedHankel f (u i) (u j)
  have hdiag (i : Fin 3) : M i i = 0 := by simp [M, weightedHankel]
  have hsymm (i j : Fin 3) : M i j = M j i :=
    weighted_hankel_symmetric f _ _
  have hxy : x - (x + t) ≠ 0 := by
    intro h
    apply ht
    linear_combination -h
  have hxz : x - (x - t) ≠ 0 := by
    intro h
    apply ht
    linear_combination h
  have hyz : (x + t) - (x - t) ≠ 0 := by
    intro h
    apply ht
    linear_combination h / 2
  have h01 : M 0 1 ≠ 0 := by
    exact mul_ne_zero (pow_ne_zero 2 hxy) ht₁
  have h02 : M 0 2 ≠ 0 := by
    exact mul_ne_zero (pow_ne_zero 2 hxz) ht₂
  have h12 : M 1 2 ≠ 0 := by
    change ((x + t) - (x - t)) ^ 2 * f ((x + t) + (x - t)) ≠ 0
    rw [show (x + t) + (x - t) = x + x by ring]
    exact mul_ne_zero (pow_ne_zero 2 hyz) hx
  have hdet : M.det = 2 * M 0 1 * M 0 2 * M 1 2 := by
    rw [Matrix.det_fin_three]
    rw [hdiag 0, hdiag 1, hdiag 2, hsymm 1 0, hsymm 2 0, hsymm 2 1]
    ring
  have hdet0 : M.det ≠ 0 := by
    rw [hdet]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) h01) h02) h12
  exact ⟨u, hdet0⟩

/-- No nonzero continuous function has a quadratic weighted Hankel kernel
with at most two separated entire terms. The local three-point construction
does not require a growth bound, a polynomial presentation, or finite support. -/
theorem not_separated_two_weighted_hankel {f : ℂ → ℂ}
    (hf : Continuous f) (hf0 : f ≠ 0) :
    ¬ SeparatedLE 2 (weightedHankel f) := by
  obtain ⟨u, hu⟩ := weighted_hankel_three_point_minor hf hf0
  intro hsep
  exact hu (separated_two_evaluation_det hsep u)

#print axioms not_separated_two_weighted_hankel

/-- A squared difference has three entire separated terms. This helper is
consumed by both equality profiles below. -/
private theorem separated_three_squared_difference
    (p e : ℂ → ℂ) (hp : Differentiable ℂ p) (he : Differentiable ℂ e) (c : ℂ) :
    SeparatedLE 3 (fun z w => c * e z * e w * (p z - p w) ^ 2) := by
  classical
  refine ⟨![fun z => c * e z * (p z) ^ 2,
      fun z => (-2 : ℂ) * c * e z * p z, fun z => c * e z],
    ![e, fun w => e w * p w, fun w => e w * (p w) ^ 2], ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact (he.const_mul c).mul (hp.pow 2)
    · exact ((he.const_mul ((-2 : ℂ) * c)).mul hp)
    · exact he.const_mul c
  · intro i
    fin_cases i
    · exact he
    · exact he.mul hp
    · exact he.mul (hp.pow 2)
  · intro z w
    simp only [Fin.sum_univ_three]
    dsimp [Matrix.vecHead, Matrix.vecTail]
    ring

/-- Arbitrary complex exponential profiles admit three entire separated
terms. The actual-channel consumer retains the exact term count. -/
theorem separated_three_exponential (c α : ℂ) :
    SeparatedLE 3 (weightedHankel (fun z => c * Complex.exp (α * z))) := by
  have h := separated_three_squared_difference (fun z => z)
    (fun z => Complex.exp (α * z)) differentiable_id
    (Complex.differentiable_exp.comp (differentiable_id.const_mul α)) c
  convert h using 1
  funext z w
  simp only [weightedHankel, mul_add, Complex.exp_add]
  ring

/-- The shifted-square profile has three entire separated terms for every
complex exponent, coefficient and shift. -/
theorem separated_three_exponential_square (c α β : ℂ) :
    SeparatedLE 3
      (weightedHankel (fun z => c * Complex.exp (α * z) * (z - β) ^ 2)) := by
  have h := separated_three_squared_difference (fun z => z ^ 2 - β * z)
    (fun z => Complex.exp (α * z))
    ((differentiable_id.pow 2).sub (differentiable_id.const_mul β))
    (Complex.differentiable_exp.comp (differentiable_id.const_mul α)) c
  convert h using 1
  funext z w
  simp only [weightedHankel, mul_add, Complex.exp_add]
  ring

#print axioms separated_three_exponential
#print axioms separated_three_exponential_square

end D5.S3.Analytic.Entire
