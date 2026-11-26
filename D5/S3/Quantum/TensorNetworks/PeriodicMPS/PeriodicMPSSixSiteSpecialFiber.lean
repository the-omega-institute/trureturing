/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteSpecialFiber
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteSpecialFiber
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteElimination]
   utility: none
   digest: A specified adjacent marginal restricts the six-site periodic state to two rays. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteElimination

/-! The special nilpotent marginal of a six-site periodic binary bond-two state. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSSixSiteSpecialFiber

open PeriodicMPSSixSiteCoordinates PeriodicMPSSixSiteMarginal
open PeriodicMPSSixSiteInvariants PeriodicMPSSixSiteElimination
open PeriodicMPSParentIntersection (Bond)
open UniformMPSExpectedDimensionRefutation (traceWord)
open scoped ComplexConjugate

/-- Common amplitude multiplication scales the marginal by its squared modulus. -/
theorem gram_scale (p : Fin 14 → ℂ) (a : ℂ) :
    gram (a • p) = Complex.normSq a • gram p := by
  have hf : flatten (a • p) = a • flatten p := by
    ext i j
    rfl
  rw [gram, hf, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [show a * star a = ↑(Complex.normSq a) from Complex.mul_conj a]
  rfl

/-- Second phase for the two actual rays over the chosen observation. -/
noncomputable def secondPhase : ℂ := (19 - 34 * Complex.I) / (19 + 34 * Complex.I)

/-- The chosen observation on the nilpotent chart forces one of two phase-fixed pairs. -/
theorem specialChart {x y : ℂ} {g : ℝ}
    (h : g • gram (nilpotentRay x y) = gram (nilpotentRay 1 Complex.I)) :
    (x = 1 ∧ y = Complex.I) ∨ (x = secondPhase ∧ y = x * (-Complex.I)) := by
  let t := Complex.normSq (y - 5 * x)
  obtain ⟨hy, hx, hxy⟩ := specialFiber_unique
    (Complex.normSq_nonneg y) (Complex.normSq_nonneg (y - 5 * x))
    (show t = _ from (projectedInvariant_eq x y).symm)
    (specialEquation_eq_zero h 0) (specialEquation_eq_zero h 1) (specialEquation_eq_zero h 2)
  exact special_chart_of_invariants h hx hy hxy

private theorem target_corner : gram (nilpotentRay 1 Complex.I) 3 3 = 0 := by
  rw [nilpotentRay]
  exact (independent_gram _ _ _ _ _).2.2.2.2

private theorem target_singleton : gram (nilpotentRay 1 Complex.I) 1 1 = 15 := by
  rw [nilpotentRay, (independent_gram _ _ _ _ _).2.2.1]
  apply Complex.ext <;>
    norm_num [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.add_re,
      Complex.add_im, pow_succ]

/-- Every actual core matching the special marginal up to a real gain has one
of the two listed necklace rays. -/
theorem actual_specialFiber {g : ℝ} (A : Fin 2 → Bond) (hne : traceWord 2 2 6 A ≠ 0)
    (h : g • gram (traceWord 2 2 6 A ∘ necklaces) = gram (nilpotentRay 1 Complex.I)) :
    ∃ a : ℂ, a ≠ 0 ∧
      (traceWord 2 2 6 A ∘ necklaces = a • nilpotentRay 1 Complex.I ∨
       traceWord 2 2 6 A ∘ necklaces = a • nilpotentRay secondPhase
          (secondPhase * (-Complex.I))) := by
  have h11 := congrArg (fun G : Matrix (Fin 4) (Fin 4) ℂ => G 1 1) h
  rw [Matrix.smul_apply, target_singleton] at h11
  have hg : g ≠ 0 := by
    intro hzero
    rw [hzero, zero_smul] at h11
    norm_num at h11
  have h11ne : gram (traceWord 2 2 6 A ∘ necklaces) 1 1 ≠ 0 := by
    intro hzero
    rw [hzero, smul_zero] at h11
    norm_num at h11
  have h33 := congrArg (fun G : Matrix (Fin 4) (Fin 4) ℂ => G 3 3) h
  rw [Matrix.smul_apply, target_corner] at h33
  have h33zero := (smul_eq_zero.mp h33).resolve_left hg
  obtain ⟨x, y, a, ha, hr⟩ := exists_nilpotentRay A hne h33zero h11ne
  rw [hr, gram_scale, smul_smul] at h
  rcases specialChart h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨a, ha, Or.inl hr⟩
  · exact ⟨a, ha, Or.inr hr⟩

/-- Every point of the nilpotent chart admits an actual periodic bond-two presentation. -/
theorem nilpotentRay_realized (x y : ℂ) :
    ∃ A : Fin 2 → Bond, traceWord 2 2 6 A ∘ necklaces = nilpotentRay x y := by
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq x (n := 2) (by decide)
  obtain ⟨A, hA, hB, hd, he, hk⟩ :=
    PeriodicMPSFiveSiteCoordinates.exists_trace_coordinates t 0 y 0 1
  refine ⟨A, ?_⟩
  rw [trace_word_necklaces, hA, hB, hd, he, hk, ht, mul_zero, zero_pow (by decide : 2 ≠ 0)]
  rw [nilpotent_coordinates]
  simp [nilpotentRay, independentSlice]

private theorem gram_independent_matrix (a b c d e : ℂ) :
    gram (independentSlice a b c d e) =
      let r := a * conj a + 4 * (b * conj b) + 2 * (c * conj c) + d * conj d
      let s := a * conj b + 2 * (b * conj c) + b * conj d + c * conj e
      let t := b * conj b + 2 * (c * conj c) + d * conj d + e * conj e
      let u := b * conj b + c * conj d + d * conj c
      !![r, s, s, 0; conj s, t, u, 0; conj s, u, t, 0; 0, 0, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gram, flatten, independentSlice, necklaceTable, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_succ, map_ofNat] <;> ring

private theorem secondPhase_cartesian :
    secondPhase = (-(795 / 1517 : ℝ) : ℂ) - (1292 / 1517 : ℝ) * Complex.I := by
  unfold secondPhase
  apply Complex.ext <;>
    norm_num [Complex.div_re, Complex.div_im, Complex.normSq_apply, Complex.mul_re,
      Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im]

set_option maxHeartbeats 2000000 in
-- Normalize the real and imaginary parts of the explicit matrix entries.
/-- Both listed rays reproduce the entire adjacent two-site observation. -/
theorem secondPhase_same_gram :
    gram (nilpotentRay secondPhase (secondPhase * (-Complex.I))) =
      gram (nilpotentRay 1 Complex.I) := by
  rw [secondPhase_cartesian]
  unfold nilpotentRay
  rw [gram_independent_matrix, gram_independent_matrix]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im,
      Complex.div_re, Complex.div_im, Complex.normSq_apply, map_ofNat, pow_succ]

/-- The two phase-fixed representatives lie on distinct complex rays. -/
theorem distinct_specialRays (a : ℂ) :
    nilpotentRay secondPhase (secondPhase * (-Complex.I)) ≠ a • nilpotentRay 1 Complex.I := by
  intro h
  have ha : (1 : ℂ) = a * 1 := congrFun h 9
  have hphase : secondPhase = a * 1 := congrFun h 5
  rw [← ha, secondPhase_cartesian] at hphase
  have hre := congrArg Complex.re hphase
  norm_num [Complex.sub_re, Complex.mul_re] at hre

end D5.S3.Quantum.TensorNetworks.PeriodicMPSSixSiteSpecialFiber
