/- GID: D5/S3/VertexAlgebra/TwistedGround/ActualOddGradeOrthogonality
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/ActualOddGradeOrthogonality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous]
   utility: none
   digest: The original chosen twisted tensor form pairs distinct signed odd degrees to zero. -/

import D5.S3.VertexAlgebra.TwistedGround.ActualChargedAdjoint
import D5.S3.VertexAlgebra.LatticeHalfFockGradedTrace
import D5.S3.Quantum.Algebra.WeightedPolynomialSubstitution

/-!
The form, its Classical.choice ground factor, the oscillator and the zero mode
are the original ones. The eigenvector hypotheses use the existing actual
zero mode, allowing all integer odd degrees without a replacement grading.
Same-mode colour substitution preserves odd weight. The old factorial Wick
coordinates then have disjoint support in different degrees, independently of
the ground factor. No ground symmetry, positivity or new pairing is needed.
This is classical graded Wick orthogonality, with no literature novelty claim.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators TensorProduct

namespace D5.S3.VertexAlgebra.TwistedGround.ActualOddGradeOrthogonality

open LatticeGeneratingFieldLocality LatticeHalfFock MvPolynomial
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockChargedCoefficients
open LatticeHalfFockGradedTrace SignedOscillatorWick ActualChargedAdjoint
open D5.S3.Quantum.Algebra.WeightedPolynomialSubstitution

private theorem substitution_monomial_homogeneous (D : LatticeData)
    (A : ℕ → Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (d : OddMonomial D) (c : ℂ) :
    IsWeightedHomogeneous (omega D)
      (OriginalCurrentMetric.substitution A (monomial d c)) (oddWeight D d) := by
  classical
  have hX (i : Index D) : IsWeightedHomogeneous (omega D)
      (OriginalCurrentMetric.variableImage A i) (omega D i) := by
    rw [OriginalCurrentMetric.variableImage]
    apply IsWeightedHomogeneous.sum
    intro j _
    exact (weightedHomogeneousSubmodule ℂ (omega D) (omega D i)).smul_mem _
      (by
        change IsWeightedHomogeneous (omega D) (X (j, i.2)) (omega D i)
        simpa only [omega] using isWeightedHomogeneous_X ℂ (omega D) (j, i.2))
  have h := eval2_totalWeight (omega D) (omega D)
    (fun i => Polynomial.C (OriginalCurrentMetric.variableImage A i))
    (fun i => HasTotalWeight.C (hX i)) (monomial d c) (oddWeight D d)
    (isWeightedHomogeneous_monomial _ _ _ rfl)
  have hC : Polynomial.C (OriginalCurrentMetric.substitution A (monomial d c)) =
      MvPolynomial.eval₂ (algebraMap ℂ (Polynomial (Oscillator D)))
        (fun i => Polynomial.C (OriginalCurrentMetric.variableImage A i))
        (monomial d c) := by
    change Polynomial.C (MvPolynomial.eval₂ (algebraMap ℂ (Oscillator D))
      (OriginalCurrentMetric.variableImage A) (monomial d c)) = _
    rw [MvPolynomial.eval₂_comp_left]
    rfl
  rw [← hC] at h
  intro m hm
  simpa only [Nat.add_zero] using h 0 m (by
    simpa only [Polynomial.coeff_C_zero] using hm)

private theorem wick_monomial_orthogonal (D : LatticeData) (d e : OddMonomial D)
    (hne : oddWeight D d ≠ oddWeight D e) :
    wick D (monomial d 1) (monomial e 1) = 0 := by
  classical
  let p := OriginalCurrentMetric.substitution
    (fun k => (-frequency (k : ℤ)) • gramComplex D) (monomial d (1 : ℂ))
  have hp : IsWeightedHomogeneous (omega D) p (oddWeight D d) :=
    substitution_monomial_homogeneous D _ d 1
  change ((basisMonomials (Index D) ℂ).constr ℂ
    (fun m => (FactorialFockMetric.weight m : ℂ) • MvPolynomial.lcoeff ℂ m))
      p (monomial e 1) = 0
  rw [Module.Basis.constr_apply]
  simp only [Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro m hm
  have hme : e ≠ m := by
    intro he
    subst m
    have hw := hp (Finsupp.mem_support_iff.mp hm)
    exact hne hw.symm
  simp [MvPolynomial.lcoeff, MvPolynomial.coeff_monomial, hme]

private theorem degree_of_eigen_support (D : LatticeData) (hu : IsUnit D.G.det)
    (u : ℤ) (x : ActualTensor D hu)
    (hx : actualTensorL0 D hu x = ((D.rank : ℂ) / 16 + (u : ℂ) / 2) • x)
    (i : OddMonomial D × LatticeTwistedGroundRealization.Half (groundRank D hu))
    (hi : i ∈ ((actualAmbientBasis D hu).repr x).support) :
    (oddWeight D i.1 : ℤ) = u := by
  have h := congrArg (fun z => (actualAmbientBasis D hu).repr z i) hx
  rw [actualTensorL0_repr] at h
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul] at h
  have hs := mul_right_cancel₀ (Finsupp.mem_support_iff.mp hi) h
  have hc : (oddWeight D i.1 : ℂ) = (u : ℂ) := by
    linear_combination 2 * hs
  exact_mod_cast hc

/-- The unchanged actual bilinear form annihilates different integer odd-degree
eigenspaces of the original tensor zero mode. The ordered ground slots are
retained; in particular, no symmetry of the chosen ground form is assumed. -/
theorem actualForm_oddGrade_orthogonal (D : LatticeData) (hu : IsUnit D.G.det)
    (u v : ℤ) (x y : ActualTensor D hu)
    (hx : actualTensorL0 D hu x = ((D.rank : ℂ) / 16 + (u : ℂ) / 2) • x)
    (hy : actualTensorL0 D hu y = ((D.rank : ℂ) / 16 + (v : ℂ) / 2) • y)
    (hne : u ≠ v) : actualForm D hu x y = 0 := by
  classical
  let b := actualAmbientBasis D hu
  have hxi := degree_of_eigen_support D hu u x hx
  have hyj := degree_of_eigen_support D hu v y hy
  rw [← b.linearCombination_repr x, ← b.linearCombination_repr y]
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum,
    LinearMap.sum_apply, map_smul, LinearMap.smul_apply]
  apply Finset.sum_eq_zero
  intro j hj
  apply smul_eq_zero.mpr
  right
  apply Finset.sum_eq_zero
  intro i hi
  have hw : wick D (monomial i.1 1) (monomial j.1 1) = 0 := by
    apply wick_monomial_orthogonal D i.1 j.1
    intro he
    apply hne
    exact (hxi i hi).symm.trans ((congrArg (Int.ofNat) he).trans (hyj j hj))
  have hb : actualForm D hu (b i) (b j) = 0 := by
    rw [show b i = monomial i.1 1 ⊗ₜ[ℂ] Pi.single i.2 1 from
      actual_basis_apply D hu i.1 i.2]
    rw [show b j = monomial j.1 1 ⊗ₜ[ℂ] Pi.single j.2 1 from
      actual_basis_apply D hu j.1 j.2]
    unfold actualForm
    change _ * wick D (monomial i.1 1) (monomial j.1 1) = 0
    rw [hw, mul_zero]
  simp only [hb, smul_zero]

end D5.S3.VertexAlgebra.TwistedGround.ActualOddGradeOrthogonality
