/- GID: D5/S3/Weil/GroundMode/ProjectiveModeSymmetry
   generality: G
   mirror-B: D5/B/S3/Weil/GroundMode/ProjectiveModeSymmetry
   mirror-E: none(waiver:operator-domain-symmetry-with-explicit-realization)
   anchors: []
   digest: Derive uniqueness and symmetry of the actual projectively normalized eigenvector from candidate-orthogonal coercivity. -/

import D5.S3.Weil.ZetaBridge.WeilProjectiveRayleighCapture

/-!
# Symmetry of a projectively normalized mode

A real/even candidate does not make an arbitrary nearby vector real/even.
The eigenvalue equation and full candidate-orthogonal coercivity supply the
missing implication. We work on the actual linear operator domain, so no
bounded extension, spectral decomposition or prior simplicity is required.

The semilinear statement covers conjugation and ordinary linear reflection.
Actual commutation and inner-product compatibility of those operations with
the Weil form/domain must still be proved by their respective realizations.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Weil.GroundMode.ProjectiveModeSymmetry

open scoped InnerProductSpace
open D5.S3.Weil.ZetaBridge.WeilProjectiveRayleighCapture

variable {H D : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [AddCommGroup D] [Module ℂ D]

/-- Candidate normalization fixes the entire eigenspace below the orthogonal
threshold. Equality is in the Hilbert space; injectivity of the domain map
is unnecessary. -/
theorem normalized_eigenvectors_unique
    (ι A : D →ₗ[ℂ] H) (k p q : D) (lam threshold : ℝ)
    (hp : A p = (lam : ℂ) • ι p) (hq : A q = (lam : ℂ) • ι q)
    (hkp : ⟪ι k, ι p⟫_ℂ = 1) (hkq : ⟪ι k, ι q⟫_ℂ = 1)
    (hgap : lam < threshold)
    (hcoercive : ∀ f : D, ⟪ι k, ι f⟫_ℂ = 0 →
      threshold * ‖ι f‖ ^ 2 ≤ (⟪ι f, A f⟫_ℂ).re) :
    ι p = ι q := by
  by_contra hne
  have hnonzero : ι (p - q) ≠ 0 := by
    rw [map_sub, sub_ne_zero]
    exact hne
  have heigen : A (p - q) = (lam : ℂ) • ι (p - q) := by
    rw [map_sub, map_sub, hp, hq, smul_sub]
  have hoverlap := eigen_overlap_ne_zero ι A k (p - q) lam threshold
    hnonzero heigen hgap hcoercive
  apply hoverlap
  rw [map_sub, inner_sub_right, hkp, hkq, sub_self]

/-- A normalized eigenvector is fixed by a compatible semilinear symmetry
which fixes the candidate and the selected real eigenvalue. Taking sigma to
be conjugation yields reality; taking sigma to be identity yields parity. -/
theorem normalized_mode_fixed_by_semilinear_symmetry
    (ι A : D →ₗ[ℂ] H) (k p : D) (lam threshold : ℝ)
    (hp : A p = (lam : ℂ) • ι p) (hkp : ⟪ι k, ι p⟫_ℂ = 1)
    (hgap : lam < threshold)
    (hcoercive : ∀ f : D, ⟪ι k, ι f⟫_ℂ = 0 →
      threshold * ‖ι f‖ ^ 2 ≤ (⟪ι f, A f⟫_ℂ).re)
    (sigma : ℂ →+* ℂ) (J : D →ₛₗ[sigma] D) (C : H →ₛₗ[sigma] H)
    (hlam : sigma (lam : ℂ) = (lam : ℂ))
    (hι : ∀ f : D, ι (J f) = C (ι f))
    (hA : ∀ f : D, A (J f) = C (A f))
    (hinner : ∀ x y : H, ⟪C x, C y⟫_ℂ = sigma ⟪x, y⟫_ℂ)
    (hk : J k = k) : C (ι p) = ι p := by
  have hCk : C (ι k) = ι k := by rw [← hι k, hk]
  have hJp : A (J p) = (lam : ℂ) • ι (J p) := by
    rw [hA, hp, map_smulₛₗ, hlam, hι]
  have hkJp : ⟪ι k, ι (J p)⟫_ℂ = 1 := by
    rw [hι, ← hCk, hinner, hkp, map_one]
  have hu := normalized_eigenvectors_unique ι A k (J p) p lam threshold
    hJp hp hkJp hkp hgap hcoercive
  simpa only [hι] using hu

/-- The existing nonzero-overlap theorem constructs the normalization used
by the symmetry theorem. Thus symmetry is obtained for the actual selected
eigenvector, not postulated for an error-ball surrogate. -/
theorem projective_eigenmode_fixed_by_semilinear_symmetry
    (ι A : D →ₗ[ℂ] H) (k u : D) (lam threshold : ℝ)
    (hu : ι u ≠ 0) (heigen : A u = (lam : ℂ) • ι u)
    (hgap : lam < threshold)
    (hcoercive : ∀ f : D, ⟪ι k, ι f⟫_ℂ = 0 →
      threshold * ‖ι f‖ ^ 2 ≤ (⟪ι f, A f⟫_ℂ).re)
    (sigma : ℂ →+* ℂ) (J : D →ₛₗ[sigma] D) (C : H →ₛₗ[sigma] H)
    (hlam : sigma (lam : ℂ) = (lam : ℂ))
    (hι : ∀ f : D, ι (J f) = C (ι f))
    (hA : ∀ f : D, A (J f) = C (A f))
    (hinner : ∀ x y : H, ⟪C x, C y⟫_ℂ = sigma ⟪x, y⟫_ℂ)
    (hk : J k = k) :
    let p := ι ((⟪ι k, ι u⟫_ℂ)⁻¹ • u)
    C p = p := by
  let alpha := ⟪ι k, ι u⟫_ℂ
  let p : D := alpha⁻¹ • u
  have ha : alpha ≠ 0 := eigen_overlap_ne_zero ι A k u lam threshold
    hu heigen hgap hcoercive
  have hp : A p = (lam : ℂ) • ι p := by
    simp only [p, map_smul, heigen, smul_smul]
    rw [mul_comm (alpha⁻¹) (lam : ℂ)]
  have hkp : ⟪ι k, ι p⟫_ℂ = 1 := by
    rw [show ι p = alpha⁻¹ • ι u by simp only [p, map_smul], inner_smul_right]
    exact inv_mul_cancel₀ ha
  exact normalized_mode_fixed_by_semilinear_symmetry ι A k p lam threshold
    hp hkp hgap hcoercive sigma J C hlam hι hA hinner hk

#print axioms normalized_eigenvectors_unique
#print axioms normalized_mode_fixed_by_semilinear_symmetry
#print axioms projective_eigenmode_fixed_by_semilinear_symmetry

end D5.S3.Weil.GroundMode.ProjectiveModeSymmetry
end
