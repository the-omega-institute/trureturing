/- GID: D5/S3/FiniteGroups/CosetActions/TransitiveEtaleAction
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/CosetActions/TransitiveEtaleAction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Scalar invariants force a finite étale action to be a coset permutation action. -/

module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.RingTheory.TotallySplit
import OmegaBuild.Commands

/-!
An orbit indicator on the complex points of a finite étale algebra lifts to an
invariant element. If every invariant is scalar, the orbit is all of the points.
Taking the stabilizer gives the equivariant coset algebra used in the argument of
Davydov–Simmons (arXiv:1603.04650), Lemma 2.10 and Corollary 2.13.
-/

compile_only_with_mathlib

public section

set_option autoImplicit false

namespace D5.S3.FiniteGroups.CosetActions.TransitiveEtaleAction

/-- A nontrivial finite étale complex algebra with scalar invariants is the function
algebra of a left coset space. The algebra action becomes pullback by inverse left
translation. -/
theorem exists_coset_algEquiv {G A : Type*} [Group G] [CommRing A] [Nontrivial A]
    [Algebra ℂ A] [Module.Finite ℂ A] [Algebra.Etale ℂ A]
    (ρ : G →* (A ≃ₐ[ℂ] A))
    (hfixed : ∀ a : A, (∀ g : G, ρ g a = a) → ∃ z : ℂ, a = algebraMap ℂ A z) :
    ∃ (K : Subgroup G) (e : A ≃ₐ[ℂ] ((G ⧸ K) → ℂ)),
      ∀ (g : G) (a : A) (q : G ⧸ K), e (ρ g a) q = e a (g⁻¹ • q) := by
  classical
  let X := A →ₐ[ℂ] ℂ
  let : MulAction G X :=
    { smul := fun g p ↦ p.comp (ρ g⁻¹).toAlgHom
      one_smul := fun p ↦ by
        apply AlgHom.ext
        intro a
        change p (ρ ((1 : G)⁻¹) a) = p a
        simp
      mul_smul := fun g h p ↦ by
        apply AlgHom.ext
        intro a
        change p (ρ ((g * h)⁻¹) a) = p (ρ h⁻¹ (ρ g⁻¹ a))
        rw [mul_inv_rev, map_mul, AlgEquiv.mul_apply] }
  let points : X ≃ PrimeSpectrum A := Algebra.IsFiniteSplit.algHomEquivPrimeSpectrum ℂ A
  let split := Algebra.FormallyEtale.equivPiOfIsSepClosed ℂ A
  let eval : A ≃ₐ[ℂ] (X → ℂ) :=
    split.trans (AlgEquiv.piCongrLeft' ℂ (fun _ ↦ ℂ) points.symm)
  have heval (a : A) (p : X) : eval a p = p a := by
    let base : PrimeSpectrum ℂ := ⟨⊥, Ideal.isPrime_bot⟩
    change split a (base.comap p.toRingHom) = p a
    exact (Algebra.FormallyEtale.equivPiOfIsSepClosed_comap p a base).trans
      (Algebra.FormallyEtale.equivPiOfIsSepClosed_self_apply (p a) base)
  have hequiv (g : G) (a : A) (p : X) : eval (ρ g a) p = eval a (g⁻¹ • p) := by
    rw [heval, heval]
    change p (ρ g a) = p (ρ ((g⁻¹)⁻¹) a)
    rw [inv_inv]
  -- Scalar invariants force the indicator of any chosen orbit to be constant.
  let p₀ : X := points.symm (Classical.choice (inferInstance : Nonempty (PrimeSpectrum A)))
  let indicator (p : X) : ℂ := if p ∈ MulAction.orbit G p₀ then 1 else 0
  let a₀ := eval.symm indicator
  have hmem (g : G) (p : X) : g • p ∈ MulAction.orbit G p₀ ↔ p ∈ MulAction.orbit G p₀ := by
    rw [← MulAction.orbit_eq_iff, MulAction.orbit_smul, MulAction.orbit_eq_iff]
  have hfixed₀ (g : G) : ρ g a₀ = a₀ := by
    apply eval.injective
    funext p
    simp only [hequiv, a₀, eval.apply_symm_apply, indicator, hmem]
  obtain ⟨z, hz⟩ := hfixed a₀ hfixed₀
  have hconstant (p : X) : indicator p = z := calc
    indicator p = eval a₀ p := congrFun (eval.apply_symm_apply indicator).symm p
    _ = z := by
      rw [hz, heval]
      exact p.commutes z
  have htrans (p : X) : p ∈ MulAction.orbit G p₀ := by
    by_contra hp
    have hzero : z = 0 := by simpa [indicator, hp] using (hconstant p).symm
    have hone : z = 1 := by
      simpa [indicator, MulAction.mem_orbit_self] using (hconstant p₀).symm
    exact one_ne_zero (hone.symm.trans hzero)
  -- Orbit-stabilizer gives the equivariant coordinates for the function algebra.
  let K := MulAction.stabilizer G p₀
  let coord : G ⧸ K ≃ X :=
    Equiv.ofBijective (MulAction.ofQuotientStabilizer G p₀) <|
      ⟨MulAction.injective_ofQuotientStabilizer G p₀, fun p ↦ by
        obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp (htrans p)
        exact ⟨QuotientGroup.mk g, hg⟩⟩
  refine ⟨K, eval.trans (AlgEquiv.piCongrLeft' ℂ (fun _ ↦ ℂ) coord.symm), ?_⟩
  intro g a q
  change eval (ρ g a) (coord q) = eval a (coord (g⁻¹ • q))
  rw [hequiv, show coord (g⁻¹ • q) = g⁻¹ • coord q from
    MulAction.ofQuotientStabilizer_smul G p₀ g⁻¹ q]

#print axioms exists_coset_algEquiv

end D5.S3.FiniteGroups.CosetActions.TransitiveEtaleAction
