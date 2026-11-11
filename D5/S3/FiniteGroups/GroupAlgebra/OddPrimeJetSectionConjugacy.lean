/- GID: D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetSectionConjugacy
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/GroupAlgebra/OddPrimeJetSectionConjugacy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Weighted semilinear averaging for the section-conjugacy obstruction. -/
import Mathlib.Algebra.Algebra.Operations
import Mathlib.Algebra.Module.BigOperators

/-! A finite weighted trace-one element kills the first obstruction to
splitting conjugacy, without dividing by the order of the acting group. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetSectionConjugacy

theorem weighted_semilinear_cocycle_coboundary
    {Γ K W : Type*} [Group Γ] [Fintype Γ] [Field K]
    [AddCommGroup W] [Module K W]
    (σ : Γ → K →+* K) (ρ : Γ → W →+ W)
    (hσ : ∀ g h a, σ (g * h) a = σ g (σ h a))
    (hsemi : ∀ g a w, ρ g (a • w) = σ g a • ρ g w)
    (θ : K) (hθ : (∑ h : Γ, σ h θ) = 1)
    (f : Γ → W)
    (hcocycle : ∀ g h, f (g * h) = f g + ρ g (f h)) :
    ∃ b : W, ∀ g, f g = b - ρ g b := by
  let b : W := ∑ h : Γ, σ h θ • f h
  refine ⟨b, ?_⟩
  intro g
  have hdiff (h : Γ) : ρ g (f h) = f (g * h) - f g := by
    rw [eq_sub_iff_add_eq]
    rw [add_comm, hcocycle]
  have hsumW (u : Γ → W) :
      (∑ h : Γ, u (g * h)) = ∑ h : Γ, u h := by
    exact Fintype.sum_equiv (Equiv.mulLeft g)
      (fun h => u (g * h)) u (fun _ => rfl)
  have hsumK (u : Γ → K) :
      (∑ h : Γ, u (g * h)) = ∑ h : Γ, u h := by
    exact Fintype.sum_equiv (Equiv.mulLeft g)
      (fun h => u (g * h)) u (fun _ => rfl)
  have hρ :
      ρ g b =
        (∑ h : Γ, σ (g * h) θ • f (g * h)) -
          (∑ h : Γ, σ (g * h) θ) • f g := by
    dsimp [b]
    rw [map_sum]
    simp_rw [hsemi, hdiff, ← hσ, smul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_smul]
  have hρ' : ρ g b = b - f g := by
    rw [hρ]
    rw [hsumW (fun h => σ h θ • f h), hsumK (fun h => σ h θ)]
    simp [b, hθ]
  rw [hρ']
  abel

end D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetSectionConjugacy
