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

/-! The same weighted average solves the additive associativity defect that
appears when arbitrary quotient representatives have not yet been corrected
to a section. This is the degree-by-degree obstruction identity used by the
principal-unit lifting argument. -/
theorem weighted_semilinear_associativity_defect
    {Γ K W : Type*} [Group Γ] [Fintype Γ] [Field K]
    [AddCommGroup W] [Module K W]
    (σ : Γ → K →+* K) (ρ : Γ → W →+ W)
    (hσ : ∀ g h a, σ (g * h) a = σ g (σ h a))
    (hsemi : ∀ g a w, ρ g (a • w) = σ g a • ρ g w)
    (θ : K) (hθ : (∑ h : Γ, σ h θ) = 1)
    (c : Γ → Γ → W)
    (hassoc : ∀ g h k, c g h + c (g * h) k = ρ g (c h k) + c g (h * k)) :
    ∀ g h,
      c g h + (∑ k : Γ, σ ((g * h) * k) θ • c (g * h) k) =
        ρ g (∑ k : Γ, σ (h * k) θ • c h k) +
          (∑ k : Γ, σ (g * k) θ • c g k) := by
  intro g h
  have hsumK (r : Γ) (u : Γ → K) :
      (∑ k : Γ, u (r * k)) = ∑ k : Γ, u k := by
    exact Fintype.sum_equiv (Equiv.mulLeft r)
      (fun k => u (r * k)) u (fun _ => rfl)
  have hsumW (r : Γ) (u : Γ → W) :
      (∑ k : Γ, u (r * k)) = ∑ k : Γ, u k := by
    exact Fintype.sum_equiv (Equiv.mulLeft r)
      (fun k => u (r * k)) u (fun _ => rfl)
  have hweight : (∑ k : Γ, σ ((g * h) * k) θ) = 1 := by
    calc
      (∑ k : Γ, σ ((g * h) * k) θ) = ∑ k : Γ, σ k θ :=
        hsumK (g * h) (fun k => σ k θ)
      _ = 1 := hθ
  have hleft :
      (∑ k : Γ, σ ((g * h) * k) θ • c g h) = c g h := by
    rw [← Finset.sum_smul, hweight, one_smul]
  have hrho :
      (∑ k : Γ, σ ((g * h) * k) θ • ρ g (c h k)) =
        ρ g (∑ k : Γ, σ (h * k) θ • c h k) := by
    calc
      (∑ k : Γ, σ ((g * h) * k) θ • ρ g (c h k)) =
          ∑ k : Γ, ρ g (σ (h * k) θ • c h k) := by
            apply Finset.sum_congr rfl
            intro k hk
            rw [hsemi, ← hσ]
            simp [mul_assoc]
      _ = ρ g (∑ k : Γ, σ (h * k) θ • c h k) := by
        rw [map_sum]
  have hlast :
      (∑ k : Γ, σ ((g * h) * k) θ • c g (h * k)) =
        ∑ k : Γ, σ (g * k) θ • c g k := by
    simpa [mul_assoc] using
      hsumW h (fun k => σ (g * k) θ • c g k)
  have hsummed :
      (∑ k : Γ, σ ((g * h) * k) θ •
          (c g h + c ((g * h)) k)) =
        ∑ k : Γ, σ ((g * h) * k) θ •
          (ρ g (c h k) + c g (h * k)) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [hassoc]
  have hsummed' :
      (∑ k : Γ, σ ((g * h) * k) θ • c g h) +
          (∑ k : Γ, σ ((g * h) * k) θ • c ((g * h)) k) =
        (∑ k : Γ, σ ((g * h) * k) θ • ρ g (c h k)) +
          (∑ k : Γ, σ ((g * h) * k) θ • c g (h * k)) := by
    simpa only [smul_add, Finset.sum_add_distrib] using hsummed
  rw [hleft, hrho, hlast] at hsummed'
  exact hsummed'

end D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetSectionConjugacy
