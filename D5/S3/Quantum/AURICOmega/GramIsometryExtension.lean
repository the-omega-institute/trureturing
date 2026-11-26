/- GID: D5/S3/Quantum/AURICOmega/GramIsometryExtension
   generality: G
   mirror-B: D5/B/S3/Quantum/AURICOmega/GramIsometryExtension
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Gram-preserving permutations of a spanning family extend uniquely to isometries. -/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Isometric extension of Gram-preserving permutations

Let `φ : ι → E` be a family whose range spans a real inner product space `E`.
A permutation `σ` of `ι` with `⟪φ (σ a), φ (σ b)⟫_ℝ = ⟪φ a, φ b⟫_ℝ` for all `a b`
extends to exactly one linear isometry equivalence `U` of `E` with `U (φ a) = φ (σ a)`.

No completeness or finite-dimensionality of `E` is required: the extension is obtained
by factoring the linear combination map `(ι →₀ ℝ) → E` of the reindexed family
`φ ∘ σ` through the surjective linear combination map of `φ`.
-/

open scoped InnerProductSpace

namespace D5.S3.Quantum.AURICOmega.GramIsometryExtension

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Gram preservation transfers from the family to all finite linear combinations:
the combinations of `φ ∘ σ` have the same inner products as those of `φ`. -/
private lemma inner_linearCombination_comp (φ : ι → E) (σ : Equiv.Perm ι)
    (hσ : ∀ a b : ι, ⟪φ (σ a), φ (σ b)⟫_ℝ = ⟪φ a, φ b⟫_ℝ) (c d : ι →₀ ℝ) :
    ⟪Finsupp.linearCombination ℝ (φ ∘ σ) c, Finsupp.linearCombination ℝ (φ ∘ σ) d⟫_ℝ =
      ⟪Finsupp.linearCombination ℝ φ c, Finsupp.linearCombination ℝ φ d⟫_ℝ := by
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, sum_inner, inner_sum,
    real_inner_smul_left, real_inner_smul_right, Function.comp_apply, hσ]

/-- A Gram-preserving permutation of a spanning family extends to a linear isometry
equivalence sending each `φ a` to `φ (σ a)`. -/
private lemma exists_linearIsometryEquiv_of_gram_preserving
    (φ : ι → E) (hφ : Submodule.span ℝ (Set.range φ) = ⊤)
    (σ : Equiv.Perm ι)
    (hσ : ∀ a b : ι, ⟪φ (σ a), φ (σ b)⟫_ℝ = ⟪φ a, φ b⟫_ℝ) :
    ∃ U : E ≃ₗᵢ[ℝ] E, ∀ a : ι, U (φ a) = φ (σ a) := by
  set L := Finsupp.linearCombination ℝ φ with hLdef
  set L' := Finsupp.linearCombination ℝ (φ ∘ σ) with hL'def
  have hL : Function.Surjective L := by
    rw [← LinearMap.range_eq_top, hLdef, Finsupp.range_linearCombination, hφ]
  have hL' : Function.Surjective L' := by
    rw [← LinearMap.range_eq_top, hL'def, Finsupp.range_linearCombination,
      σ.surjective.range_comp, hφ]
  have hinner : ∀ c d, ⟪L' c, L' d⟫_ℝ = ⟪L c, L d⟫_ℝ :=
    inner_linearCombination_comp φ σ hσ
  have hnorm : ∀ c, ‖L' c‖ = ‖L c‖ := fun c => by
    rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner, hinner]
  have hker : LinearMap.ker L ≤ LinearMap.ker L' := fun c hc => by
    rw [LinearMap.mem_ker] at hc ⊢
    rw [← norm_eq_zero, hnorm, hc, norm_zero]
  let U₀ : E →ₗ[ℝ] E :=
    ((LinearMap.ker L).liftQ L' hker).comp (L.quotKerEquivOfSurjective hL).symm.toLinearMap
  have hU₀ : ∀ c, U₀ (L c) = L' c := fun c => by
    simp only [U₀, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply]
  have hU₀norm : ∀ x, ‖U₀ x‖ = ‖x‖ := fun x => by
    obtain ⟨c, rfl⟩ := hL x
    rw [hU₀, hnorm]
  let U₁ : E →ₗᵢ[ℝ] E := { toLinearMap := U₀, norm_map' := hU₀norm }
  have hU₁ : Function.Surjective U₁ := fun y => by
    obtain ⟨c, rfl⟩ := hL' y
    exact ⟨L c, hU₀ c⟩
  refine ⟨LinearIsometryEquiv.ofSurjective U₁ hU₁, fun a => ?_⟩
  have h := hU₀ (Finsupp.single a 1)
  simp only [L, L', Finsupp.linearCombination_single, one_smul, Function.comp_apply] at h
  rw [LinearIsometryEquiv.coe_ofSurjective]
  exact h

/-- A permutation of the index set of a spanning family that preserves the Gram kernel
extends uniquely to a linear isometry equivalence of the ambient real inner product space. -/
theorem existsUnique_linearIsometryEquiv_of_gram_preserving
    (φ : ι → E) (hφ : Submodule.span ℝ (Set.range φ) = ⊤)
    (σ : Equiv.Perm ι)
    (hσ : ∀ a b : ι, ⟪φ (σ a), φ (σ b)⟫_ℝ = ⟪φ a, φ b⟫_ℝ) :
    ∃! U : E ≃ₗᵢ[ℝ] E, ∀ a : ι, U (φ a) = φ (σ a) := by
  obtain ⟨U, hU⟩ := exists_linearIsometryEquiv_of_gram_preserving φ hφ σ hσ
  refine ⟨U, hU, fun V hV => ?_⟩
  apply LinearIsometryEquiv.toLinearEquiv_injective
  apply LinearEquiv.toLinearMap_injective
  exact LinearMap.ext_on_range hφ fun a => (hV a).trans (hU a).symm

end D5.S3.Quantum.AURICOmega.GramIsometryExtension
