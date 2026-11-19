/- GID: D5/S3/Combinatorics/Orthogonality/SixDimensionalProfiles
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Orthogonality/SixDimensionalProfiles
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: All actual nonclique profiles are realized and their complete image has cardinality 240. -/

import D5.S3.Combinatorics.Orthogonality.SixDimensionalLiftGeometry

/-! Profiles retain the entire actual first kernel and projection. The
image is taken over every actual submodule outside the original T. The
constant 240 is derived from the full submodule lattices and a proved
realization map; no list of selected profiles is assumed. The separate
139 multi-color statistic of the fixed supplied certificate is not inferred. -/
set_option autoImplicit false
noncomputable section
namespace D5.S3.Combinatorics.Orthogonality.SixDimensionalProfiles

open SixDimensionalLiftGeometry SplitSubmoduleLift

/-- The represented full placement always has exactly its original K and P. -/
theorem represented_profile (K' P' : Submodule F A) (f : P' →ₗ[F] A ⧸ K') :
    K (represented K' P' f) = K' ∧ P (represented K' P' f) = P' := by
  have hs : split (represented K' P' f) = liftSpace K' P' f :=
    Submodule.comap_map_eq_of_injective coordinates.injective _
  change firstKernel (split (represented K' P' f)) = K' ∧
    secondRange (split (represented K' P' f)) = P'
  rw [hs]
  exact ⟨firstKernel_liftSpace _ _ _,secondRange_liftSpace _ _ _⟩

/-- The complete actual nonclique domain, with zero excluded by the geometry. -/
abbrev Nonclique := {U : Submodule F V // ¬ U ≤ T}

/-- Full exact profiles, not merely dimension triples. -/
abbrev Profile := Submodule F A × Label

/-- Every actual nonclique submodule has its full profile. -/
def profile (U : Nonclique) : Profile :=
  (K U.val,⟨P U.val,fun h => U.property ((projection_eq_bot_iff U.val).mp h)⟩)

/-- Every full exact profile occurs in the original graph domain. -/
theorem profile_surjective : Function.Surjective profile := by
  rintro ⟨K',P'⟩
  let U := represented K' P'.val 0
  have hh := represented_profile K' P'.val 0
  have hU : ¬ U ≤ T := by
    intro h
    apply P'.property
    exact hh.2.symm.trans ((projection_eq_bot_iff U).mpr h)
  refine ⟨⟨U,hU⟩,?_⟩
  apply Prod.ext
  · exact hh.1
  · exact Subtype.ext hh.2

private theorem all_submodule_card : Nat.card (Submodule F A) = 16 := by
  classical
  letI : Fintype (Submodule F A) := Fintype.ofFinite _
  have hc := Fintype.card_subtype_compl (fun U : Submodule F A => U = ⊥)
  rw [Fintype.card_subtype_eq] at hc
  simp only [← Nat.card_eq_fintype_card] at hc
  change Nat.card Label = Nat.card (Submodule F A) - 1 at hc
  rw [label_card] at hc
  have hp := Fintype.card_pos (α := Submodule F A)
  rw [← Nat.card_eq_fintype_card] at hp
  omega

private theorem all_profile_card : Nat.card Profile = 240 := by
  rw [Nat.card_prod,all_submodule_card,label_card]

/-- The image contains exactly those profiles actually realized by original
nonclique submodules. -/
abbrev RealizedProfile := Set.range profile

/-- Actual realized profiles are in bijection with the entire K/P domain. -/
def realizedEquiv : RealizedProfile ≃ Profile where
  toFun x := x.val
  invFun p := ⟨p,profile_surjective p⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The exact number of profiles of the entire actual nonclique graph is 240. -/
theorem result : Nat.card RealizedProfile = 240 :=
  (Nat.card_congr realizedEquiv).trans all_profile_card

#print axioms result
end D5.S3.Combinatorics.Orthogonality.SixDimensionalProfiles
