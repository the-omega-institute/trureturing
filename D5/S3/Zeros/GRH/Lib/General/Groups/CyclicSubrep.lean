/- GID: D5/S3/Zeros/GRH/Lib/General/Groups/CyclicSubrep
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/General/Groups/CyclicSubrep
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.General.Groups.CyclicSubrep. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/General/Groups/CyclicSubrep.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Adelic.Unitary.CongruenceLevel
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! General lemmas of group theory (textbook or folklore).

This file: Cyclic subrepresentation of a vector; subrepresentation of smooth vectors. -/

variable {G V} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)

/-- The subspace V_y spanned by the translates ρ(g)y of the vector y. -/
abbrev cyclicSpan y := Submodule.span ℂ (.range (ρ · y))

lemma self_mem_cyclicSpan {ρ : Representation ℂ G V} {y} : y ∈ cyclicSpan ρ y :=
  Submodule.subset_span ⟨1, by simp⟩

lemma apply_mem_cyclicSpan {ρ : Representation ℂ G V} {y} g : ∀ x ∈ cyclicSpan ρ y,
  ρ g x ∈ cyclicSpan ρ y := Submodule.mapsTo_span fun _ ⟨h, _⟩ ↦ ⟨g * h, by simp [*]⟩

lemma compactMean_mem_cyclicSpan {ρ : Representation ℂ G V} {y} {K : Subgroup G} [TopologicalSpace
  G] [IsTopologicalGroup G] [IsSmoothRep ρ] [CompactSpace K] g {x} (h : x ∈ cyclicSpan ρ y) :
  compactMean ρ K (ρ g x) ∈ cyclicSpan ρ y :=
  (Submodule.ker_mkQ _).le (map_compactMean_of_const _ (by simp_all [apply_mem_cyclicSpan]))

/-- The subrepresentation of ρ on its smooth vectors, those fixed by all g in some neighbourhood
of 1. -/
def smoothVectorRep [TopologicalSpace G] [IsTopologicalGroup G] := ρ.subrepresentation ⟨⟨⟨{x | ∀ᶠ
  g in _, ρ g x = x}, (·.mp <| ·.mono (by grind))⟩, by simp⟩, fun _ _ ↦ (·.mono (by simp_all))⟩
  fun a _ _ ↦ .mono ((continuous_const_mul a⁻¹).mul_const a |>.tendsto 1 (by simpa)) (by simp)

instance [TopologicalSpace G] [IsTopologicalGroup G] : IsSmoothRep (smoothVectorRep ρ) :=
  ⟨(·.2.mono (by aesop))⟩
