/- GID: D5/S3/Geometry/AlgebraicBoundary/TauCeti/Geometry/RealAlgebraic/Semialgebraic/Connected
   generality: G
   mirror-B: D5/B/S3/Geometry/AlgebraicBoundary/TauCeti/Geometry/RealAlgebraic/Semialgebraic/Connected
   mirror-E: none(waiver:external-source-adaptation)
   anchors: []
   utility: none
   digest: Selected finite connected partition and closure source for boundary recovery. -/

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors

Source: TauCetiProject/TauCeti revision 62bbc0596dc3539d488232e4e924a338548ea0a9.
Selection: CAD/Basic.sUnion_sep_subset; CAD/Existence.exists_isCAD_subset_or_disjoint; Semialgebraic/Connected partition declarations.
Adaptation: D5 import routes and selection of consumed declarations; mathematical telescopes
and proof bodies are retained. License: docs/reports/licenses/TauCeti-LICENSE.txt.
Retire each adaptation when the actual pinned mathlib supplies an equivalent declaration,
replacing its consumers by direct applications of that pinned owner.
No independent mathematical novelty or escape credit is claimed.
-/
module

public import D5.S3.Geometry.AlgebraicBoundary.TauCeti.Geometry.RealAlgebraic.CAD.Existence

public section
open Function MvPolynomial Set
namespace TauCeti
variable {σ τ : Type*}

namespace IsCAD
variable {n : ℕ} {𝒞 : Set (Set (Fin n → ℝ))}
/-- A set containing or missing each cell of a cylindrical algebraic decomposition is the union
of the cells it contains. -/
theorem sUnion_sep_subset (h : IsCAD n 𝒞) {s : Set (Fin n → ℝ)}
    (hs : ∀ E ∈ 𝒞, E ⊆ s ∨ Disjoint E s) : ⋃₀ {E ∈ 𝒞 | E ⊆ s} = s := by
  refine Subset.antisymm (sUnion_subset fun E hE ↦ hE.2) fun y hy ↦ ?_
  obtain ⟨E, hE, hyE⟩ := mem_sUnion.1 (h.isPartition.sUnion_eq_univ ▸ mem_univ y)
  exact ⟨E, ⟨hE, (hs E hE).resolve_right fun hd ↦ disjoint_left.1 hd hyE hy⟩, hyE⟩

end IsCAD

/-- **Decompositions adapted to a semialgebraic set.** For a semialgebraic subset `s` of `ℝ ^ n`
there is a cylindrical algebraic decomposition of `ℝ ^ n` each cell of which lies in `s` or misses
it, so that `s` is the union of the cells it contains (`TauCeti.IsCAD.sUnion_sep_subset`). -/
theorem IsSemialgebraic.exists_isCAD_subset_or_disjoint {s : Set (Fin n → ℝ)}
    (hs : IsSemialgebraic s) : ∃ 𝒞, IsCAD n 𝒞 ∧ ∀ E ∈ 𝒞, E ⊆ s ∨ Disjoint E s := by
  classical
  obtain ⟨m, p, Φ, rfl⟩ := hs.exists_eq_setOf_sign_eval
  obtain ⟨𝒞, h𝒞, hp⟩ := exists_isCAD_signInvariant (Finset.univ.image p)
  exact ⟨𝒞, h𝒞, fun E hE ↦ subset_or_disjoint_setOf_sign (f := fun i x ↦ eval x (p i))
    (fun i ↦ hp _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)) E hE) Φ⟩

/-- A semialgebraic subset of `ℝ ^ n` is the union of the cells of a cylindrical algebraic
decomposition that it contains. -/
private theorem IsSemialgebraic.exists_finite_isConnected_partition_fin {n : ℕ}
    {s : Set (Fin n → ℝ)} (hs : IsSemialgebraic s) :
    ∃ 𝒞 : Set (Set (Fin n → ℝ)), 𝒞.Finite ∧ 𝒞.PairwiseDisjoint id ∧
      (∀ t ∈ 𝒞, IsConnected t ∧ IsSemialgebraic t) ∧ ⋃₀ 𝒞 = s := by
  obtain ⟨𝒟, h𝒟, hsub⟩ := hs.exists_isCAD_subset_or_disjoint
  exact ⟨{E ∈ 𝒟 | E ⊆ s}, h𝒟.finite.subset (sep_subset _ _),
    h𝒟.isPartition.pairwiseDisjoint.subset (sep_subset _ _),
    fun E hE ↦ ⟨h𝒟.isConnected hE.1, h𝒟.isSemialgebraic hE.1⟩, h𝒟.sUnion_sep_subset hsub⟩

/-- **Connected decomposition of semialgebraic sets.** A semialgebraic subset of `σ → ℝ`, for a
finite index type `σ`, is the union of finitely many pairwise disjoint connected semialgebraic
sets. -/
theorem IsSemialgebraic.exists_finite_isConnected_partition {σ : Type*} [Finite σ]
    {s : Set (σ → ℝ)} (hs : IsSemialgebraic s) :
    ∃ 𝒞 : Set (Set (σ → ℝ)), 𝒞.Finite ∧ 𝒞.PairwiseDisjoint id ∧
      (∀ t ∈ 𝒞, IsConnected t ∧ IsSemialgebraic t) ∧ ⋃₀ 𝒞 = s := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin σ
  -- transport a decomposition of the set read in the coordinates `Fin n`
  let φ : (Fin n → ℝ) → σ → ℝ := fun y ↦ y ∘ e
  have hφψ : LeftInverse φ (fun x ↦ x ∘ e.symm) := fun x ↦ by ext; simp [φ]
  have hψφ : RightInverse φ (fun x ↦ x ∘ e.symm) := fun y ↦ by ext; simp [φ]
  have hφ : Continuous φ := continuous_pi fun i ↦ continuous_apply (e i)
  obtain ⟨𝒟, h𝒟, hd, hc, hu⟩ :=
    IsSemialgebraic.exists_finite_isConnected_partition_fin (hs.preimage_comp e)
  refine ⟨image φ '' 𝒟, h𝒟.image _, ?_, ?_, ?_⟩
  · rintro _ ⟨E, hE, rfl⟩ _ ⟨E', hE', rfl⟩ hne
    exact (disjoint_image_iff hψφ.injective).2 (hd hE hE' fun h ↦ hne (h ▸ rfl))
  · rintro _ ⟨E, hE, rfl⟩
    refine ⟨(hc E hE).1.image φ hφ.continuousOn, ?_⟩
    rw [image_eq_preimage_of_inverse hψφ hφψ]
    exact (hc E hE).2.preimage_comp e.symm
  · rw [← image_sUnion, hu, image_preimage_eq s hφψ.surjective]


end TauCeti
