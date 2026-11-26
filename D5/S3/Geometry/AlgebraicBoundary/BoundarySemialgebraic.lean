/- GID: D5/S3/Geometry/AlgebraicBoundary/BoundarySemialgebraic
   generality: G
   mirror-B: D5/B/S3/Geometry/AlgebraicBoundary/BoundarySemialgebraic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Any nonzero entire-boundary polynomial makes the original full cone semialgebraic. -/

import D5.S3.Geometry.AlgebraicBoundary.BoundaryComponentRecovery
import D5.S3.Geometry.AlgebraicBoundary.TauCeti.Geometry.RealAlgebraic.Semialgebraic.Connected
import D5.S3.Geometry.AlgebraicBoundary.TauCeti.Geometry.RealAlgebraic.Semialgebraic.Topology

noncomputable section
open Set Filter
open scoped Topology
namespace D5.S3.Geometry.AlgebraicBoundary.BoundarySemialgebraic

open private polynomial_nonzero_dense
  from D5.S3.Geometry.AlgebraicBoundary.BoundaryComponentRecovery

variable {ι : Type*} [Fintype ι]

private theorem cone_semialgebraic (C : ProperCone ℝ (ι → ℝ))
    (hfull : (interior (C : Set (ι → ℝ))).Nonempty)
    (p : MvPolynomial ι ℝ) (hp : p ≠ 0)
    (hvan : ∀ y ∈ frontier (C : Set (ι → ℝ)), MvPolynomial.eval y p = 0) :
    TauCeti.IsSemialgebraic (C : Set (ι → ℝ)) := by
  classical
  let U : Set (ι → ℝ) := {x | MvPolynomial.eval x p ≠ 0}
  obtain ⟨D, hDf, _, hD, hDU⟩ :=
    (TauCeti.isSemialgebraic_eval_ne_zero p).exists_finite_isConnected_partition
  change ⋃₀ D = U at hDU
  let F : Set (Set (ι → ℝ)) := {E ∈ D | E ⊆ interior (C : Set (ι → ℝ))}
  have hFf : F.Finite := hDf.subset (sep_subset _ _)
  have hEU : ∀ E ∈ D, E ⊆ U := by
    intro E hE x hx
    exact hDU ▸ mem_sUnion.mpr ⟨E, hE, hx⟩
  have hside : ∀ E ∈ D, E ⊆ interior (C : Set (ι → ℝ)) ∨ E ⊆ (C : Set (ι → ℝ))ᶜ := by
    intro E hE
    apply (hD E hE).1.isPreconnected.subset_or_subset isOpen_interior C.isClosed.isOpen_compl
      (disjoint_left.mpr fun _ hi ho => ho (interior_subset hi))
    intro x hx
    by_cases hi : x ∈ interior (C : Set (ι → ℝ))
    · exact Or.inl hi
    · right
      intro hC
      have hf : x ∈ frontier (C : Set (ι → ℝ)) := C.isClosed.frontier_eq ▸ ⟨hC, hi⟩
      exact hEU E hE hx (hvan x hf)
  have hunion : ⋃₀ F = interior (C : Set (ι → ℝ)) ∩ U := by
    apply Subset.antisymm
    · rintro x ⟨E, hE, hx⟩
      exact ⟨hE.2 hx, hEU E hE.1 hx⟩
    · intro x hx
      obtain ⟨E, hE, hxE⟩ := mem_sUnion.mp (hDU.symm ▸ hx.2)
      have hEi := (hside E hE).resolve_right fun h => h hxE (interior_subset hx.1)
      exact ⟨E, ⟨hE, hEi⟩, hxE⟩
  have hsemi : TauCeti.IsSemialgebraic (⋃₀ F) := by
    rw [sUnion_eq_biUnion]
    exact TauCeti.IsSemialgebraic.biUnion hFf fun E hE => (hD E hE.1).2
  have hd : Dense U := polynomial_nonzero_dense p hp
  have hcl : closure (⋃₀ F) = (C : Set (ι → ℝ)) := by
    rw [hunion]
    apply (closure_minimal (inter_subset_left.trans interior_subset) C.isClosed).antisymm
    calc
      (C : Set (ι → ℝ)) = closure (interior (C : Set (ι → ℝ))) := by
        rw [C.convex.closure_interior_eq_closure_of_nonempty_interior hfull, C.isClosed.closure_eq]
      _ ⊆ closure (interior (C : Set (ι → ℝ)) ∩ U) :=
        closure_minimal (hd.open_subset_closure_inter isOpen_interior) isClosed_closure
  exact hcl ▸ hsemi.closure

/-- The conclusion uses finite Boolean combinations of the actual polynomial conditions on E. -/
private theorem original_cone_semialgebraic {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (c : E ≃L[ℝ] (ι → ℝ))
    (C : ProperCone ℝ E) (hfull : (interior (C : Set E)).Nonempty)
    (p : MvPolynomial ι ℝ) (hp : p ≠ 0)
    (hvan : ∀ y ∈ frontier (C : Set E), MvPolynomial.eval (c y) p = 0) :
    (C : Set E) ∈ MeasureTheory.generateSetAlgebra
      (range (fun r : MvPolynomial ι ℝ => {x : E | MvPolynomial.eval (c x) r = 0}) ∪
        range (fun r : MvPolynomial ι ℝ => {x : E | 0 < MvPolynomial.eval (c x) r})) ∧
    ∃ (m : ℕ) (r : Fin m → MvPolynomial ι ℝ) (Φ : (Fin m → SignType) → Prop),
      ∀ x : E, x ∈ C ↔ Φ (fun i => SignType.sign (MvPolynomial.eval (c x) (r i))) := by
  let D := C.comap c.symm.toContinuousLinearMap
  have hi : interior (D : Set (ι → ℝ)) = c.symm ⁻¹' interior (C : Set E) :=
    (c.symm.toHomeomorph.preimage_interior (C : Set E)).symm
  have hf : frontier (D : Set (ι → ℝ)) = c.symm ⁻¹' frontier (C : Set E) :=
    (c.symm.toHomeomorph.preimage_frontier (C : Set E)).symm
  have hfullD : (interior (D : Set (ι → ℝ))).Nonempty := by
    obtain ⟨a, ha⟩ := hfull
    exact ⟨c a, by simpa [hi] using ha⟩
  have hsemi := cone_semialgebraic D hfullD p hp (by
    intro z hz
    simpa using hvan (c.symm z) (by simpa [hf] using hz))
  have hpre : c ⁻¹' (D : Set (ι → ℝ)) = (C : Set E) := by ext x; simp [D]
  constructor
  · rw [← hpre]
    apply TauCeti.IsSemialgebraic.induction (motive := fun s =>
      c ⁻¹' s ∈ MeasureTheory.generateSetAlgebra
        (range (fun r : MvPolynomial ι ℝ => {x : E | MvPolynomial.eval (c x) r = 0}) ∪
          range (fun r : MvPolynomial ι ℝ => {x : E | 0 < MvPolynomial.eval (c x) r})))
      (fun r => MeasureTheory.self_subset_generateSetAlgebra (Or.inl ⟨r, rfl⟩))
      (fun r => MeasureTheory.self_subset_generateSetAlgebra (Or.inr ⟨r, rfl⟩))
      (by simpa using MeasureTheory.isSetAlgebra_generateSetAlgebra.empty_mem)
      (fun s _ hs => by simpa using MeasureTheory.isSetAlgebra_generateSetAlgebra.compl_mem hs)
      (fun s t _ _ hs ht => by simpa using
        MeasureTheory.isSetAlgebra_generateSetAlgebra.union_mem hs ht) hsemi
  · obtain ⟨m, r, Φ, hr⟩ := hsemi.exists_eq_setOf_sign_eval
    refine ⟨m, r, Φ, fun x => ?_⟩
    have hx : c x ∈ (D : Set (ι → ℝ)) ↔ x ∈ C := by simp [D]
    rw [← hx, hr]
    rfl

end D5.S3.Geometry.AlgebraicBoundary.BoundarySemialgebraic
