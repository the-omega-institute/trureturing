/- GID: D5/S3/Geometry/AlgebraicBoundary/BoundaryComponentRecovery
   generality: G
   mirror-B: D5/B/S3/Geometry/AlgebraicBoundary/BoundaryComponentRecovery
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Arbitrary finite boundary equations recover the cone from entire complement components. -/

import D5.S3.Geometry.AlgebraicBoundary.BoundaryElimination

/-! The topological recovery step for arbitrary finite-degree boundary equations. -/

noncomputable section

open Set Filter
open scoped Topology

namespace D5.S3.Geometry.AlgebraicBoundary.BoundaryComponentRecovery

variable {ι : Type*}

private theorem polynomial_nonzero_dense (p : MvPolynomial ι ℝ) (hp : p ≠ 0) :
    Dense {x : ι → ℝ | MvPolynomial.eval x p ≠ 0} := by
  classical
  apply dense_iff_inter_open.mpr
  intro U hU hUne
  by_contra hne
  have hzero : ∀ x ∈ U, MvPolynomial.eval x p = 0 := by
    intro x hx
    by_contra h
    exact hne ⟨x, hx, h⟩
  obtain ⟨a, ha⟩ := hUne
  obtain ⟨I, s, hs, hsU⟩ := isOpen_pi_iff.mp hU a ha
  let T (i : ι) : Set ℝ := if i ∈ I then s i else univ
  have hT (i : ι) : (T i).Infinite := by
    by_cases hi : i ∈ I
    · exact infinite_of_mem_nhds (a i) (by simpa [T, hi] using
        ((hs i hi).1.mem_nhds (hs i hi).2))
    · simpa [T, hi] using infinite_univ (α := ℝ)
  have hTU : univ.pi T ⊆ U := by
    simpa only [T, ← Finset.mem_coe, univ_pi_ite] using hsU
  apply hp
  apply MvPolynomial.funext_set T hT
  intro x hx
  simpa using hzero x (hTU hx)

/-- No degree bound, homogeneity, semialgebraicity or interior nonvanishing is assumed.
The selected collection of components is not asserted finite here. -/
private theorem boundary_component_recovery [Fintype ι] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (c : E ≃L[ℝ] (ι → ℝ))
    (C : ProperCone ℝ E) (hfull : (interior (C : Set E)).Nonempty)
    (p : MvPolynomial ι ℝ) (hp : p ≠ 0)
    (hvan : ∀ y ∈ frontier (C : Set E), MvPolynomial.eval (c y) p = 0) :
    let U : Set E := {x | MvPolynomial.eval (c x) p ≠ 0}
    closure (⋃₀ {D ∈ connectedComponentIn U '' U | D ⊆ interior (C : Set E)}) =
      (C : Set E) := by
  dsimp only
  let U : Set E := {x | MvPolynomial.eval (c x) p ≠ 0}
  let F : Set (Set E) := {D ∈ connectedComponentIn U '' U | D ⊆ interior (C : Set E)}
  have hcomp : ∀ x ∈ interior (C : Set E) ∩ U,
      connectedComponentIn U x ⊆ interior (C : Set E) := by
    intro x hx
    have hcover : connectedComponentIn U x ⊆ interior (C : Set E) ∪ (C : Set E)ᶜ := by
      intro y hy
      by_cases hyi : y ∈ interior (C : Set E)
      · exact Or.inl hyi
      · right
        intro hyC
        have hyf : y ∈ frontier (C : Set E) := C.isClosed.frontier_eq ▸ ⟨hyC, hyi⟩
        exact connectedComponentIn_subset U x hy (hvan y hyf)
    rcases isPreconnected_connectedComponentIn.subset_or_subset isOpen_interior
      C.isClosed.isOpen_compl (Set.disjoint_left.mpr (fun _ hi ho => ho (interior_subset hi)))
      hcover with h | h
    · exact h
    · exact False.elim (h (mem_connectedComponentIn hx.2) (interior_subset hx.1))
  have hsub : ⋃₀ F ⊆ interior (C : Set E) := by
    rintro x ⟨D, hD, hx⟩
    exact hD.2 hx
  have hTsub : interior (C : Set E) ∩ U ⊆ ⋃₀ F := by
    intro x hx
    exact ⟨connectedComponentIn U x, ⟨⟨x, hx.2, rfl⟩, hcomp x hx⟩,
      mem_connectedComponentIn hx.2⟩
  have hd : Dense U := (polynomial_nonzero_dense p hp).preimage c.isOpenMap
  have hdint := hd.open_subset_closure_inter (t := interior (C : Set E)) isOpen_interior
  have hclosure : closure (interior (C : Set E) ∩ U) = (C : Set E) := by
    apply (closure_minimal (inter_subset_left.trans interior_subset) C.isClosed).antisymm
    calc
      (C : Set E) = closure (interior (C : Set E)) := by
        rw [C.convex.closure_interior_eq_closure_of_nonempty_interior hfull, C.isClosed.closure_eq]
      _ ⊆ closure (interior (C : Set E) ∩ U) := closure_minimal hdint isClosed_closure
  apply (closure_minimal (hsub.trans interior_subset) C.isClosed).antisymm
  rw [← hclosure]
  exact closure_mono hTsub

end D5.S3.Geometry.AlgebraicBoundary.BoundaryComponentRecovery
