/- GID: D5/S3/Topology/FiniteSubspaceComplement
   generality: G
   mirror-B: D5/B/S3/Topology/FiniteSubspaceComplement
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Avoiding finitely many subspaces in an open convex domain by two line segments. -/

import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Baire.Lemmas

open Set

namespace D5.S3.Topology.FiniteSubspaceComplement

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Finite ι]

private theorem dense_compl_submodule {P : Submodule ℝ E} (hP : P ≠ ⊤) :
    Dense (P : Set E)ᶜ := by
  apply interior_eq_empty_iff_dense_compl.mp
  apply Set.not_nonempty_iff_eq_empty.mp
  intro h
  exact hP (P.eq_top_of_nonempty_interior' h)

private theorem segment_avoids {P : Submodule ℝ E} {x z : E} (hx : x ∉ P)
    (hz : z ∉ P ⊔ Submodule.span ℝ {x}) :
    segment ℝ x z ⊆ (P : Set E)ᶜ := by
  intro y hy hyP
  rw [segment_eq_image] at hy
  obtain ⟨t, ht, rfl⟩ := hy
  by_cases ht0 : t = 0
  · apply hx
    simpa [ht0] using hyP
  · let Q := P ⊔ Submodule.span ℝ {x}
    have hxQ : x ∈ Q := (show Submodule.span ℝ {x} ≤ Q from le_sup_right)
      (Submodule.subset_span (mem_singleton x))
    have hpQ : (1 - t) • x + t • z ∈ Q := (show P ≤ Q from le_sup_left) hyP
    have htQ : t • z ∈ Q := by
      convert Q.sub_mem hpQ (Q.smul_mem (1 - t) hxQ) using 1; abel
    apply hz
    have h := Q.smul_mem t⁻¹ htQ
    rwa [smul_smul, inv_mul_cancel₀ ht0, one_smul] at h

/-- In an open convex set, the complement of finitely many subspaces is path connected if
adjoining any line to any of the forbidden subspaces still gives a proper subspace. -/
theorem pathConnected_complement_in_open_convex [FiniteDimensional ℝ E]
    (U : Set E) (hopen : IsOpen U) (hconv : Convex ℝ U) (hne : U.Nonempty)
    (P : ι → Submodule ℝ E)
    (proper : ∀ i x, P i ⊔ Submodule.span ℝ {x} ≠ ⊤) :
    IsPathConnected (U \ ⋃ i, (P i : Set E)) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hdense (x : E) : Dense (⋂ i, ((P i ⊔ Submodule.span ℝ {x} : Submodule ℝ E) : Set E)ᶜ) :=
    dense_iInter_of_isOpen
      (fun i => (P i ⊔ Submodule.span ℝ {x}).closed_of_finiteDimensional.isOpen_compl)
      (fun i => dense_compl_submodule (proper i x))
  have hbase : Dense (⋂ i, (P i : Set E)ᶜ) := dense_iInter_of_isOpen
    (fun i => (P i).closed_of_finiteDimensional.isOpen_compl)
    (fun i => dense_compl_submodule (fun hi => proper i 0 (by simp [hi])))
  obtain ⟨x, hxU, hxout⟩ := hbase.inter_open_nonempty U hopen hne
  rw [← compl_iUnion] at hxout
  have hx : x ∈ U \ ⋃ i, (P i : Set E) := ⟨hxU, hxout⟩
  refine ⟨x, hx, ?_⟩
  intro y hy
  let A (w : E) : Set E := ⋂ i, ((P i ⊔ Submodule.span ℝ {w} : Submodule ℝ E) : Set E)ᶜ
  have hA (w : E) : IsOpen (A w) := isOpen_iInter_of_finite fun i =>
    (P i ⊔ Submodule.span ℝ {w}).closed_of_finiteDimensional.isOpen_compl
  have hd : Dense (A x ∩ A y) :=
    (hdense x).inter_of_Gδ (hA x).isGδ (hA y).isGδ (hdense y)
  obtain ⟨z, hzU, ⟨hzx, hzy⟩⟩ := hd.inter_open_nonempty U hopen hne
  have seg (w : E) (hw : w ∈ U \ ⋃ i, (P i : Set E)) (hz' : z ∈ A w) :
      segment ℝ w z ⊆ U \ ⋃ i, (P i : Set E) := by
    intro u hu
    refine ⟨hconv.segment_subset hw.1 hzU hu, ?_⟩
    intro huP
    obtain ⟨i, hui⟩ := mem_iUnion.mp huP
    have hwi : w ∉ P i := fun h => hw.2 (mem_iUnion.mpr ⟨i, h⟩)
    exact (segment_avoids hwi (mem_iInter.mp hz' i) hu) hui
  exact (JoinedIn.of_segment_subset (seg x hx hzx)).trans
    (JoinedIn.of_segment_subset (seg y hy hzy)).symm

#print axioms pathConnected_complement_in_open_convex

end D5.S3.Topology.FiniteSubspaceComplement
