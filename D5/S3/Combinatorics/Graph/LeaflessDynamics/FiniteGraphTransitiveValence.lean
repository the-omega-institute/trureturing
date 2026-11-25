/- GID: D5/S3/Combinatorics/Graph/LeaflessDynamics/FiniteGraphTransitiveValence
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/LeaflessDynamics/FiniteGraphTransitiveValence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The sharp forward Bowen bound for topologically transitive finite graph maps. -/

import D5.S1.Dynamics.Shadowing.FiniteGraphExceptionalRepeller
import D5.S1.Dynamics.Shadowing.FiniteGraphTransitivityFrontier
import D5.S3.Combinatorics.Graph.LeaflessDynamics.FiniteGraphValenceBound

/-! Strong transitivity in the finitely positively expansive case and the valence bound. -/

open D5.S1.Dynamics.Shadowing
open Function Set

namespace D5.S1.Dynamics.Shadowing.FiniteGraphAffineRealization

variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] (G : SimpleGraph V)
variable {f : Space G → Space G}

/-- Finite positive expansivity rules out the finite set of points missed by
the images of a free subarc. This gives the pointwise form of strong transitivity. -/
theorem stronglyTransitive_of_finitelyPositiveExpansive (hG : G.Connected) (hf : Continuous f)
    (htrans : ∀ A B : Set (Space G), IsOpen A → A.Nonempty → IsOpen B → B.Nonempty →
      ∃ n : ℕ, (f^[n] '' A ∩ B).Nonempty)
    (hfinite : FinitelyPositiveExpansive f) : StronglyTransitive G f := by
  intro U hU hUne x
  obtain ⟨u, v, h, a, b, _, hab, _, hsub, hEfin, hinv, _⟩ :=
    exists_edgeChart_Icc_finite_exceptional_set G hG hf htrans hU hUne
  let J := edgeChart G h '' Icc a b
  let O := ⋃ n : ℕ, f^[n] '' J
  have hJ : edgeChart G h a ∈ J := mem_image_of_mem _ (left_mem_Icc.mpr hab.le)
  have hO : edgeChart G h a ∈ O := mem_iUnion_of_mem 0 (by simpa using hJ)
  have hproper : Oᶜ ≠ univ := by
    intro he
    have hmiss : edgeChart G h a ∈ Oᶜ := he ▸ mem_univ _
    exact hmiss hO
  have hnone : Oᶜ = ∅ := finite_totally_invariant_eq_empty G hf htrans hfinite hEfin hinv hproper
  have hx : x ∈ O := by
    by_contra hx
    have hmiss : x ∈ Oᶜ := hx
    rw [hnone] at hmiss
    exact hmiss
  obtain ⟨n, hn⟩ := mem_iUnion.mp hx
  exact ⟨n, image_mono hsub hn⟩

end D5.S1.Dynamics.Shadowing.FiniteGraphAffineRealization

namespace D5.S3.Combinatorics.Graph.LeaflessDynamics.FiniteMultigraphExactDynamics

open D5.S3.ConceptDynamics.Coding.EssentialWordRealization (DirectedMultigraph)
open D5.S3.Combinatorics.Graph.LeaflessDynamics.TripleEdgeSubdivision (Flag endpoint step graph connected)
open TripleEdgeSubdivisionRealization (realization subdivisionHomeomorph)
/-- The sharp bound for a transitive selfmap of any metric model of a finite
connected multigraph counts each loop twice at its vertex. -/
theorem forwardBowenBound_of_transitive_multigraph {V E X : Type*}
    [Fintype V] [Fintype E] [Nonempty E] [DecidableEq V] [DecidableEq E]
    [TopologicalSpace V] [DiscreteTopology V] [TopologicalSpace E] [DiscreteTopology E]
    [MetricSpace X] (M : DirectedMultigraph V E) (e : X ≃ₜ realization M)
    (hconn : ∀ u v, Relation.ReflTransGen (step M) u v) {f : X → X} (hf : Continuous f)
    (hfinite : FinitelyPositiveExpansive f)
    (htrans : ∀ A B : Set X, IsOpen A → A.Nonempty → IsOpen B → B.Nonempty →
      ∃ n : ℕ, (f^[n] '' A ∩ B).Nonempty)
    {D : ℕ} (hD : 2 ≤ D) (hdeg : ∀ v, ({a : Flag E | endpoint M a = v} : Set _).ncard ≤ D) :
    ∃ ε > 0, ForwardBowenBound f univ ε (D - 1) := by
  obtain ⟨a⟩ : Nonempty E := inferInstance
  let : Nonempty V := ⟨M.source a⟩
  let : Nontrivial (V ⊕ Flag E) := ⟨⟨Sum.inr (Sum.inl a), Sum.inr (Sum.inr a), by simp⟩⟩
  let equiv := e.trans (subdivisionHomeomorph M)
  let g := equiv ∘ f ∘ equiv.symm
  have hconj : Semiconj equiv f g := by intro x; simp [g]
  have hg : Continuous g := equiv.continuous.comp (hf.comp equiv.symm.continuous)
  obtain ⟨ε, hε, N, hN, hbound⟩ := hfinite
  obtain ⟨δ, hδ, hδbound⟩ := forwardBowenBound_conjugate equiv hε hbound
  have hpre {A : Set (FiniteGraphAffineRealization.Space (graph M))} (hA : A.Nonempty) :
      (equiv ⁻¹' A).Nonempty := by
    obtain ⟨z, hz⟩ := hA
    exact ⟨equiv.symm z, by simpa using hz⟩
  have hgtrans (A B : Set (FiniteGraphAffineRealization.Space (graph M)))
      (hA : IsOpen A) (hAne : A.Nonempty) (hB : IsOpen B) (hBne : B.Nonempty) :
      ∃ n : ℕ, (g^[n] '' A ∩ B).Nonempty := by
    obtain ⟨n, y, ⟨x, hx, rfl⟩, hy⟩ := htrans _ _ (hA.preimage equiv.continuous) (hpre hAne)
      (hB.preimage equiv.continuous) (hpre hBne)
    exact ⟨n, equiv (f^[n] x), ⟨equiv x, hx, (hconj.iterate_right n x).symm⟩, hy⟩
  have hgstrong := FiniteGraphAffineRealization.stronglyTransitive_of_finitelyPositiveExpansive
    (graph M) (connected M hconn) hg hgtrans ⟨δ, hδ, N, hN, hδbound⟩
  refine forwardBowenBound_of_stronglyTransitive_multigraph M e hconn hf
    ⟨ε, hε, N, hN, hbound⟩ ?_ hD hdeg
  intro U hU hUne y
  obtain ⟨n, _, ⟨x, hx, rfl⟩, hy⟩ := hgstrong _ (equiv.isOpenMap _ hU) (hUne.image equiv) (equiv y)
  exact ⟨n, x, hx, equiv.injective ((hconj.iterate_right n x).trans hy)⟩

#print axioms forwardBowenBound_of_transitive_multigraph

end D5.S3.Combinatorics.Graph.LeaflessDynamics.FiniteMultigraphExactDynamics
