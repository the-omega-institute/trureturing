/- GID: D5/S1/Dynamics/Shadowing/FiniteMultigraphExactDynamics
   generality: G
   mirror-B: D5/B/S1/Dynamics/Shadowing/FiniteMultigraphExactDynamics
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact positively expansive dynamics on the original finite closed-edge realization. -/

import D5.S1.Dynamics.Shadowing.ExactExpansiveConjugacy
import D5.S1.Dynamics.Shadowing.FiniteGraphExactDynamics
import D5.S1.Dynamics.Shadowing.TripleEdgeSubdivisionRealization

/-! Three-segment subdivision permits the edge-walk construction on graphs with loops
and parallel edges. The subdivision homeomorphism transports both the edge-walk map
and the pendant arc obstruction to the original realization. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Function Set
open D5.S3.ConceptDynamics.Coding.EssentialWordRealization (DirectedMultigraph)
open D5.S3.Combinatorics.Graph.LeaflessDynamics.TripleEdgeSubdivision (Flag endpoint step graph connected leafless_iff)

namespace D5.S1.Dynamics.Shadowing.FiniteMultigraphExactDynamics

open TripleEdgeSubdivisionRealization (realization subdivisionHomeomorph)

variable {V E X : Type*} [Fintype V] [Fintype E] [Nonempty E]
  [DecidableEq V] [DecidableEq E]
  [TopologicalSpace V] [DiscreteTopology V] [TopologicalSpace E] [DiscreteTopology E]
  [MetricSpace X]

/-- Every compact metric model of a connected leafless finite graph with at least
one edge admits the conjugate of the affine edge-walk map. Flags count loops twice. -/
theorem exists_exact_positivelyExpansive (M : DirectedMultigraph V E)
    (e : X ≃ₜ realization M) (hconn : ∀ u v, Relation.ReflTransGen (step M) u v)
    (hleaf : ∀ v, ({f : Flag E | endpoint M f = v} : Set _).ncard ≠ 1) :
    ∃ f : X → X, Continuous f ∧ ExactPendantObstruction.TopologicallyExact f ∧
      PositivelyExpansive f := by
  obtain ⟨a⟩ : Nonempty E := inferInstance
  let : Nonempty V := ⟨M.source a⟩
  let : Nontrivial (V ⊕ Flag E) :=
    ⟨⟨Sum.inr (Sum.inl a), Sum.inr (Sum.inr a), by simp⟩⟩
  let equivalence := e.trans (subdivisionHomeomorph M)
  let : CompactSpace X := equivalence.symm.compactSpace
  have hsub := connected M hconn
  have hsubleaf := (leafless_iff M).mpr hleaf
  let tours := FiniteGraphExactDynamics.chooseTours hsub hsubleaf
  let f := FiniteGraphExactDynamics.edgeWalkMap tours hsub
  exact ⟨equivalence.symm ∘ f ∘ equivalence,
    ExactExpansiveConjugacy.exact_expansive_conjugate equivalence.symm
      (FiniteGraphExactDynamics.continuous_edgeWalkMap tours hsub)
      (FiniteGraphExactDynamics.topologicallyExact_edgeWalkMap tours hsub)
      (FiniteGraphExactDynamics.forwardBowenBound_edgeWalkMap tours hsub)⟩

/-- A vertex with exactly one incident flag prevents an exact continuous selfmap
of the original realization from being finitely positively expansive. -/
theorem not_finitelyPositiveExpansive_of_one_incident_flag (M : DirectedMultigraph V E)
    (e : X ≃ₜ realization M) (v : V)
    (hv : ({f : Flag E | endpoint M f = v} : Set _).ncard = 1)
    {f : X → X} (hf : Continuous f) (hex : ExactPendantObstruction.TopologicallyExact f) :
    ¬ FinitelyPositiveExpansive f := by
  classical
  have hsub : ¬ ∀ w, ((graph M).neighborSet w).ncard ≠ 1 :=
    fun h => (leafless_iff M).mp h v hv
  obtain ⟨w, hw⟩ := not_forall.mp hsub
  have hdegree : (graph M).degree w = 1 := by
    simpa only [SimpleGraph.ncard_neighborSet] using (Classical.not_not.mp hw)
  let subdividedArc := FiniteGraphAffineRealization.pendantArcOfDegreeOne (graph M) w hdegree
  let equivalence := e.trans (subdivisionHomeomorph M)
  let : CompactSpace X := equivalence.symm.compactSpace
  let arc : PendantArc X :=
    { param := equivalence.symm ∘ subdividedArc.param
      continuous_param := equivalence.symm.continuous.comp subdividedArc.continuous_param
      injective_param := equivalence.symm.injective.comp subdividedArc.injective_param
      isOpen_tip := by
        simpa only [Set.image_image, Function.comp_def] using
          equivalence.symm.isOpenMap _ subdividedArc.isOpen_tip }
  exact ExactPendantObstruction.not_finitelyPositiveExpansive arc hf hex

/-- A finite connected multigraph with at least one edge admits continuous exact
finitely positively expansive dynamics on its original realization precisely when
no vertex has one incident flag. A loop contributes two flags. -/
theorem exists_exact_finitelyPositiveExpansive_iff (M : DirectedMultigraph V E)
    (e : X ≃ₜ realization M) (hconn : ∀ u v, Relation.ReflTransGen (step M) u v) :
    (∃ f : X → X, Continuous f ∧ ExactPendantObstruction.TopologicallyExact f ∧
      FinitelyPositiveExpansive f) ↔
      ∀ v, ({f : Flag E | endpoint M f = v} : Set _).ncard ≠ 1 := by
  constructor
  · rintro ⟨f, hf, hex, hF⟩ v hv
    exact not_finitelyPositiveExpansive_of_one_incident_flag M e v hv hf hex hF
  · intro hleaf
    obtain ⟨f, hf, hex, ε, hε, hsep⟩ := exists_exact_positivelyExpansive M e hconn hleaf
    refine ⟨f, hf, hex, ε, hε, 1, le_rfl, ?_⟩
    intro x _
    have hsubset : univ ∩ ForwardBowen f ε x ⊆ ({x} : Set X) := by
      intro y hy
      exact mem_singleton_iff.mpr (hsep x y hy.2).symm
    exact (Set.encard_mono hsubset).trans_eq (Set.encard_singleton x)

/--
info: 'D5.S1.Dynamics.Shadowing.FiniteMultigraphExactDynamics.exists_exact_positivelyExpansive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms exists_exact_positivelyExpansive

/--
info: 'D5.S1.Dynamics.Shadowing.FiniteMultigraphExactDynamics.not_finitelyPositiveExpansive_of_one_incident_flag' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms not_finitelyPositiveExpansive_of_one_incident_flag

/--
info: 'D5.S1.Dynamics.Shadowing.FiniteMultigraphExactDynamics.exists_exact_finitelyPositiveExpansive_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms exists_exact_finitelyPositiveExpansive_iff

end D5.S1.Dynamics.Shadowing.FiniteMultigraphExactDynamics
