/- GID: D5/S3/ConceptDynamics/Coding/PositiveRecoding/FiniteGraphRelabelHomeomorph
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/PositiveRecoding/FiniteGraphRelabelHomeomorph
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Relabel actual graph histories by vertex and edge equivalences. -/

/- Graph relabels act coordinatewise on integer-indexed histories. The homeomorphism requires discrete edge topologies, without a finiteness premise. -/
import D5.S3.ConceptDynamics.Coding.TwoSidedFiniteInduction

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.ConceptDynamics.Coding.ZeroWindowRelabeling
open EssentialWordRealization
variable {V E W D : Type*} {G : DirectedMultigraph V E} {H : DirectedMultigraph W D}

def Relabel.symm (r : Relabel G H) : Relabel H G where
  vertex := r.vertex.symm
  edge := r.edge.symm
  source d := by
    apply r.vertex.injective
    rw [r.vertex.apply_symm_apply]
    exact (r.source (r.edge.symm d)).symm.trans
      (congrArg H.source (r.edge.apply_symm_apply d))
  target d := by
    apply r.vertex.injective
    rw [r.vertex.apply_symm_apply]
    exact (r.target (r.edge.symm d)).symm.trans
      (congrArg H.target (r.edge.apply_symm_apply d))

section Topology
variable [TopologicalSpace E] [DiscreteTopology E]
variable [TopologicalSpace D] [DiscreteTopology D]
def Relabel.homeomorph (r : Relabel G H) : History G ≃ₜ History H where
  toFun := r.history
  invFun := r.symm.history
  left_inv x := by
    apply Subtype.ext
    funext t
    exact r.edge.symm_apply_apply _
  right_inv y := by
    apply Subtype.ext
    funext t
    exact r.edge.apply_symm_apply _
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro t
    exact (continuous_of_discreteTopology : Continuous r.edge).comp
      ((continuous_apply t).comp continuous_subtype_val)
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro t
    exact (continuous_of_discreteTopology : Continuous r.edge.symm).comp
      ((continuous_apply t).comp continuous_subtype_val)
end Topology
end D5.S3.ConceptDynamics.Coding.ZeroWindowRelabeling
