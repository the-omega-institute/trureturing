/- GID: D5/S3/ConceptDynamics/Coding/PositiveRecoding/SplitTowerTranslation
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/PositiveRecoding/SplitTowerTranslation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Derive integer-time laws inside the actual recoding constructions. -/

/- The signed convention is (translate a x)_t = x_(t+a). Time equivariance is derived for the actual relabel and split constructions. -/
import D5.S3.ConceptDynamics.Coding.TwoSidedFiniteInduction
import D5.S3.ConceptDynamics.Coding.PositiveRecoding.InSplitNumberedRecoding
import D5.S3.ConceptDynamics.Coding.StandardBeamHomeomorphisms

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace D5.S3.ConceptDynamics.Coding.SplitTowerTranslation
open EssentialWordRealization
open TwoSidedFiniteInduction
open CountedMatrixOverlap (CountMat Path elementaryHomeomorph)
open ZeroWindowRelabeling (Relabel)

abbrev time {V E : Type*} (G : DirectedMultigraph V E) :=
  StandardBeamHomeomorphisms.translate G
abbrev counted {n : ℕ} (B : CountMat n n) := InSplitNumberedRecoding.counted B


section Relabel
variable {V E W D : Type*} {G : DirectedMultigraph V E} {H : DirectedMultigraph W D}

theorem relabel_time (r : Relabel G H) (a : ℤ) (x : History G) :
    r.history (time G a x) = time H a (r.history x) := rfl

variable [TopologicalSpace E] [DiscreteTopology E]
variable [TopologicalSpace D] [DiscreteTopology D]

theorem relabel_homeomorph_time (r : Relabel G H) (a : ℤ) (x : History G) :
    r.homeomorph (time G a x) = time H a (r.homeomorph x) := rfl

theorem relabel_inverse_time (r : Relabel G H) (a : ℤ) (x : History H) :
    r.homeomorph.symm (time H a x) = time G a (r.homeomorph.symm x) := rfl
end Relabel

section Split
variable {V E L : Type*} (G : DirectedMultigraph V E) (p : E → L)


theorem outgoing_forget_time (a : ℤ) (z : History (ActualOutSplit.graph G p)) :
    ActualOutSplit.forget G p (time (ActualOutSplit.graph G p) a z) =
      time G a (ActualOutSplit.forget G p z) := rfl


theorem incoming_forget_time (a : ℤ) (z : History (ActualInSplit.graph G p)) :
    ActualInSplit.forget G p (time (ActualInSplit.graph G p) a z) =
      time G a (ActualInSplit.forget G p z) := rfl
end Split

section Positive
variable {n m : ℕ} (R : CountMat n m) (S : CountMat m n)

theorem positive_time (a : ℤ) (x : Path (R*S)) :
    elementaryHomeomorph R S (time (counted (R*S)) a x) =
      time (counted (S*R)) a (elementaryHomeomorph R S x) :=
  NumberedPositiveInverseLaws.positive_translate R S a x

end Positive
end D5.S3.ConceptDynamics.Coding.SplitTowerTranslation
