/- GID: D5/S3/ConceptDynamics/Coding/ResponseRealization/ResponseTwoSidedConsumer
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/ResponseRealization/ResponseTwoSidedConsumer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual response output is reduced to two concrete finite split towers and a terminal finite graph relabeling. -/

/- Combine the actual response graph, its first outgoing step and the existing two-sided reduction into the concrete terminal data. -/
import D5.S3.ConceptDynamics.Coding.TwoSidedFiniteInduction
import D5.S3.ConceptDynamics.Coding.ResponseRealization.ResponseOutSplitConsumer

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace D5.S3.ConceptDynamics.Coding.ResponseTwoSidedConsumer
open EssentialWordRealization FiniteWindowTableCriterion
open OriginalResponseNumbering ResponseOutSplitConsumer
open TwoSidedFiniteInduction
variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable [TopologicalSpace E] [DiscreteTopology E]
variable (G : DirectedMultigraph V E) (hG : Essential G)
variable {a b c d : ℕ} (pair : TablePair G G a b c d) (S : SameTableConjugacy pair)

def original : Presentation where
  V := V
  E := E
  finiteV := inferInstance
  finiteE := inferInstance
  eqV := inferInstance
  eqE := inferInstance
  topology := inferInstance
  discrete := inferInstance
  graph := G
  essential := hG

def response : Presentation where
  V := Fin (OriginalResponseNumbering.Size (G := G) (a := a) (b := b))
  E := CountedMatrixOverlap.Edge (matrix G pair)
  finiteV := inferInstance
  finiteE := inferInstance
  eqV := inferInstance
  eqE := Classical.decEq _
  topology := inferInstance
  discrete := inferInstance
  graph := countedGraph G pair
  essential := (numbered_response_reduction G pair hG S).1

/-- Concrete terminal towers for the ACTUAL response output, including the
already completed first step. Exactly (a+c)+(b+d+1) actual steps on each side. -/
def terminal : Terminal (response G hG pair S) (original G hG)
    (numberedOutput G pair S (local_of_conjugacy hG hG pair S).seamG)
    ((a+c)+(b+d+1)) := by
  let F := response G hG pair S
  let H := original G hG
  letI : DiscreteTopology H.E := H.discrete
  let C := local_of_conjugacy hG hG pair S
  let cb : OutSplitConjugacyDecrease.Code F.graph H.graph := responseCode G pair C.seamG
  let P : Hist F ≃ₜ Hist H := numberedOutput G pair S C.seamG
  let F' := out F H cb.edge
  let H' := out H H id
  let cp := OutSplitConjugacyDecrease.splitCode cb
  let P' : Hist F' ≃ₜ Hist H' := splitOutput G pair hG S
  have hp' : ∀ x t, (P' x).val t = cp.edge (x.val t) := by
    apply OutSplitConjugacyDecrease.changed_one_block
    intro x t
    rfl
  let Q' : LegalWord H'.graph ((a+c)+(b+d)+1) → F'.E := splitRecover G pair hG S
  have hq' : ∀ y t, Q' (historyWindow H'.graph y (t-((a+c:ℕ):ℤ)) ((a+c)+(b+d)+1)) =
      (P'.symm y).val t := response_recovery G pair hG S
  let r := reduce ((a+c)+(b+d)) F' H' cp P' hp' (a+c) (b+d) Q' hq' rfl
  refine ⟨r.source,r.target,.outgoing H cb.edge r.left,.outgoing H id r.right,
    r.relabel,?_,?_,?_⟩
  · change r.left.length+1 = _
    rw [r.source_depth]
    omega
  · change r.right.length+1 = _
    rw [r.target_depth]
    omega
  · intro z
    have hs := r.square (ActualOutSplit.lift F.graph cb.edge z)
    change r.right.toHomeomorph
      (OutSplitConjugacyDecrease.changed cb P (ActualOutSplit.lift F.graph cb.edge z)) = _ at hs
    exact (congrArg r.right.toHomeomorph (OutSplitConjugacyDecrease.square cb P z)).symm.trans hs

end D5.S3.ConceptDynamics.Coding.ResponseTwoSidedConsumer
