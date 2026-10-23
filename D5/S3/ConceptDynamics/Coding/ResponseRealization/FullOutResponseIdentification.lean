/- GID: D5/S3/ConceptDynamics/Coding/ResponseRealization/FullOutResponseIdentification
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/ResponseRealization/FullOutResponseIdentification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Repeated full outgoing splits identify with the original response graph and its unchanged finite edge numbering on every history. -/

/- Identify the actual full outgoing tower with the response graph and its existing numbered edges. Both finite graph maps and their full-history equation are constructed. -/
import D5.S3.ConceptDynamics.Coding.FullOutSplitWordIdentification
import D5.S3.ConceptDynamics.Coding.ResponseGraphs.OriginalResponseGraph
import D5.S3.ConceptDynamics.Coding.ResponseRealization.CentredResponseCorrection
import D5.S3.ConceptDynamics.Coding.PositiveRecoding.FiniteGraphRelabelHomeomorph

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

namespace D5.S3.ConceptDynamics.Coding.FullOutResponseIdentification
open EssentialWordRealization FiniteWindowTableCriterion StandardBeamHomeomorphisms
open ZeroWindowRelabeling (Relabel)
open TwoSidedFiniteInduction (Presentation Hist)
open RepeatedFullOutSplit
open OriginalResponseGraph OriginalResponseNumbering

variable (F : Presentation) {a b c d : ℕ}
variable (pair : TablePair F.graph F.graph a b c d)

/-- The output is forced. The inverse retains the entire original word,
not just its endpoints or its table response. -/
private def wordResponse : LegalWord F.graph (a+b+1+1) ≃ ResponseEdge F.graph pair where
  toFun := makeEdge F.graph pair
  invFun := edgeWord F.graph pair
  left_inv _ := rfl
  right_inv e := by
    apply Subtype.ext
    exact Prod.ext rfl e.property.symm

/-- Both finite equivalences and both endpoint equations are constructed
from the actual (a+b+1)-fold id outsplit, not supplied as an input. -/
def responseIdentification : Relabel (stage F (a+b+1)).graph (graph F.graph pair) where
  vertex := (identification F (a+b+1)).vertex
  edge := (identification F (a+b+1)).edge.trans (wordResponse F pair)
  source e := (identification F (a+b+1)).source e
  target e := (identification F (a+b+1)).target e

/-- Equality induced by the finite graph identification on the actual
repeated lift, proved before consulting the older uncentred U. -/
theorem response_coordinate (x : Hist F) (t : ℤ) :
    ((responseIdentification F pair).history (repeated F (a+b+1) x)).val t =
      makeEdge F.graph pair (historyWindow F.graph x t (a+b+1+1)) := by
  change makeEdge F.graph pair
    ((identification F (a+b+1)).edge ((repeated F (a+b+1) x).val t)) = _
  rw [flatten_window]

/-- Reuse the existing exact enumeration. This is only the endpoint
computation hidden by its private helper, not a new numbering supplier. -/
private theorem decode_endpoints (e : CountedMatrixOverlap.Edge (matrix F.graph pair)) :
    endpoints F.graph pair (edgeEquiv F.graph pair e) = (e.source,e.target) :=
  ((Fintype.equivFin (Fibre F.graph pair e.source e.target)).symm e.number).property

private def numbering : Relabel (graph F.graph pair) (countedGraph F.graph pair) where
  vertex := vertexNumber F.graph
  edge := (edgeEquiv F.graph pair).symm
  source e := by
    have h := decode_endpoints F pair ((edgeEquiv F.graph pair).symm e)
    rw [(edgeEquiv F.graph pair).apply_symm_apply] at h
    exact (congrArg Prod.fst h).symm
  target e := by
    have h := decode_endpoints F pair ((edgeEquiv F.graph pair).symm e)
    rw [(edgeEquiv F.graph pair).apply_symm_apply] at h
    exact (congrArg Prod.snd h).symm

/-- The actual numbered input, with its existing finite vertex numbering
and every existing parallel-edge number. No count matrix is redefined. -/
def numberedIdentification :
    Relabel (stage F (a+b+1)).graph (countedGraph F.graph pair) where
  vertex := (responseIdentification F pair).vertex.trans (numbering F pair).vertex
  edge := (responseIdentification F pair).edge.trans (numbering F pair).edge
  source e := ((numbering F pair).source ((responseIdentification F pair).edge e)).trans
    (congrArg (vertexNumber F.graph) ((responseIdentification F pair).source e))
  target e := ((numbering F pair).target ((responseIdentification F pair).edge e)).trans
    (congrArg (vertexNumber F.graph) ((responseIdentification F pair).target e))




/-- Defined from the actual repeated outsplit followed by the constructed
finite numbered graph identification. It does not reuse inputHomeomorph. -/
def uncentredRepeatedLift : Hist F ≃ₜ CountedMatrixOverlap.Path (matrix F.graph pair) :=
  (repeated F (a+b+1)).trans (numberedIdentification F pair).homeomorph

theorem numbered_coordinate (x : Hist F) (t : ℤ) :
    edgeEquiv F.graph pair ((uncentredRepeatedLift F pair x).val t) =
      makeEdge F.graph pair (historyWindow F.graph x t (a+b+1+1)) := by
  change edgeEquiv F.graph pair ((edgeEquiv F.graph pair).symm
    ((responseIdentification F pair).edge ((repeated F (a+b+1) x).val t))) = _
  rw [(edgeEquiv F.graph pair).apply_symm_apply]
  exact response_coordinate F pair x t

/-- Comparison with the older U is a consequence of the actual finite
construction and its coordinates, not the definition of the new lift. -/
theorem agrees_existing_uncentred (x : Hist F) :
    uncentredRepeatedLift F pair x = CentredResponseCorrection.uncentred F.graph pair x := by
  apply Subtype.ext
  funext t
  apply (edgeEquiv F.graph pair).injective
  rw [numbered_coordinate,CentredResponseCorrection.uncentred_coordinate]

/-- Exact handoff to the existing centred input, on every legal history.
The sign is -a. No accumulated word shift is claimed. -/
theorem numberedLift_eq_repeated_negative (x : Hist F) :
    numberedLift F.graph pair x =
      uncentredRepeatedLift F pair (translate F.graph (-(a:ℤ)) x) := by
  rw [agrees_existing_uncentred]
  exact CentredResponseCorrection.centred_eq_uncentred_negative F.graph pair x

/-- The identical equation using the predecessor's concrete Tower evaluator. -/
theorem numberedLift_eq_tower_negative (x : Hist F) :
    numberedLift F.graph pair x = (numberedIdentification F pair).history
      ((tower F (a+b+1)).toHomeomorph (translate F.graph (-(a:ℤ)) x)) := by
  rw [tower_apply,numberedLift_eq_repeated_negative] <;> rfl

end D5.S3.ConceptDynamics.Coding.FullOutResponseIdentification
