/- GID: Reg/D5/S3/Combinatorics/Graph/Hypercube/EdgeExpansion
   generality: G
   mirror-B: none
   mirror-E: none
   anchors: []
   utility: none
   digest: A source-bound audit of the Boolean cube crossing-edge count. -/

import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.Hypercube.EdgeExpansion
import Reg.Support.SingleDependentReadout

/-! The dependent state is the chosen vertex set, and the observation is its
actual crossing-edge cardinality. The whole family ranges over all dimensions. -/

noncomputable section
open _root_.D5.S3.Combinatorics.Graph.Hypercube.EdgeExpansion
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Combinatorics.Graph.Hypercube.EdgeExpansion

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ (fun n => Finset (Vertex n)) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ n W => (boundaryEdges n W).card) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (W : Finset (Vertex n)), min W.card (2 ^ n - W.card) ≤ R.readout () n W

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 1 {((false, ()) : Vertex 1)}
  change min ({((false, ()) : Vertex 1)} : Finset (Vertex 1)).card
    (2 ^ 1 - ({((false, ()) : Vertex 1)} : Finset (Vertex 1)).card) ≤ 0 at hh
  norm_num at hh

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, ∅, {((false, ()) : Vertex 1)}, ?_⟩
  intro h
  change (boundaryEdges 1 ∅).card = (boundaryEdges 1 {((false, ()) : Vertex 1)}).card at h
  have he : (boundaryEdges 1 ∅).card = 0 := by simp [boundaryEdges]
  have hp : 1 ≤ (boundaryEdges 1 {((false, ()) : Vertex 1)}).card := by
    simpa using edge_expansion 1 {((false, ()) : Vertex 1)}
  exact (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hp)) (h.symm.trans he)

def family : Registration arena (type_of% (@edge_expansion)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨edge_expansion, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
    (@edge_expansion) (Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.Hypercube.EdgeExpansion.edge_expansion.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Hypercube.EdgeExpansion.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ n W => (boundaryEdges n W).card) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Hypercube.EdgeExpansion
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end Reg.D5.S3.Combinatorics.Graph.Hypercube.EdgeExpansion
