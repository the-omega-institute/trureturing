import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.Saturation.MatchingConeLeafExistence
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Combinatorics.Graph.Saturation.MatchingConeLeafExistence

open _root_.D5.S3.Combinatorics.Graph.Saturation.MatchingConeLeafUniversality
open _root_.D5.S3.Combinatorics.Graph.Saturation.MatchingConeLeafExistence
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit SimpleGraph

universe u
noncomputable section

abbrev signature : Signature where
  Params := Σ V : Type u, Fintype V × DecidableEq V ×
    (Σ G : SimpleGraph V, DecidableRel G.Adj)
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} := realize signature
  (fun _ p v => by
    letI := p.2.1
    letI := p.2.2.1
    letI := p.2.2.2.2
    exact p.2.2.2.1.degree v = 1) (fun e => nomatch e)

def rejected : Realization signature.{u} := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {V : Type u} [iF : Fintype V] [iD : DecidableEq V]
    (G : SimpleGraph V) [iA : DecidableRel G.Adj],
    Maximal H.Free G → 20 ≤ Fintype.card V →
    G.edgeFinset.card ≤ Fintype.card V + 5 → ∃ v, R.readout () ⟨V, iF, iD, G, iA⟩ v

theorem source_bridge : (type_of% (@exists_degree_one.{u})) ↔ arena.{u}.Law actual := by
  constructor <;> intro h V iF iD G iA hm hn he
  · exact h G hm hn he
  · exact h G hm hn he

theorem actual_law : arena.{u}.Law actual := by
  intro V iF iD G iA hm hn he
  exact exists_degree_one G hm hn he

/-- The standard cone over two triangles and thirteen isolated base vertices. -/
def witness : SimpleGraph (ULift.{u} (Fin 20)) where
  Adj x y := x ≠ y ∧ (x.down = 0 ∨ y.down = 0 ∨
    (x.down.val ≤ 3 ∧ y.down.val ≤ 3) ∨
    (4 ≤ x.down.val ∧ x.down.val ≤ 6 ∧ 4 ≤ y.down.val ∧ y.down.val ≤ 6))
  symm := ⟨by intro x y; aesop⟩
  loopless := ⟨by intro x; simp⟩

instance witness_decidable : DecidableRel witness.{u}.Adj := fun x y => by
  dsimp [witness]
  infer_instance

theorem witness_order : Fintype.card (ULift.{u} (Fin 20)) = 20 := by decide

theorem witness_edges : witness.{u}.edgeFinset.card = 25 := by decide

theorem observational_dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨⟨ULift.{u} (Fin 20), inferInstance, inferInstance,
    witness.{u}, witness_decidable⟩, ULift.up 7, ULift.up 1, ?_⟩
  change (witness.degree (ULift.up 7) = 1) ≠ (witness.degree (ULift.up 1) = 1)
  have hl : witness.{u}.degree (ULift.up 7) = 1 := by decide
  have ht : witness.{u}.degree (ULift.up 1) = 3 := by decide
  simp only [hl, ht]
  decide

#print axioms source_bridge
#print axioms actual_law
#print axioms observational_dependence

end
end Reg.D5.S3.Combinatorics.Graph.Saturation.MatchingConeLeafExistence
