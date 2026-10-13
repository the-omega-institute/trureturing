import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.Saturation.MatchingConeLeafUniversality
import Mathlib.Combinatorics.SimpleGraph.Star
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Combinatorics.Graph.Saturation.MatchingConeLeafUniversality

open _root_.D5.S3.Combinatorics.Graph.Saturation.MatchingConeLeafUniversality
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit SimpleGraph

universe u
noncomputable section

abbrev signature : Signature where
  Params := Σ V : Type u, SimpleGraph V
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} := realize signature
  (fun _ p v => p.2.IsUniversal v) (fun e => nomatch e)

def rejected : Realization signature.{u} := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj],
    Maximal H.Free G → G.edgeFinset.card ≤ Fintype.card V + 5 →
    ∀ {u v : V}, G.degree u = 1 → G.Adj u v → R.readout () ⟨V, G⟩ v

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  classical
  intro h
  let G : SimpleGraph (ULift.{u} (Fin 2)) := ⊤
  have hf : H.Free G := by
    rintro ⟨f⟩
    have hc := Fintype.card_le_of_injective f f.injective
    norm_num at hc
  have hm : Maximal H.Free G := ⟨hf, by intro J hj hle; exact le_top⟩
  have he : G.edgeFinset.card ≤ Fintype.card (ULift.{u} (Fin 2)) + 5 := by
    have hl := G.card_edgeFinset_le_card_choose_two
    norm_num at hl ⊢
    omega
  have hd : G.degree (ULift.up (0 : Fin 2)) = 1 := by
    apply degree_eq_one_iff_existsUnique_adj.mpr
    refine ⟨ULift.up 1, by simp [G], ?_⟩
    rintro ⟨w⟩ hw
    have hw0 : w ≠ 0 := by simpa [G, ne_comm] using hw
    congr
    omega
  exact h G hm he (u := ULift.up 0) (v := ULift.up 1) hd (by simp [G])

def registration : Registration arena.{u}
    (type_of% (@leaf_neighbor_isUniversal.{u})) where
  actual := actual
  bridge := by
    constructor <;> intro h V iF iD G iA hm he u v hd ha
    · exact h G hm he hd ha
    · exact h G hm he hd ha
  variation := ⟨by intro V iF iD G iA hm he u v hd ha
                   exact leaf_neighbor_isUniversal G hm he hd ha,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    let G : SimpleGraph (ULift.{u} (Fin 3)) := starGraph (ULift.up 0)
    refine ⟨⟨ULift.{u} (Fin 3), G⟩, ULift.up 0, ULift.up 1, ?_⟩
    change G.IsUniversal (ULift.up 0) ≠ G.IsUniversal (ULift.up 1)
    intro he
    have h0 : G.IsUniversal (ULift.up 0) := isUniversal_starGraph_self
    have h1 := he ▸ h0
    have ha := h1 (w := ULift.up 2) (by simp)
    simp [G] at ha

def registration_contract : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@leaf_neighbor_isUniversal.{u})
    (type_of% (realize signature.{u} (fun _ p v => p.2.IsUniversal v)
      (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Graph.Saturation.MatchingConeLeafUniversality.informationUnit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Saturation.MatchingConeLeafUniversality.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨registration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ p v => p.2.IsUniversal v)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    definition := none
    owner := `D5.S3.Combinatorics.Graph.Saturation.MatchingConeLeafUniversality
    coordinates := #[0, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body"]
      stateBinder := 8
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration

end
end Reg.D5.S3.Combinatorics.Graph.Saturation.MatchingConeLeafUniversality
