import D5.S3.Combinatorics.Graph.LinearForests.BipartiteCompletion
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! The original extension family, observing its actual containing graph. -/
namespace Reg.D5.S3.Combinatorics.Graph.LinearForests.BipartiteCompletion
open _root_.D5.S3.Combinatorics.Graph.LinearForests.BipartiteCompletion
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
universe u

abbrev signature : Signature where
  Params := Type u
  State V := SimpleGraph V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ V := SimpleGraph V
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ H => H) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => ⊥) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A B : Finset V),
    G.IsIndepSet (A : Set V) → G.IsIndepSet (B : Set V) →
    Disjoint A B → A ∪ B = univ → G.IsAcyclic →
    (∀ x, G.degree x ≤ 2) → A.card < B.card →
    ∃ H : SimpleGraph V, G ≤ R.readout () V H ∧ H.IsAcyclic ∧
      (∀ x, H.degree x ≤ 2) ∧ H.IsIndepSet (A : Set V) ∧
      H.IsIndepSet (B : Set V) ∧ ∀ x ∈ A, H.degree x = 2

private theorem source_bridge :
    (type_of% @exists_saturating_extension.{u}) ↔ arena.{u}.Law actual := by
  exact Iff.rfl

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  classical
  intro h
  let a : ULift.{u} (Fin 3) := ⟨0⟩
  let b : ULift.{u} (Fin 3) := ⟨1⟩
  let c : ULift.{u} (Fin 3) := ⟨2⟩
  let G : SimpleGraph (ULift.{u} (Fin 3)) := edge a b
  have hA : G.IsIndepSet (({a} : Finset (ULift.{u} (Fin 3))) : Set _) := by
    simp [SimpleGraph.IsIndepSet, Set.Pairwise]
  have hB : G.IsIndepSet (({b, c} : Finset (ULift.{u} (Fin 3))) : Set _) := by
    intro x hx y hy hne hxy
    simp only [mem_coe, mem_insert, mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
      simp [G, edge_adj, a, b, c] at hxy
  have hdis : Disjoint ({a} : Finset _) {b, c} := by simp [a, b, c]
  have hcover : ({a} : Finset _) ∪ {b, c} = univ := by
    ext x
    rcases x with ⟨x⟩
    fin_cases x <;> simp [a, b, c]
  have hacyc : G.IsAcyclic := by
    have hn : ¬ (⊥ : SimpleGraph (ULift.{u} (Fin 3))).Reachable a b := by
      simp [a, b]
    simpa [G] using (isAcyclic_bot.sup_edge_of_not_reachable hn)
  have hdegree : ∀ x, G.degree x ≤ 2 := by
    intro x
    have hx := G.degree_lt_card_verts x
    simpa only [Fintype.card_ulift, Fintype.card_fin, ← ncard_neighborSet,
      Nat.lt_succ_iff] using hx
  obtain ⟨H, hle, _⟩ := h G {a} {b, c} hA hB hdis hcover hacyc
    (by simpa only [← ncard_neighborSet] using hdegree) (by simp [b, c])
  have hadj : G.Adj a b := by simp [G, edge_adj, a, b]
  have hf := hle hadj
  change (⊥ : SimpleGraph (ULift.{u} (Fin 3))).Adj a b at hf
  exact hf

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨ULift.{u} (Fin 2), ⊥, ⊤, ?_⟩
  intro h
  change (⊥ : SimpleGraph (ULift.{u} (Fin 2))) = ⊤ at h
  have hh := congrArg (fun H : SimpleGraph (ULift.{u} (Fin 2)) => H.Adj ⟨0⟩ ⟨1⟩) h
  simp at hh

def family : Registration arena.{u} (type_of% @exists_saturating_extension.{u}) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp @exists_saturating_extension.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@exists_saturating_extension.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.LinearForests.BipartiteCompletion.unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.LinearForests.BipartiteCompletion.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ _ H => H) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.LinearForests.BipartiteCompletion
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "arg", "body", "fn", "arg", "arg"]
      stateBinder := 13
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.Graph.LinearForests.BipartiteCompletion
