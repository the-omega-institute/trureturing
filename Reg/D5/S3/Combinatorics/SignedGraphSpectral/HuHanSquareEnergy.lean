import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.SignedGraphSpectral.HuHanSquareEnergy

/-! Source-bound readouts for both signed square-energy equality clauses. -/

namespace Reg.D5.S3.Combinatorics.SignedGraphSpectral.HuHanSquareEnergy

open LeanInformationAudit
open _root_.D5.S3.Combinatorics.SignedGraphSpectral.HuHanSquareEnergy
open _root_.D5.S3.Combinatorics.SignedGraphSpectral.MO479815 (signedAdj)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section

private abbrev signature : Signature where
  Params := Σ n : ℕ, SimpleGraph (Fin n)
  State p := Sym2 (Fin p.1) → Bool
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization signature :=
  realize signature (fun _ p σ => sPlus p.2 σ) (fun e => nomatch e)

private def rejected (role : Bool) : Realization signature :=
  realize signature (fun i p σ => if i = role then 1 else sPlus p.2 σ) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ {n : ℕ} (G : SimpleGraph (Fin n)) (σ : Sym2 (Fin n) → Bool), G.Connected →
    (r.readout false ⟨n, G⟩ σ = endpoint G ↔ G.IsTree ∨ (G = ⊤ ∧ Balanced G σ)) ∧
    (r.readout true ⟨n, G⟩ σ = (n : ℝ) - 1 ↔ G.IsTree ∨ (G = ⊤ ∧ Antibalanced G σ))

private theorem rejected_law (role : Bool) : ¬ arena.Law (rejected role) := by
  intro h
  have ht : (⊥ : SimpleGraph (Fin 1)).IsTree :=
    ⟨⟨SimpleGraph.Preconnected.of_subsingleton⟩, SimpleGraph.isAcyclic_bot⟩
  have hc := h (⊥ : SimpleGraph (Fin 1)) (fun _ => true) ht.1
  cases role
  · have he := hc.1.2 (Or.inl ht)
    simp only [rejected, realize, ite_true, endpoint, Nat.cast_one, sub_add_cancel,
      SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card, SimpleGraph.edgeSet_bot] at he
    norm_num at he
  · have he := hc.2.2 (Or.inl ht)
    norm_num [rejected, realize] at he

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  let G : SimpleGraph (Fin 3) := ⊤
  refine ⟨⟨3, G⟩, fun _ => true, fun _ => false, ?_⟩
  have hc := SimpleGraph.connected_top (V := Fin 3)
  have hpos : Balanced G (fun _ => true) := by
    refine ⟨fun _ => 1, fun _ => Or.inl rfl, ?_⟩
    intro i j hij
    simp [signedAdj, hij]
  have hneg : Antibalanced G (fun _ => false) := by
    refine ⟨fun _ => 1, fun _ => Or.inl rfl, ?_⟩
    intro i j hij
    simp [signedAdj, hij]
  have h1 := (result G (fun _ => true) hc).1.2 (Or.inr ⟨rfl, hpos⟩)
  have h2 := (result G (fun _ => false) hc).2.2 (Or.inr ⟨rfl, hneg⟩)
  change sPlus G (fun _ => true) ≠ sPlus G (fun _ => false)
  rw [h1, h2]
  unfold endpoint
  dsimp only [G]
  simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card]
  have cardEdges : Nat.card (⊤ : SimpleGraph (Fin 3)).edgeSet = 3 := by
    rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card,
      SimpleGraph.card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin]
    decide
  rw [cardEdges]
  norm_num

def family : Registration arena (type_of% (@result)) where
  actual := realize signature (fun _ p σ => sPlus p.2 σ) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨@result, rejected false, rejected_law false⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected i, ?_, rfl, rejected_law i⟩
      intro j h
      funext p σ
      exact (ite_eq_right h).symm
    · intro i
      exact nomatch i
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Combinatorics.SignedGraphSpectral.HuHanSquareEnergy.result) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.SignedGraphSpectral.HuHanSquareEnergy.result_unit
  realizationName := `Reg.D5.S3.Combinatorics.SignedGraphSpectral.HuHanSquareEnergy.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p σ => sPlus p.2 σ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.SignedGraphSpectral.HuHanSquareEnergy
    definition := none
    coordinates := #[0, 1]
    readouts := #[{ path := #["body", "body", "body", "body", "fn", "arg", "fn", "arg", "fn", "arg"], stateBinder := 2, functionOperand := false, stateOperand := none, booleanPredicate := false },
      { path := #["body", "body", "body", "body", "arg", "fn", "arg", "fn", "arg"], stateBinder := 2, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }]

end

end Reg.D5.S3.Combinatorics.SignedGraphSpectral.HuHanSquareEnergy
