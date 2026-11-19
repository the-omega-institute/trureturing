import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Graph.Incidence.ZhengWuOddLineTree
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Combinatorics.Graph.Incidence.ZhengWuOddLineTree

open _root_.D5.S3.Combinatorics.Graph.Incidence.ZhengWuOddLineTree (result)
open _root_.D5.S3.Combinatorics.Graph.Incidence.EndpointSplit (EndpointPartition)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit SimpleGraph
open scoped Sym2

noncomputable section

-- A two-edge path gives a positive instance of the entire source law.
private def twoEdgeRoot : SimpleGraph (Fin 3) := fromEdgeSet {s(0, 1), s(1, 2)}

private def e01 : twoEdgeRoot.edgeSet :=
  ⟨s(0, 1), (fromEdgeSet_adj _).2 ⟨Or.inl rfl, by decide⟩⟩

private def e12 : twoEdgeRoot.edgeSet :=
  ⟨s(1, 2), (fromEdgeSet_adj _).2 ⟨Or.inr rfl, by decide⟩⟩

private theorem e01_ne_e12 : e01 ≠ e12 := by
  intro h
  have he : s((0 : Fin 3), 1) = s(1, 2) := congrArg Subtype.val h
  have hz : (0 : Fin 3) ∈ s((1 : Fin 3), 2) := he ▸ Sym2.mem_mk_left (0 : Fin 3) 1
  simp at hz

private theorem eq_e01_or_e12 (e : twoEdgeRoot.edgeSet) : e = e01 ∨ e = e12 := by
  have h := e.property
  change e.val ∈ (fromEdgeSet ({s(0, 1), s(1, 2)} : Set (Sym2 (Fin 3)))).edgeSet at h
  rw [edgeSet_fromEdgeSet] at h
  rcases h.1 with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

private def fromFin (i : Fin 2) : twoEdgeRoot.edgeSet := if i = 0 then e01 else e12

private noncomputable def edgeEquiv : Fin 2 ≃ twoEdgeRoot.edgeSet :=
  Equiv.ofBijective fromFin ⟨by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [fromFin, e01_ne_e12, e01_ne_e12.symm],
    fun e => (eq_e01_or_e12 e).elim (fun h => ⟨0, h.symm⟩) (fun h => ⟨1, h.symm⟩)⟩

private theorem twoEdgeRoot_card : Nat.card twoEdgeRoot.edgeSet = 2 := by
  rw [Nat.card_congr edgeEquiv.symm, Nat.card_fin]

private theorem twoEdgeRoot_odd_tree :
    ∃ H : SimpleGraph twoEdgeRoot.edgeSet, H ≤ twoEdgeRoot.lineGraph ∧ H.IsTree ∧
      ∀ e, Odd (Nat.card (H.neighborSet e)) := by
  let H := (pathGraph 2).comap edgeEquiv.symm
  let iso : H ≃g pathGraph 2 := Iso.comap edgeEquiv.symm _
  refine ⟨H, ?_, iso.isTree_iff.mpr (isTree_pathGraph_add_one 1), ?_⟩
  · intro e f h
    have hef : e ≠ f := Adj.ne h
    rcases eq_e01_or_e12 e with he | he <;>
      rcases eq_e01_or_e12 f with hf | hf
    · exact (hef (he.trans hf.symm)).elim
    · subst e
      subst f
      exact lineGraph_adj_iff_exists.mpr ⟨hef, 1, Sym2.mem_mk_right _ _, Sym2.mem_mk_left _ _⟩
    · subst e
      subst f
      exact lineGraph_adj_iff_exists.mpr ⟨hef, 1, Sym2.mem_mk_left _ _, Sym2.mem_mk_right _ _⟩
    · exact (hef (he.trans hf.symm)).elim
  · intro e
    rw [Nat.card_congr (iso.mapNeighborSet e)]
    generalize iso e = i
    have hcard (j : Fin 2) : Nat.card ((pathGraph 2).neighborSet j) = 1 := by
      fin_cases j
      · change Nat.card ((pathGraph 2).neighborSet 0) = 1
        rw [show (pathGraph 2).neighborSet 0 = {1} by
              ext x
              fin_cases x <;> decide]
        exact Nat.card_unique
      · change Nat.card ((pathGraph 2).neighborSet 1) = 1
        rw [show (pathGraph 2).neighborSet 1 = {0} by
              ext x
              fin_cases x <;> decide]
        exact Nat.card_unique
    rw [hcard]
    decide

/-- The root edge-set observation used in the positive-size conjunct. -/
abbrev signature : Signature where
  Params := Type
  State V := Set (Sym2 V)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ edges => Nat.card edges) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- The complete source equivalence with one selected edge-count observation. -/
abbrev arena : Arena where
  signature := signature
  Law O := ∀ {V : Type} [Finite V] (F : SimpleGraph V),
    (∃ H : SimpleGraph F.edgeSet, H ≤ F.lineGraph ∧ H.IsTree ∧
      ∀ e, Odd (Nat.card (H.neighborSet e))) ↔
    (0 < O.readout () V F.edgeSet ∧ Even (Nat.card F.edgeSet) ∧
      ∃ P : EndpointPartition F, P.splitGraph.IsTree ∧
        ∀ b : P.Block, 2 ≤ Nat.card (P.splitGraph.neighborSet b) →
          2 ≤ Nat.card {C : (P.splitGraph.induce {x | x ≠ b}).ConnectedComponent //
            Odd (Nat.card C.supp)})

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hp := ((h twoEdgeRoot).mp twoEdgeRoot_odd_tree).1
  exact (Nat.lt_irrefl 0) hp

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  have ho : Nat.card (∅ : Set (Sym2 (Fin 3))) = 0 :=
    Nat.card_eq_zero.mpr (Or.inl ⟨fun e => e.property⟩)
  refine ⟨Fin 3, twoEdgeRoot.edgeSet, ∅, ?_⟩
  change Nat.card twoEdgeRoot.edgeSet ≠ Nat.card (∅ : Set (Sym2 (Fin 3)))
  rw [twoEdgeRoot_card, ho]
  decide

def family : Registration arena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@result) (Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.Incidence.ZhengWuOddLineTree.result.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Incidence.ZhengWuOddLineTree.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ edges => Nat.card edges) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Incidence.ZhengWuOddLineTree
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms registration

end
end Reg.D5.S3.Combinatorics.Graph.Incidence.ZhengWuOddLineTree
