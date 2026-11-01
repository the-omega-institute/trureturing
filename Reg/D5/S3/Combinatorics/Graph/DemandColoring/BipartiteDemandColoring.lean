import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.DemandColoring.BipartiteDemandColoring
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Combinatorics.Graph.DemandColoring.BipartiteDemandColoring
open _root_.D5.S3.Combinatorics.Graph.DemandColoring.BipartiteDemandColoring
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
universe u
noncomputable section

abbrev signature : Signature where
  Params := Σ V : Type u, Σ G : SimpleGraph V, G.Coloring Bool × ℕ × (V → ℕ)
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p v => p.2.2.2.2 v) (fun e => nomatch e)
def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature.{u}
  Law R := ∀ {V : Type u} (G : SimpleGraph V) (b : G.Coloring Bool) (k : ℕ) (z : V → ℕ),
    (∀ v, z v ≤ k) → (∀ ⦃v w⦄, G.Adj v w → z v + z w ≤ k) →
    ∃ W : Fin k → V → Bool,
      (∀ c, G.IsIndepSet {v | W c v = true}) ∧
      ∀ v, (Finset.univ.filter (fun c => W c v = true)).card = R.readout () ⟨V, G, b, k, z⟩ v

def registration : Registration arena.{u} (type_of% (@exists_independent_layers.{u})) := by
  classical
  have hbad : ¬ arena.Law rejected.{u} := by
    intro h
    let G : SimpleGraph (ULift.{u} Unit) := ⊥
    let b : G.Coloring Bool := SimpleGraph.Coloring.mk (fun _ => false) (by simp [G])
    obtain ⟨W, _, count⟩ := h G b 0 (fun _ => 0) (by simp) (by simp [G])
    have impossible := count (ULift.up ())
    simpa [rejected, realize, signature] using impossible
  refine {
    actual := actual
    bridge := Iff.rfl
    variation := ⟨@exists_independent_layers.{u}, rejected, hbad⟩
    sensitivity := ?_
    dependence := ?_ }
  · constructor
    · intro i
      refine ⟨rejected, ?_, ?_, hbad⟩
      · intro j h; exact (h (Subsingleton.elim _ _)).elim
      · funext e; exact nomatch e
    · intro e; exact nomatch e
  · intro i
    let G : SimpleGraph (ULift.{u} Bool) := ⊥
    let b : G.Coloring Bool := SimpleGraph.Coloring.mk (fun _ => false) (by simp [G])
    refine ⟨⟨ULift.{u} Bool, G, b, 1, fun v => if v.down then 1 else 0⟩,
      ULift.up false, ULift.up true, ?_⟩
    decide

noncomputable def registration_1 :
    LeanInformationAudit.Contract.Registration
      (@exists_independent_layers.{u})
      (type_of% (realize signature.{u}
        (fun (_ : Unit) (p : signature.Params) (v : p.1) => p.2.2.2.2 v)
        (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Combinatorics.Graph.DemandColoring.BipartiteDemandColoring.exists_independent_layers.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.DemandColoring.BipartiteDemandColoring.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u}
    (fun (_ : Unit) (p : signature.Params) (v : p.1) => p.2.2.2.2 v)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.DemandColoring.BipartiteDemandColoring
    definition := none
    coordinates := #[0, 1, 2, 3, 4]
    readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body",
      "arg", "body", "arg", "body", "arg"], stateBinder := 8,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `relaxedAutoImplicit, value := .bool false }] }

end
end Reg.D5.S3.Combinatorics.Graph.DemandColoring.BipartiteDemandColoring
