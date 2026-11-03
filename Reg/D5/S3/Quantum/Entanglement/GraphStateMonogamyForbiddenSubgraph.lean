import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.GraphStateMonogamyForbiddenSubgraph
import Reg.Support.UniverseSingleReadout

/-! Source-bound registrations of the selected public mathematical statements. -/

namespace Reg.D5.S3.Quantum.Entanglement.GraphStateMonogamyForbiddenSubgraph
open _root_.D5.S3.Quantum.Entanglement.GraphStateMonogamyForbiddenSubgraph
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace EntropyProfile

/-- Evaluate the entropy profile at the selected vertex set. -/
abbrev signature : Signature :=
  Reg.Support.UniverseSingleReadout.signature (Σ V : Type, Finset V)
    (fun p => Finset p.1 → ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ p f => f (Sigma.snd p)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨Unit, ∅⟩, (fun _ => 0), (fun _ => 1), ?_⟩
  exact Nat.zero_ne_one

private theorem entropy_bot {V : Type} [Fintype V] [DecidableEq V] (A : Finset V) :
    entropy (⊥ : SimpleGraph V) A = 0 := by
  have hz : cut (⊥ : SimpleGraph V) A = 0 := by
    ext a b
    simp only [cut, Matrix.submatrix_apply, SimpleGraph.adjMatrix_apply,
      SimpleGraph.bot_adj, ite_false, Matrix.zero_apply]
  unfold entropy
  rw [hz, Matrix.rank_zero]

end EntropyProfile

namespace Complement
open EntropyProfile

abbrev arena : Arena where
  signature := signature

  Law R := ∀ {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A : Finset V),
      entropy G Aᶜ = R.readout () ⟨V, A⟩ (entropy G)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h (⊥ : SimpleGraph Unit) ∅
  change entropy (⊥ : SimpleGraph Unit) _ = 1 at he
  rw [entropy_bot] at he
  exact Nat.zero_ne_one he

def source_registration : Registration arena (type_of% (@compl_eq)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@compl_eq, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@compl_eq) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.GraphStateMonogamyForbiddenSubgraph.Complement.unit
  realizationName := Lean.Name.str
    `Reg.D5.S3.Quantum.Entanglement.GraphStateMonogamyForbiddenSubgraph.Complement
    "source_registration"
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.GraphStateMonogamyForbiddenSubgraph
    definition := none
    coordinates := #[0, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end Complement

namespace Relabel
open EntropyProfile

abbrev arena : Arena where
  signature := signature

  Law R := ∀ {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (e : W ≃ V) (A : Finset W),
      R.readout () ⟨W, A⟩ (entropy (G.comap e)) = entropy G (A.map e.toEmbedding)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h (⊥ : SimpleGraph Unit) (Equiv.refl Unit) ∅
  change 1 = entropy (⊥ : SimpleGraph Unit) _ at he
  rw [entropy_bot] at he
  exact Nat.one_ne_zero he

def source_registration : Registration arena (type_of% (@relabel)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@relabel, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@relabel) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.GraphStateMonogamyForbiddenSubgraph.Relabel.unit
  realizationName := Lean.Name.str
    `Reg.D5.S3.Quantum.Entanglement.GraphStateMonogamyForbiddenSubgraph.Relabel
    "source_registration"
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.GraphStateMonogamyForbiddenSubgraph
    definition := none
    coordinates := #[1, 8]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end Relabel

namespace LocalComplement
open EntropyProfile

abbrev arena : Arena where
  signature := signature

  Law R := ∀ {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (v : V) (A : Finset V),
      R.readout () ⟨V, A⟩ (entropy (lc G v)) = entropy G A

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h (⊥ : SimpleGraph Unit) () ∅
  change 1 = entropy (⊥ : SimpleGraph Unit) ∅ at he
  rw [entropy_bot] at he
  exact Nat.one_ne_zero he

def source_registration : Registration arena (type_of% (@lc_eq)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@lc_eq, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@lc_eq) (Realization signature) Unit Unit := {
  unitName := Lean.Name.str
    `Reg.D5.S3.Quantum.Entanglement.GraphStateMonogamyForbiddenSubgraph.LocalComplement "unit"
  realizationName := Lean.Name.str
    `Reg.D5.S3.Quantum.Entanglement.GraphStateMonogamyForbiddenSubgraph.LocalComplement
    "source_registration"
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.GraphStateMonogamyForbiddenSubgraph
    definition := none
    coordinates := #[0, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end LocalComplement

end
end Reg.D5.S3.Quantum.Entanglement.GraphStateMonogamyForbiddenSubgraph
