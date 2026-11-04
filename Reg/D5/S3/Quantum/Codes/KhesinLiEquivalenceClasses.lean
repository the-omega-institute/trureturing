import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Codes.KhesinLiEquivalenceClasses
import Reg.Support.UniverseSingleReadout

/-! Source-bound registrations of the selected public mathematical statements. -/

namespace Reg.D5.S3.Quantum.Codes.KhesinLiEquivalenceClasses
open _root_.D5.S3.Quantum.Codes.KhesinLiEquivalenceClasses
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open _root_.D5.S3.Quantum.Entanglement.GraphStateMonogamyForbiddenSubgraph (lc)
namespace LocalComplement

/-- Observe local complementation at the selected vertex as the graph varies. -/
abbrev signature : Signature :=
  Reg.Support.UniverseSingleReadout.signature (Σ V : Type, V)
    (fun p => SimpleGraph p.1) (fun p => SimpleGraph p.1)

def actual : Realization signature :=
  realize signature (fun _ p G => lc G (Sigma.snd p)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => ⊤) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {V : Type} (G : SimpleGraph V) (v : V),
    R.readout () ⟨V, v⟩ G =
      SimpleGraph.fromRel (fun x y => Xor (G.Adj x y) (G.Adj v x ∧ G.Adj v y))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h (⊥ : SimpleGraph Bool) false
  have edge : (⊤ : SimpleGraph Bool).Adj false true := by simp
  change (⊤ : SimpleGraph Bool) = _ at he
  rw [he] at edge
  rcases edge.2 with h | h <;> exact h.elim And.left (fun h => h.1.1)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨Bool, false⟩, ⊥, ⊤, ?_⟩
  intro h
  have he := congrArg (fun G : SimpleGraph Bool => G.Adj false true) h
  change (lc (⊥ : SimpleGraph Bool) false).Adj false true =
    (lc (⊤ : SimpleGraph Bool) false).Adj false true at he
  simp [lc] at he

def source_registration : Registration arena (type_of% (@lc_source)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@lc_source, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@lc_source) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Codes.KhesinLiEquivalenceClasses.LocalComplement.unit
  realizationName := Lean.Name.str
    `Reg.D5.S3.Quantum.Codes.KhesinLiEquivalenceClasses.LocalComplement "source_registration"
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
    owner := `D5.S3.Quantum.Codes.KhesinLiEquivalenceClasses
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end LocalComplement
end
end Reg.D5.S3.Quantum.Codes.KhesinLiEquivalenceClasses
