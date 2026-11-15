import D5.S3.Combinatorics.Graph.StarForming.TripleModule
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

noncomputable section
open Classical LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Graph.StarForming.TripleModule
open _root_.D5.S3.Combinatorics.Graph.StarFormingDissociationRefutation

namespace Reg.D5.S3.Combinatorics.Graph.StarForming.TripleModule

abbrev signature : Signature where
  Params := Unit
  State _ := Finset (Fin 48)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def observation : ∀ (_ : Unit) (_ : Unit), Finset (Fin 48) → ℕ := fun _ _ S => S.card

def noAnchor : ∀ (_ : Empty) (_ : Unit), Finset (Fin 48) := fun e => nomatch e

def actual : Realization signature := realize signature observation noAnchor

def bad : Realization signature := realize signature (fun _ _ _ => 27) noAnchor

abbrev arena : Arena where
  signature := signature
  Law r := ∀ S : Finset (Fin 48), IsKIndependent graph 2 S →
    r.readout () () S ≤ 26

private theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hi : IsKIndependent graph 2 (∅ : Finset (Fin 48)) := by simp [IsKIndependent]
  have hh := h ∅ hi
  change (27 : ℕ) ≤ 26 at hh
  exact (by decide : ¬ (27 : ℕ) ≤ 26) hh

abbrev SourceClaim : Prop := ∀ S : Finset (Fin 48), IsKIndependent graph 2 S →
  S.card ≤ 26

def family : Registration arena SourceClaim where
  actual := realize signature observation noAnchor
  bridge := Iff.rfl
  variation := ⟨fun S hS => beta_cap S hS,bad,bad_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad,?_,rfl,bad_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(),∅,{0},?_⟩
    change (∅ : Finset (Fin 48)).card ≠ ({0} : Finset (Fin 48)).card
    simp

noncomputable def betaCapRegistration :
    Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.Combinatorics.Graph.StarForming.TripleModule.beta_cap)
      (Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.StarForming.TripleModule.beta_cap.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.StarForming.TripleModule.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature observation noAnchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.StarForming.TripleModule
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Graph.StarForming.TripleModule
