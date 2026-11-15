import LeanInformationAuditInterface.Contract.Registration
import D5.S0.Certificates.Algebra.BergmanCyclicSemigroup
import Reg.Support.DependentFamily

/-! # The generated presentation and its normal forms -/

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S0.Certificates.Algebra.BergmanCyclicSemigroup

namespace Reg.D5.S0.Certificates.Algebra.BergmanCyclicSemigroup

noncomputable section

abbrev Parameters := Σ _n : ℕ, Σ _q : Bool, Word

abbrev signature : Signature where
  Params := Parameters
  State := fun _ => Word
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ p => Model p.1 p.2.1
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev actual : Realization signature :=
  realize signature (fun _ p t => reduce p.1 p.2.1 t) (fun e => nomatch e)

abbrev rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ (n : ℕ) (hn : 0 < n) (q : Bool) (s t : Word),
    presentation n hn q s t ↔ reduce n q s = r.readout () ⟨n, q, s⟩ t

private abbrev witness : Word := .monomial ⟨{0}, by simp⟩

private theorem witness_nonzero : reduce 2 false witness ≠ 0 := by
  simp [reduce, witness, normal, survives]

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have H := (h 2 (by decide) false witness witness).mp (ConGen.Rel.refl _)
  exact witness_nonzero H

abbrev completenessAudit : Registration arena
    (type_of% @_root_.D5.S0.Certificates.Algebra.BergmanCyclicSemigroup.normal_form_complete) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S0.Certificates.Algebra.BergmanCyclicSemigroup.normal_form_complete,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨2, false, witness⟩, witness, 0, ?_⟩
    exact witness_nonzero

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S0.Certificates.Algebra.BergmanCyclicSemigroup.normal_form_complete)
    (type_of% actual) Unit Unit := {
  unitName := `D5.S0.Certificates.Algebra.BergmanCyclicSemigroup.normal_form_complete.__information_unit
  realizationName := `Reg.D5.S0.Certificates.Algebra.BergmanCyclicSemigroup.completenessAudit
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨completenessAudit⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S0.Certificates.Algebra.BergmanCyclicSemigroup
    definition := none
    coordinates := #[0, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end

end Reg.D5.S0.Certificates.Algebra.BergmanCyclicSemigroup
