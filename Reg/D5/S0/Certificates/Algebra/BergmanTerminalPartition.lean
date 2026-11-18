import LeanInformationAuditInterface.Contract.Registration
import D5.S0.Certificates.Algebra.BergmanTerminalPartition
import Reg.Support.DependentFamily
import Mathlib.Algebra.Field.ULift

/-! # The generated presentation and its normal forms -/

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S0.Certificates.Algebra.BergmanTerminalPartition
open private reduce from D5.S0.Certificates.Algebra.BergmanTerminalPartition

namespace Reg.D5.S0.Certificates.Algebra.BergmanTerminalPartition

noncomputable section
namespace Presentation

abbrev Parameters := Σ _n : ℕ, Σ _I : Finset ℕ, Word

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
  Law r := ∀ (n : ℕ) (hn : 0 < n) (I : Finset ℕ) (h0 : 0 ∈ I) (hN : n ∉ I) (s t : Word),
    presentation n I s t ↔ reduce n I s = r.readout () ⟨n, I, s⟩ t

private abbrev witness : Word := .monomial ⟨{0}, by simp⟩

private theorem witness_nonzero : reduce 2 {0} witness ≠ 0 := by
  simp [reduce, witness, normal]

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have H := (h 2 (by decide) {0} (by simp) (by simp) witness witness).mp (ConGen.Rel.refl _)
  exact witness_nonzero H

abbrev completenessAudit : Registration arena
    (type_of% @_root_.D5.S0.Certificates.Algebra.BergmanTerminalPartition.normal_form_complete) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S0.Certificates.Algebra.BergmanTerminalPartition.normal_form_complete,
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
    refine ⟨⟨2, {0}, witness⟩, witness, 0, ?_⟩
    exact witness_nonzero

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S0.Certificates.Algebra.BergmanTerminalPartition.normal_form_complete)
    (type_of% actual) Unit Unit := {
  unitName := `D5.S0.Certificates.Algebra.BergmanTerminalPartition.normal_form_complete.__information_unit
  realizationName := `Reg.D5.S0.Certificates.Algebra.BergmanTerminalPartition.Presentation.completenessAudit
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
    owner := `D5.S0.Certificates.Algebra.BergmanTerminalPartition
    definition := none
    coordinates := #[0, 2, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Presentation

namespace Family
open _root_.D5.S0.Certificates.Algebra
open BergmanQuestion15Refutation (Contracted delta positivePower product)
open BergmanQuestion23Refutation (mixedPower)
open BergmanCyclicGrading (positiveProduct)
open private cardinalities from D5.S0.Certificates.Algebra.BergmanTerminalPartition
universe u
abbrev signature : Signature where
  Params := Finset ℕ
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance
abbrev actual : Realization signature :=
  realize signature (fun _ I n => Fintype.card (Model n I)) (fun e => nomatch e)
abbrev rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (F : Type u) [_field : Field F] (I : Finset ℕ) (n : ℕ) (_hn : 2 ≤ n)
    (_h0 : 0 ∈ I) (_hN : n ∉ I) (_hsum : signedSum n I = 0),
    r.readout () I n = n * (n + 1) / 2 + 2 ∧
    Module.finrank F (Contracted F (Model n I)) = n * (n + 1) / 2 + 1 ∧
    Subsemigroup.closure (Set.range (generator n I)) = ⊤ ∧
    positivePower (generator n I 0) (n - 1) ≠ 0 ∧
    positivePower (generator n I 1) (n - 1) ≠ 0 ∧
    positivePower (generator n I 0) (n - 1) ≠ positivePower (generator n I 1) (n - 1) ∧
    difference F n I ≠ 0 ∧
    difference F n I ∈ Submodule.span F
      (Set.range (fun i => delta F (Model n I) (generator n I i))) ∧
    positivePower (difference F n I) (n - 1) = 0 ∧
    (∀ a : Fin (n + 1) → Model n I, positiveProduct n a = 0) ∧
    mixedPower (product F (Model n I)) ⊤ n = ⊥ ∧
    (∀ a : Fin (n + 1) → Contracted F (Model n I), positiveProduct n a = 0) ∧
    positivePower (delta F (Model n I) (generator n I 0)) (n - 1) ≠ 0
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := (h (ULift.{u} ℚ) (Finset.range 14 ∪ {20, 21}) 35 (by decide)
    (by decide) (by decide) (by decide)).1
  norm_num [rejected, realize] at hh
abbrev audit : Registration arena.{u}
    (type_of% @_root_.D5.S0.Certificates.Algebra.BergmanTerminalPartition.partition_family) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S0.Certificates.Algebra.BergmanTerminalPartition.partition_family,
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
    refine ⟨{0}, 2, 3, ?_⟩
    change Fintype.card (Model 2 {0}) ≠ Fintype.card (Model 3 {0})
    rw [(cardinalities ℚ 2 (by decide) {0}).1, (cardinalities ℚ 3 (by decide) {0}).1]
    norm_num
noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S0.Certificates.Algebra.BergmanTerminalPartition.partition_family)
    (type_of% actual) Unit Unit := {
  unitName := `D5.S0.Certificates.Algebra.BergmanTerminalPartition.partition_family.__information_unit
  realizationName := `Reg.D5.S0.Certificates.Algebra.BergmanTerminalPartition.Family.audit
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨audit⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S0.Certificates.Algebra.BergmanTerminalPartition
    definition := none
    coordinates := #[2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Family
end
end Reg.D5.S0.Certificates.Algebra.BergmanTerminalPartition
