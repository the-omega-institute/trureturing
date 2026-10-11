import Reg.Support.FibonacciFactorWitnesses
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping.ExactOriginal192
noncomputable section

open Reg.Support.FibonacciFactorWitnesses

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Unit
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature :=
  realize observationSignature (fun _ _ T => T) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => 1) (fun e => nomatch e)
abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (side : MemorySide) (n K : ℕ) (d : ℝ) (T : ℕ), Nonempty (CorePathWitnessDictionary side n K d (r.readout () () T) ≃ RetainedPathDictionary side n K d T)

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  letI : IsEmpty (CorePathWitnessDictionary .lower 1 1 0 1) := ⟨by
    intro x
    exact word_weight_ne_one _ x.property.2⟩
  obtain ⟨e⟩ := h .lower 1 1 0 0
  change CorePathWitnessDictionary .lower 1 1 0 1 ≃ RetainedPathDictionary .lower 1 1 0 0 at e
  exact isEmptyElim (e.symm empty_retained)

def evidence : Registration sourceArena (type_of% @core_path_witness_dictionary_equiv) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@core_path_witness_dictionary_equiv, rejected, rejected_law⟩
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
    refine ⟨(), 0, 1, ?_⟩
    norm_num [actual, realize]

def core_path_witness_dictionary_equiv_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping.core_path_witness_dictionary_equiv)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ _ T => T) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping.ExactOriginal192.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping.ExactOriginal192.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature
    (fun _ _ T => T) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "fn", "arg", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms core_path_witness_dictionary_equiv_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping.ExactOriginal192

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping.ExactOriginal193
noncomputable section

open Reg.Support.FibonacciFactorWitnesses

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Unit
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature :=
  realize observationSignature (fun _ _ T => T) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => 1) (fun e => nomatch e)
abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (side : MemorySide) (n K : ℕ) (d : ℝ) (T : ℕ), Nat.card (CorePathWitnessDictionary side n K d (r.readout () () T)) = Nat.card (RetainedPathDictionary side n K d T)

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  letI : IsEmpty (CorePathWitnessDictionary .lower 1 1 0 1) := ⟨by
    intro x
    exact word_weight_ne_one _ x.property.2⟩
  letI : Finite (RetainedPathDictionary .lower 1 1 0 0) :=
    (original_weighted_path_count .lower 1 1 0 (by decide) (by decide) 0).1
  letI : Nonempty (RetainedPathDictionary .lower 1 1 0 0) := ⟨empty_retained⟩
  have positive := Nat.card_pos (α := RetainedPathDictionary .lower 1 1 0 0)
  have eq := h .lower 1 1 0 0
  change Nat.card (CorePathWitnessDictionary .lower 1 1 0 1) = _ at eq
  have zero : Nat.card (CorePathWitnessDictionary .lower 1 1 0 1) = 0 := by simp
  omega

def evidence : Registration sourceArena (type_of% @core_path_witness_dictionary_card) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@core_path_witness_dictionary_card, rejected, rejected_law⟩
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
    refine ⟨(), 0, 1, ?_⟩
    norm_num [actual, realize]

def core_path_witness_dictionary_card_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping.core_path_witness_dictionary_card)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ _ T => T) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping.ExactOriginal193.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping.ExactOriginal193.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature
    (fun _ _ T => T) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "arg", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms core_path_witness_dictionary_card_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping.ExactOriginal193
