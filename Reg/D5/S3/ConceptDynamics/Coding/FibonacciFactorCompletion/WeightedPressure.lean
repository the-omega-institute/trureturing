import Reg.Support.FibonacciFactorCompletion.WeightedPressureReadouts
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure
import Reg.Support.SingleDependentReadout

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure
noncomputable section

def partition_positive_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.partition_positive)
      (type_of% (realize.{0,0,0,0,0} partitionSignature
        (fun _ p X => partitionSum X p.1 p.2) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.partition_positive_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.positiveRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨positiveArena⟩
  objectArena := .source ⟨positiveArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source positiveArena ⟨positiveRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} partitionSignature
    (fun _ p X => partitionSum X p.1 p.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure
    definition := none
    coordinates := #[2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms positiveRegistration
#print axioms partition_positive_registration

def partition_submultiplicative_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.partition_submultiplicative)
      (type_of% (realize.{0,0,0,0,0} partitionSignature
        (fun _ p X => partitionSum X p.1 p.2) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.partition_submultiplicative_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.submultiplicativeRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨submultiplicativeArena⟩
  objectArena := .source ⟨submultiplicativeArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source submultiplicativeArena ⟨submultiplicativeRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} partitionSignature
    (fun _ p X => partitionSum X p.1 p.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure
    definition := none
    coordinates := #[1, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms submultiplicativeRegistration
#print axioms partition_submultiplicative_registration

def partition_lower_bound_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.partition_lower_bound)
      (type_of% (realize.{0,0,0,0,0} partitionSignature
        (fun _ p X => partitionSum X p.1 p.2) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.partition_lower_bound_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.lowerRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨lowerArena⟩
  objectArena := .source ⟨lowerArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source lowerArena ⟨lowerRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} partitionSignature
    (fun _ p X => partitionSum X p.1 p.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure
    definition := none
    coordinates := #[2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms lowerRegistration
#print axioms partition_lower_bound_registration

def partition_shift_bounds_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.partition_shift_bounds)
      (type_of% (realize.{0,0,0,0,0} partitionSignature
        (fun _ p X => partitionSum X p.1 p.2) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.partition_shift_bounds_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.shiftRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨shiftArena⟩
  objectArena := .source ⟨shiftArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source shiftArena ⟨shiftRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} partitionSignature
    (fun _ p X => partitionSum X p.1 p.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure
    definition := none
    coordinates := #[1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms shiftRegistration
#print axioms partition_shift_bounds_registration

end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.Injection
noncomputable section

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral

abbrev splitSignature : Signature.{0,0,0,0,0} where
  Params := Σ _ : Set (ℤ → CuLetter), Σ _ : ℕ, ℕ
  State p := LengthDictionary p.1 (p.2.1 + p.2.2)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := LengthDictionary p.1 p.2.1 × LengthDictionary p.1 p.2.2
  Anchor := Empty
  finiteAnchor := inferInstance

def splitActual : Realization splitSignature :=
  realize splitSignature (fun _ p => splitWord p.1 p.2.1 p.2.2)
    (fun e => nomatch e)

-- Choice only constructs a hypothetical rejected family. It neither substitutes
-- the actual source readout nor evaluates a proposition to encode the Law.
-- A source input supplies an output inhabitant; empty state fibers need no choice.
-- Proof irrelevance makes the chosen output constant within each inhabited fiber.
def splitRejected : Realization splitSignature :=
  realize splitSignature
    (fun _ p x => Classical.choice (show Nonempty (LengthDictionary p.1 p.2.1 ×
        LengthDictionary p.1 p.2.2) from ⟨splitWord p.1 p.2.1 p.2.2 x⟩))
    (fun e => nomatch e)

abbrev splitArena : Arena.{0,0,0,0,0} where
  signature := splitSignature
  Law r := ∀ (X : Set (ℤ → CuLetter)) (k j : ℕ),
    Function.Injective (r.readout () ⟨X, ⟨k, j⟩⟩)

private def oneLetter (a : CuLetter) : LengthDictionary Set.univ 1 :=
  ⟨[a], ⟨⟨(fun _ => a), Set.mem_univ _, 0, by intro k; simp⟩, rfl⟩⟩

private theorem split_bad : ¬ splitArena.Law splitRejected := by
  intro h
  have eq : oneLetter .c = oneLetter .u := h Set.univ 1 0 rfl
  have impossible := congrArg Subtype.val eq
  simpa [oneLetter] using impossible

def splitRegistration : Registration splitArena (type_of% @split_word_injective) where
  actual := splitActual
  bridge := Iff.rfl
  variation := ⟨@split_word_injective, splitRejected, split_bad⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨splitRejected, ?_, rfl, split_bad⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨Set.univ, ⟨1, 0⟩⟩, oneLetter .c, oneLetter .u, ?_⟩
    intro h
    have impossible := congrArg (fun y => y.1.val) h
    simpa [splitActual, realize, splitWord, oneLetter] using impossible

def split_word_injective_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.split_word_injective)
      (type_of% (realize.{0,0,0,0,0} splitSignature
        (fun _ p => splitWord p.1 p.2.1 p.2.2) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.Injection.split_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.Injection.splitRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨splitArena⟩
  objectArena := .source ⟨splitArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source splitArena ⟨splitRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} splitSignature
        (fun _ p => splitWord p.1 p.2.1 p.2.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


#print axioms splitRegistration
#print axioms split_word_injective_registration

end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.Injection

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.ExactOriginal173
noncomputable section


def length_dictionary_nonempty_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.length_dictionary_nonempty)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ _ X => X) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.ExactOriginal173.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.ExactOriginal173.evidence
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
    (fun _ _ X => X) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms length_dictionary_nonempty_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.ExactOriginal173

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.ExactOriginal182
noncomputable section

def pressure_shift_bounds_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.pressure_shift_bounds)
      (type_of% (realize.{0,0,0,0,0} observationSignature (fun _ X s => pressure X s) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.ExactOriginal182.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.ExactOriginal182.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature (fun _ X s => pressure X s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms pressure_shift_bounds_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.ExactOriginal182

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.ExactOriginal185
noncomputable section

def pressure_zero_nonneg_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.pressure_zero_nonneg)
      (type_of% (realize.{0,0,0,0,0} observationSignature (fun _ X s => pressure X s) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.ExactOriginal185.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.ExactOriginal185.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature (fun _ X s => pressure X s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms pressure_zero_nonneg_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.ExactOriginal185

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.ExactOriginal191
noncomputable section

def pressure_zero_iff_rate_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.pressure_zero_iff_rate)
      (type_of% (realize.{0,0,0,0,0} observationSignature (fun _ X s => pressure X s) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.ExactOriginal191.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.ExactOriginal191.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature (fun _ X s => pressure X s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms pressure_zero_iff_rate_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.ExactOriginal191

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped ENNReal NNReal


namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.ExactOriginal186
noncomputable section

def pressure_unique_zero_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.pressure_unique_zero)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ X η => pressure X η) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.ExactOriginal186.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.ExactOriginal186.evidence
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
        (fun _ X η => pressure X η) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg", "body", "arg", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms pressure_unique_zero_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.ExactOriginal186

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.ExactOriginal187
noncomputable section

def whole_series_regrouping_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.whole_series_regrouping)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ p w => wordTerm p.2 w.val) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.ExactOriginal187.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.ExactOriginal187.evidence
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
        (fun _ p w => wordTerm p.2 w.val) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "fn", "arg", "fn", "arg", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms whole_series_regrouping_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.ExactOriginal187

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.ExactOriginal188
noncomputable section

def whole_series_finiteness_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.whole_series_finiteness)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ p k => partitionSum p.1 k p.2) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.ExactOriginal188.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.ExactOriginal188.evidence
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
        (fun _ p k => partitionSum p.1 k p.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "fn", "arg", "fn", "arg", "body"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms whole_series_finiteness_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.ExactOriginal188

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.ExactOriginal189
noncomputable section

def whole_series_nonpositive_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.whole_series_nonpositive)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ p w => wordTerm p.2 w.val) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.ExactOriginal189.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.ExactOriginal189.evidence
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
        (fun _ p w => wordTerm p.2 w.val) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn", "arg", "body", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms whole_series_nonpositive_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.ExactOriginal189

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.ExactOriginal190
noncomputable section

def negative_pressure_summable_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.negative_pressure_summable)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ p k => partitionSum p.1 k p.2) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.ExactOriginal190.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.ExactOriginal190.evidence
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
        (fun _ p k => partitionSum p.1 k p.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "body"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms negative_pressure_summable_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.ExactOriginal190

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.ExactOriginal179
noncomputable section

def log_quotient_lower_bound_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.log_quotient_lower_bound)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ k x => x / (k : ℝ)) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.ExactOriginal179.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.ExactOriginal179.evidence
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
    (fun _ k x => x / (k : ℝ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure
    definition := none
    coordinates := #[3]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms log_quotient_lower_bound_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.ExactOriginal179


namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.ExactOriginal183
noncomputable section

def pressure_lipschitz_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.pressure_lipschitz)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ X θ => pressure X θ) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.ExactOriginal183.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.ExactOriginal183.evidence
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
    (fun _ X θ => pressure X θ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms pressure_lipschitz_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.ExactOriginal183

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.ExactOriginal184
noncomputable section

def pressure_strictAnti_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.pressure_strictAnti)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ X θ => pressure X θ) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.ExactOriginal184.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.ExactOriginal184.evidence
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
    (fun _ X θ => pressure X θ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms pressure_strictAnti_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.ExactOriginal184


namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.ExactOriginal177
noncomputable section

def log_partition_subadditive_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.log_partition_subadditive)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ p k => logPartition p.1 p.2 k) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.ExactOriginal177.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.ExactOriginal177.evidence
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
    (fun _ p k => logPartition p.1 p.2 k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms log_partition_subadditive_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.ExactOriginal177

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.ExactOriginal180
noncomputable section
open Filter Topology

def pressure_tendsto_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.pressure_tendsto)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ p k => logPartition p.1 p.2 k / (k : ℝ)) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.ExactOriginal180.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.ExactOriginal180.evidence
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
    (fun _ p k => logPartition p.1 p.2 k / (k : ℝ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms pressure_tendsto_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.ExactOriginal180
