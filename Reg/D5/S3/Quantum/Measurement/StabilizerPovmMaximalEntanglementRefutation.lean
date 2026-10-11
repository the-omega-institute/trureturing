import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation
import Reg.Support.DependentFamily

open LeanInformationAudit Matrix
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence
open _root_.D5.S3.Quantum.FiniteDimensional (qubitX qubitZ)
open _root_.D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation
  (letterProduct letterPhase letter_mul)

set_option linter.style.longLine false

noncomputable section
namespace Reg.D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation

namespace LetterMul

abbrev signature : Signature where
  Params := Pauli
  State _ := Pauli
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Matrix (Fin 2) (Fin 2) ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ p => pauliMatrix p) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ p q : Pauli, R.readout () q p * pauliMatrix q =
    letterPhase p q • pauliMatrix (letterProduct p q)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have bad := h Pauli.I Pauli.I
  have bad' : (0 : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
    simp [rejected, realize, letterPhase, letterProduct, pauliMatrix] at bad
  have entry := congrFun (congrFun bad' 0) 0
  change (0 : ℂ) = 1 at entry
  exact zero_ne_one entry

def family : Registration arena (type_of% @letter_mul) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨letter_mul, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨Pauli.I, Pauli.I, Pauli.X, ?_⟩
    intro h
    have entry := congrFun (congrFun h 0) 0
    simp [actual, realize, pauliMatrix, qubitX] at entry

noncomputable def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation.letter_mul)
      (type_of% (realize signature (fun _ _ p => pauliMatrix p) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation.letter_mul.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation.LetterMul.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ p => pauliMatrix p) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms family
#print axioms registration

end LetterMul

end Reg.D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation
