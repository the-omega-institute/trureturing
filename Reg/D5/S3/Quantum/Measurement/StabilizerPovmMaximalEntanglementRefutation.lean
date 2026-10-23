import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation
import Reg.Support.DependentFamily

open LeanInformationAudit Matrix
open scoped BigOperators
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence
open _root_.D5.S3.Quantum.FiniteDimensional (qubitX qubitZ)
open _root_.D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation
  (letterProduct letterPhase letter_mul letter_comm word_mul word_trace_pair word_comm_sign)

set_option linter.style.longLine false

noncomputable section
namespace Reg.D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation

namespace LetterMul

abbrev signature : Signature where
  Params := Unit
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
  Law R := ∀ p q : Pauli, R.readout () () p * pauliMatrix q =
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
    refine ⟨(), Pauli.I, Pauli.X, ?_⟩
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
    coordinates := #[]
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

namespace LetterComm

abbrev signature : Signature where
  Params := Unit
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
  Law R := ∀ p q : Pauli, R.readout () () p * pauliMatrix q =
    (sgn p q : ℂ) • (pauliMatrix q * pauliMatrix p)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have bad := h Pauli.I Pauli.I
  have bad' : (0 : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
    simp [rejected, realize, sgn, anticomm, pauliMatrix] at bad
  have entry := congrFun (congrFun bad' 0) 0
  change (0 : ℂ) = 1 at entry
  exact zero_ne_one entry

def family : Registration arena (type_of% @letter_comm) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨letter_comm, rejected, rejected_law⟩
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
    refine ⟨(), Pauli.I, Pauli.X, ?_⟩
    intro h
    have entry := congrFun (congrFun h 0) 0
    simp [actual, realize, pauliMatrix, qubitX] at entry

noncomputable def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation.letter_comm)
      (type_of% (realize signature (fun _ _ p => pauliMatrix p) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation.letter_comm.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation.LetterComm.family
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
    coordinates := #[]
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

end LetterComm

namespace WordMul

abbrev signature : Signature where
  Params := ℕ
  State n := Fin n → Pauli
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ n := Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ v => wordOp v) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (v w : Fin n → Pauli), R.readout () n v * wordOp w = (∏ i, letterPhase (v i) (w i)) • wordOp (fun i => letterProduct (v i) (w i))

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have bad := @h 0 (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
  dsimp only [rejected, realize] at bad
  rw [zero_mul] at bad
  have entry := congrFun (congrFun bad (fun i => Fin.elim0 i)) (fun i => Fin.elim0 i)
  change (0 : ℂ) = _ at entry
  simp [wordOp, tensorOp,
    letterPhase, letterProduct] at entry

def family : Registration arena (type_of% @word_mul) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@word_mul, rejected, rejected_law⟩
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
    refine ⟨1, (fun _ => Pauli.I), (fun _ => Pauli.X), ?_⟩
    intro h
    have entry := congrFun (congrFun h (fun _ => 0)) (fun _ => 0)
    simp [actual, realize, wordOp, tensorOp, pauliMatrix, qubitX] at entry

noncomputable def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation.word_mul)
      (type_of% (realize signature (fun _ _ v => wordOp v) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation.word_mul.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation.WordMul.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ v => wordOp v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms family
#print axioms registration

end WordMul

namespace WordTracePair

abbrev signature : Signature where
  Params := ℕ
  State n := Fin n → Pauli
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ n := Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ v => wordOp v) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (v w : Fin n → Pauli), Matrix.trace (R.readout () n v * wordOp w) = if v = w then (2 : ℂ)^n else 0

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have bad := @h 0 (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
  simp [rejected, realize, wordOp, tensorOp, Matrix.trace, Matrix.diag,
    Matrix.mul_apply] at bad

def family : Registration arena (type_of% @word_trace_pair) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@word_trace_pair, rejected, rejected_law⟩
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
    refine ⟨1, (fun _ => Pauli.I), (fun _ => Pauli.X), ?_⟩
    intro h
    have entry := congrFun (congrFun h (fun _ => 0)) (fun _ => 0)
    simp [actual, realize, wordOp, tensorOp, pauliMatrix, qubitX] at entry

noncomputable def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation.word_trace_pair)
      (type_of% (realize signature (fun _ _ v => wordOp v) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation.word_trace_pair.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation.WordTracePair.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ v => wordOp v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms family
#print axioms registration

end WordTracePair

namespace WordCommSign

abbrev signature : Signature where
  Params := ℕ
  State n := Fin n → Pauli
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ n := Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ v => wordOp v) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (v w : Fin n → Pauli), R.readout () n v * wordOp w = (∏ i, (sgn (v i) (w i) : ℂ)) • (wordOp w * wordOp v)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have bad := @h 0 (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
  dsimp only [rejected, realize] at bad
  rw [zero_mul] at bad
  have entry := congrFun (congrFun bad (fun i => Fin.elim0 i)) (fun i => Fin.elim0 i)
  change (0 : ℂ) = _ at entry
  simp [wordOp, tensorOp,
    Matrix.mul_apply] at entry

def family : Registration arena (type_of% @word_comm_sign) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@word_comm_sign, rejected, rejected_law⟩
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
    refine ⟨1, (fun _ => Pauli.I), (fun _ => Pauli.X), ?_⟩
    intro h
    have entry := congrFun (congrFun h (fun _ => 0)) (fun _ => 0)
    simp [actual, realize, wordOp, tensorOp, pauliMatrix, qubitX] at entry

noncomputable def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation.word_comm_sign)
      (type_of% (realize signature (fun _ _ v => wordOp v) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation.word_comm_sign.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation.WordCommSign.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ v => wordOp v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms family
#print axioms registration

end WordCommSign

end Reg.D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation
