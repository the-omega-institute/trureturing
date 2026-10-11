import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Information.SeparableStateLocalUnitaryStabilizerObstruction
import Reg.Support.DependentFamily

open LeanInformationAudit Matrix
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence
open _root_.D5.S3.Quantum.FiniteDimensional (qubitX qubitZ)
open _root_.D5.S3.Quantum.Information.SeparableStateLocalUnitaryStabilizerObstruction
  (pauli_square pauli_hermitian pauli_trace_pair)

set_option linter.style.longLine false

noncomputable section
namespace Reg.D5.S3.Quantum.Information.SeparableStateLocalUnitaryStabilizerObstruction

namespace Square

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
  Law R := ∀ p : Pauli, R.readout () () p * pauliMatrix p = 1

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have bad := h Pauli.I
  change (0 : Matrix (Fin 2) (Fin 2) ℂ) * pauliMatrix Pauli.I = 1 at bad
  rw [zero_mul] at bad
  have entry := congrFun (congrFun bad 0) 0
  change (0 : ℂ) = 1 at entry
  exact zero_ne_one entry

def family : Registration arena (type_of% @pauli_square) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨pauli_square, rejected, rejected_law⟩
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
      (@_root_.D5.S3.Quantum.Information.SeparableStateLocalUnitaryStabilizerObstruction.pauli_square)
      (type_of% (realize signature (fun _ _ p => pauliMatrix p) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Quantum.Information.SeparableStateLocalUnitaryStabilizerObstruction.pauli_square.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Information.SeparableStateLocalUnitaryStabilizerObstruction.Square.family
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
    owner := `D5.S3.Quantum.Information.SeparableStateLocalUnitaryStabilizerObstruction
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms family
#print axioms registration

end Square

namespace Hermitian

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
  Law R := ∀ p : Pauli, (R.readout () () p)ᴴ = pauliMatrix p

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have bad := h Pauli.I
  change (0 : Matrix (Fin 2) (Fin 2) ℂ)ᴴ = pauliMatrix Pauli.I at bad
  rw [Matrix.conjTranspose_zero] at bad
  have entry := congrFun (congrFun bad 0) 0
  change (0 : ℂ) = 1 at entry
  exact zero_ne_one entry

def family : Registration arena (type_of% @pauli_hermitian) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨pauli_hermitian, rejected, rejected_law⟩
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
      (@_root_.D5.S3.Quantum.Information.SeparableStateLocalUnitaryStabilizerObstruction.pauli_hermitian)
      (type_of% (realize signature (fun _ _ p => pauliMatrix p) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Quantum.Information.SeparableStateLocalUnitaryStabilizerObstruction.pauli_hermitian.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Information.SeparableStateLocalUnitaryStabilizerObstruction.Hermitian.family
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
    owner := `D5.S3.Quantum.Information.SeparableStateLocalUnitaryStabilizerObstruction
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms family
#print axioms registration

end Hermitian

namespace TracePair

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
  Law R := ∀ p q : Pauli, trace (R.readout () () p * pauliMatrix q) = if p = q then 2 else 0

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have bad := h Pauli.I Pauli.I
  norm_num [rejected, realize, pauliMatrix] at bad

def family : Registration arena (type_of% @pauli_trace_pair) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨pauli_trace_pair, rejected, rejected_law⟩
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
      (@_root_.D5.S3.Quantum.Information.SeparableStateLocalUnitaryStabilizerObstruction.pauli_trace_pair)
      (type_of% (realize signature (fun _ _ p => pauliMatrix p) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Quantum.Information.SeparableStateLocalUnitaryStabilizerObstruction.pauli_trace_pair.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Information.SeparableStateLocalUnitaryStabilizerObstruction.TracePair.family
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
    owner := `D5.S3.Quantum.Information.SeparableStateLocalUnitaryStabilizerObstruction
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms family
#print axioms registration

end TracePair

end Reg.D5.S3.Quantum.Information.SeparableStateLocalUnitaryStabilizerObstruction
