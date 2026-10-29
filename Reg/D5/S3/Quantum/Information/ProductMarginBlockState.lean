import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Quantum.Information.ProductMarginBlockState
noncomputable section
namespace Reg.D5.S3.Quantum.Information.ProductMarginBlockState
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Information.ProductMarginBlockState
open _root_.D5.S3.Quantum.Information.PartialTraceMutualInformation
open scoped Kronecker MatrixOrder ComplexOrder
abbrev signature.{u} : Signature where
  Params := Type u
  State n := Matrix (Fin 2 × n) (Fin 2 × n) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ n := Matrix (Fin 2 × n) (Fin 2 × n) ℂ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def readout.{u} : Realization signature.{u} := realize signature (fun _ _ X => Eq X) (fun e => nomatch e)
def bad.{u} : Realization signature.{u} := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
private theorem dependence.{u} : ObservationalDependence signature.{u} readout := by
  intro i
  refine ⟨ULift.{u} Unit, 0, 1, ?_⟩
  intro h
  have he := congrFun h 0
  change ((0 : Matrix (Fin 2 × ULift.{u} Unit) (Fin 2 × ULift.{u} Unit) ℂ) = 0) = (1 = 0) at he
  exact one_ne_zero (Eq.mp he rfl)

private def pointer (a : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal fun b => if b = a then 1 else 0
abbrev arena.{u} : Arena where
  signature := signature.{u}
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n] (P Q K : Matrix n n ℂ),
    R.readout () n (partialTraceLeft (blockMatrix P Q K))
      ((1 / 2 : ℝ) • (pointer 0 ⊗ₖ P + pointer 1 ⊗ₖ Q)) ∧
    (fun a c => ∑ b : Fin 2, blockMatrix P Q K (a.1, (b, a.2)) (c.1, (b, c.2))) =
      (1 / 2 : ℝ) • (pointer 0 ⊗ₖ P + pointer 1 ⊗ₖ Q) ∧
    partialTraceLeft (partialTraceLeft (blockMatrix P Q K)) = (1 / 2 : ℝ) • (P + Q)
private theorem bad_law.{u} : ¬ arena.{u}.Law bad := by
  intro h
  exact (@h (ULift.{u} Unit) inferInstance inferInstance 0 0 0).1
def family.{u} : Registration arena.{u} (type_of% (@block_partial_traces.{u})) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨@block_partial_traces.{u}, bad, bad_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨bad, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, bad_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration.{u} : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@block_partial_traces.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Information.ProductMarginBlockState.unit
  realizationName := `Reg.D5.S3.Quantum.Information.ProductMarginBlockState.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ _ X => Eq X) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.ProductMarginBlockState
    definition := none
    coordinates := #[0]
    readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms family
end Reg.D5.S3.Quantum.Information.ProductMarginBlockState
