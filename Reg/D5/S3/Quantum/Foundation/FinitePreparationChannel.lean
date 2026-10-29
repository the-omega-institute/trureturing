import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Quantum.Foundation.FinitePreparationChannel
noncomputable section
namespace Reg.D5.S3.Quantum.Foundation.FinitePreparationChannel
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Foundation.FinitePreparationChannel
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel
open scoped MatrixOrder ComplexOrder
abbrev signature.{u} : Signature where
  Params := Type u
  State n := Matrix n n ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ n := Matrix n n ℂ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def readout.{u} : Realization signature.{u} := realize signature (fun _ _ X => Eq X) (fun e => nomatch e)
def bad.{u} : Realization signature.{u} := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
private theorem dependence.{u} : ObservationalDependence signature.{u} readout := by
  intro i
  refine ⟨ULift.{u} Unit, 0, 1, ?_⟩
  intro h
  have he := congrFun h 0
  change ((0 : Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ) = 0) = (1 = 0) at he
  exact one_ne_zero (Eq.mp he rfl)

abbrev arena.{u, v} : Arena where
  signature := signature.{v}
  Law R := ∀ {a : Type u} {b : Type v} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (rho : a → DensityState b),
    ∃ channel : QuantumChannel a b, ∀ X : Matrix a a ℂ,
      R.readout () b (CStarMatrix.ofMatrix.symm
        (channel.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)))
        (∑ i, X i i • CStarMatrix.ofMatrix.symm (rho i).1)
private theorem bad_law.{u, v} : ¬ arena.{u, v}.Law bad := by
  intro h
  let rho : DensityState (ULift.{v} Unit) := ⟨1, zero_le_one, by simp [Matrix.trace]⟩
  obtain ⟨channel, hc⟩ := @h (ULift.{u} Unit) (ULift.{v} Unit)
    inferInstance inferInstance inferInstance inferInstance (fun _ => rho)
  exact hc 0
def family.{u, v} : Registration arena.{u, v} (type_of% (@finite_preparation_quantum_channel.{u, v})) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨@finite_preparation_quantum_channel.{u, v}, bad, bad_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨bad, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, bad_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration.{u, v} : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@finite_preparation_quantum_channel.{u, v}) (Realization signature.{v}) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Foundation.FinitePreparationChannel.unit
  realizationName := `Reg.D5.S3.Quantum.Foundation.FinitePreparationChannel.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{v} (fun _ _ X => Eq X) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Foundation.FinitePreparationChannel
    definition := none
    coordinates := #[1]
    readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "arg", "body", "body", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms family
end Reg.D5.S3.Quantum.Foundation.FinitePreparationChannel
