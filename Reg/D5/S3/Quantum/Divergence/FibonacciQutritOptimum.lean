import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Divergence.FibonacciQutritOptimum
import D5.S3.Quantum.Divergence.FibonacciQutritSingularSupport
import D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy
import D5.S3.Quantum.Foundation.FiniteStateChannel
import D5.S3.Quantum.Recovery.DiagonalRecordCapacity

/-! Source-bound registrations for the attained value and the equality constraint. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open LeanInformationAudit
open scoped CStarAlgebra ComplexOrder MatrixOrder
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Divergence.FibonacciQutritOptimum
open _root_.D5.S3.Quantum.Divergence.FibonacciQutritSingularSupport.Preparation (matrix)
open _root_.D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy (extendedQuantumRelativeEntropy)
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel (QuantumChannel)
open _root_.D5.S3.Quantum.Recovery.DiagonalRecordCapacity.Basis (basisState)

namespace Reg.D5.S3.Quantum.Divergence.FibonacciQutritOptimum

private abbrev score (Φ : QuantumChannel (Fin 4) (Fin 3)) :=
  extendedQuantumRelativeEntropy (Φ.mapState diagonalInput) (Φ.mapState diagonalReference)

namespace Maximum

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => Set (WithTop ℝ)) (fun _ => WithTop ℝ → Prop)

private def actual : Realization signature :=
  realize signature (fun _ _ s x => IsGreatest s x) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), {0}, ∅, ?_⟩
  intro h
  have he : IsGreatest ({0} : Set (WithTop ℝ)) 0 = IsGreatest (∅ : Set (WithTop ℝ)) 0 :=
    congrFun h 0
  exact (Eq.mp he (by simp [IsGreatest, upperBounds])).1

abbrev arena : Arena where
  signature := signature
  Law A := A.readout () () (Set.range score) (C3 : WithTop ℝ)

private theorem rejected_law : ¬ arena.Law rejected := id

def sourceRegistration : Registration arena (type_of% @isGreatest_channel) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@isGreatest_channel, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

set_option linter.style.longLine false in
def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@isGreatest_channel) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Divergence.FibonacciQutritOptimum.isGreatest_channel.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.FibonacciQutritOptimum.Maximum.sourceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨True.intro⟩ True.intro
  readout := some (realize signature (fun _ _ s x => IsGreatest s x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.FibonacciQutritOptimum
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


end Maximum

namespace Equality

private abbrev Qutrit := Matrix (Fin 3) (Fin 3) ℂ

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => Qutrit) (fun _ => Qutrit → Prop)

private def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have he : ((0 : Qutrit) = 0) = ((1 : Qutrit) = 0) := congrFun h 0
  exact one_ne_zero (he.mp rfl)

abbrev arena : Arena where
  signature := signature
  Law A := ∀ (Φ : QuantumChannel (Fin 4) (Fin 3)) (_ : score Φ = (C3 : WithTop ℝ)),
    let W (i : Fin 4) := Φ.mapState (basisState i)
    ¬ (positiveReference (positiveClasses W)).PosDef ∧
      A.readout () () (matrix (W 0)) (matrix (W 1)) ∧
      matrix (W 0) * matrix (W 2) = 0 ∧
      matrix (W 0) * matrix (W 3) = 0 ∧
      matrix (W 2) * matrix (W 3) = 0

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨Φ, hΦ⟩ := isGreatest_channel.1
  exact (h Φ hΦ).2.1

def sourceRegistration : Registration arena (type_of% @channel_equality_conditions) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@channel_equality_conditions, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

set_option linter.style.longLine false in
def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@channel_equality_conditions) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Divergence.FibonacciQutritOptimum.channel_equality_conditions.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.FibonacciQutritOptimum.Equality.sourceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨True.intro⟩ True.intro
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.FibonacciQutritOptimum
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Equality

#print axioms Maximum.audit
#print axioms Equality.audit

end Reg.D5.S3.Quantum.Divergence.FibonacciQutritOptimum
