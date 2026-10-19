import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Subentropy.GuessingProbability
import Reg.Support.SingleDependentReadout

noncomputable section
set_option autoImplicit false
open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel
open _root_.D5.S3.Quantum.Information.OrthogonalRecordEntropy
open _root_.D5.S3.Quantum.Subentropy.GuessingProbability
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Quantum.Subentropy.GuessingProbability
universe u v
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {X : Type u} {B : Type v} [Fintype X] [Fintype B] [DecidableEq B]
    (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hs : ∑ x, p x = 1) (ρ : X → DensityState B),
    (successProbabilitySet p ρ).Nonempty ∧ BddAbove (successProbabilitySet p ρ) ∧
      0 < pGuess p ρ ∧ pGuess p ρ ≤ 1 ∧
      R.readout () () (1 - pGuess p ρ) (-Real.log (pGuess p ρ)) ∧
      ∀ q : ℝ, (∀ M : X → Matrix B B ℂ,
        (∀ x, (M x).PosSemidef) → ∑ x, M x = 1 →
          q ≤ 1 - successProbability p ρ M) → q ≤ 1 - pGuess p ρ
private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  let ρ : ULift.{u} Unit → DensityState (ULift.{v} Unit) := fun _ => pointerState ⟨()⟩
  have hb := @h (ULift.{u} Unit) (ULift.{v} Unit) inferInstance inferInstance
    inferInstance (fun _ => 1) (fun _ => by norm_num) (by simp) ρ
  exact hb.2.2.2.2.1
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have ht := congrFun he 0
  norm_num [actual, realize] at ht
def family : Registration arena.{u,v} (type_of% @pGuess_bounds.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@pGuess_bounds, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@pGuess_bounds.{u,v}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Subentropy.GuessingProbability.pGuess_bounds.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Subentropy.GuessingProbability.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Subentropy.GuessingProbability
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "arg", "arg", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Quantum.Subentropy.GuessingProbability
