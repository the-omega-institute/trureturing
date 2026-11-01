import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Semigroups.ThresholdSchurSemigroup
import Reg.Support.DependentFamily
import Mathlib.Tactic

open _root_.D5.S3.Quantum.Semigroups.ThresholdSchurSemigroup
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators Matrix CStarAlgebra ComplexOrder MatrixOrder Matrix.Norms.Elementwise

noncomputable section
universe u
namespace Reg.D5.S3.Quantum.Semigroups.ThresholdSchurSemigroup

abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x => -(x / 2)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law observation := ∀ {S : Type u} [Fintype S] [DecidableEq S] (a : S → ℝ),
    ∃ channels : {u : ℝ // 0 ≤ u} → QuantumChannel S S,
      (∀ u X, CStarMatrix.ofMatrix.symm
        ((channels u).toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) =
        evolution a u.val X) ∧
      (∀ (u v : {u : ℝ // 0 ≤ u}), channels ⟨u.val+v.val, add_nonneg u.property v.property⟩ =
        (channels u).comp (channels v)) ∧
      ((channels ⟨0, le_rfl⟩).toCompletelyPositiveMap.toLinearMap = LinearMap.id) ∧
      (∀ X, evolution a 0 X = X) ∧
      (∀ X, Continuous (fun u : ℝ => evolution a u X)) ∧
      (∀ i, 0 ≤ gap a i ∧ (projection a i)ᴴ = projection a i ∧
        projection a i * projection a i = projection a i) ∧
      (∀ X, generator a X = fun s t => observation.readout () () ((|a s-a t| : ℝ) : ℂ) * X s t) ∧
      (∀ s t, generator a (Matrix.single s t 1) =
        (-(|a s-a t|/2) : ℂ) • Matrix.single s t 1) ∧
      (∀ u X, (fun st : S × S => evolution a u X st.1 st.2) =
        (NormedSpace.exp (u • generatorMatrix a)).mulVec (fun st => X st.1 st.2)) ∧
      (∀ u X, HasDerivAt (fun v : ℝ => evolution a v X)
        (generator a (evolution a u X)) u)

theorem actual_law : arena.{u}.Law actual := by
  intro S instF instD a
  simpa only [arena, actual, realize] using
    _root_.D5.S3.Quantum.Semigroups.ThresholdSchurSemigroup.result a

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  obtain ⟨channels, hh⟩ := h (S := ULift.{u} (Fin 2)) (fun i => (i.down.val : ℝ) * 2)
  have hz := congrArg (fun M : Matrix (ULift.{u} (Fin 2)) (ULift.{u} (Fin 2)) ℂ => M ⟨0⟩ ⟨1⟩)
    (hh.2.2.2.2.2.2.1 (Matrix.single ⟨0⟩ ⟨1⟩ 1))
  have he := congrArg (fun M : Matrix (ULift.{u} (Fin 2)) (ULift.{u} (Fin 2)) ℂ => M ⟨0⟩ ⟨1⟩)
    (hh.2.2.2.2.2.2.2.1 ⟨0⟩ ⟨1⟩)
  norm_num [rejected, realize, Matrix.single] at hz he
  have hbad : (0 : ℂ) = -1 := hz.symm.trans he
  norm_num at hbad

theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨(), 1, 2, ?_⟩
  norm_num [actual, realize]

def registration : Registration arena.{u} (type_of% (@_root_.D5.S3.Quantum.Semigroups.ThresholdSchurSemigroup.result.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (show j = i from @Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := dependence

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Semigroups.ThresholdSchurSemigroup.result.{u})
    (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.Semigroups.ThresholdSchurSemigroup.result.threshold_information_unit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.ThresholdSchurSemigroup.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨registration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => -(x / 2)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Semigroups.ThresholdSchurSemigroup
    definition := none, coordinates := #[], readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body", "arg", "arg", "arg", "arg", "arg", "arg", "fn", "arg", "body", "arg", "body", "body", "fn", "arg"]
      stateBinder := 0, functionOperand := false
      stateOperand := some #["arg", "fn", "arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration
end Reg.D5.S3.Quantum.Semigroups.ThresholdSchurSemigroup
