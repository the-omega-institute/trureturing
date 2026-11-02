import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.Ergodicity.IrreducibleVisibleErgodicity
import Reg.Support.DependentFamily
import Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkedPredictiveQuotient

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open MeasureTheory LeanInformationAudit
open scoped Classical
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkedPredictiveQuotient
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalLawTrimming
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.Ergodicity.IrreducibleVisibleErgodicity
open _root_.Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkedPredictiveQuotient (toy)

namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.Ergodicity.IrreducibleVisibleErgodicity
universe u

/-- The observation acts on the full integer-bit path space. Only the role is finite. -/
@[reducible] def signature : Signature where
  Params := Unit
  State _ := ℤ → Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ → Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ z t => z (1 + t)) Empty.elim

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => true) Empty.elim

/-- All source binders, dictionaries and the actual visible measure remain in the law. -/
@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ {H : Type u} [Fintype H] [MeasurableSpace H] [MeasurableSingletonClass H]
    (θ : Presentation H)
    (_hirr : Matrix.IsIrreducible (θ.matrix false + θ.matrix true)),
    Ergodic (R.readout () ()) (visibleLaw θ : Measure (ℤ → Bool))

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let θ := toy.{u}
  have hirr : Matrix.IsIrreducible (θ.matrix false + θ.matrix true) := by
    apply (Matrix.isIrreducible_iff_exists_pow_pos
      (fun i j => add_nonneg (θ.matrix_nonneg false i j)
        (θ.matrix_nonneg true i j))).mpr
    intro i j
    exact ⟨1, by norm_num, by simp [θ, toy]⟩
  have he : Ergodic (fun _z : ℤ → Bool => fun _t : ℤ => true)
      (visibleLaw θ : Measure (ℤ → Bool)) := h θ hirr
  have hno := (same_law_trimming θ).2.2.2.2.2.2.2.2.1
  have hfalse : ∀ᵐ _z ∂(visibleLaw θ : Measure (ℤ → Bool)), False :=
    (he.toMeasurePreserving.quasiMeasurePreserving.ae hno).mono
      (fun _ hz => hz 0 ⟨rfl, rfl⟩)
  simpa using (ae_iff.mp hfalse)

def family : Registration arena.{u} (type_of% (@actual_output_ergodic.{u})) where
  actual := realize signature (fun _ _ z t => z (1 + t)) Empty.elim
  bridge := Iff.rfl
  variation := ⟨@actual_output_ergodic.{u}, rejected, rejected_law⟩
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
    refine ⟨(), (fun _ => false), (fun _ => true), ?_⟩
    intro he
    have hh := congrFun he (0 : ℤ)
    change (false : Bool) = true at hh
    exact Bool.noConfusion hh

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@actual_output_ergodic.{u}) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.Ergodicity.IrreducibleVisibleErgodicity.unit
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.Ergodicity.IrreducibleVisibleErgodicity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z t => z (1 + t)) Empty.elim)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  -- The direct-source contract reconstructs the origin slot from sourceSelection.
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.Ergodicity.IrreducibleVisibleErgodicity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false}]}
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit
end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.Ergodicity.IrreducibleVisibleErgodicity
