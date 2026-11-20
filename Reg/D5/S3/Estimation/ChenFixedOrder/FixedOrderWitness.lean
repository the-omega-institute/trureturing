import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Estimation.ChenFixedOrder.FixedOrderWitness
import Reg.Support.DependentFamily

/-! The comparison of the second weak limit with the standard Gaussian. -/

namespace Reg.D5.S3.Estimation.ChenFixedOrder.FixedOrderWitness

open _root_.D5.S3.Estimation.ChenFixedOrder.FixedOrderWitness
open _root_.D5.S3.Analytic.Probability.MomentPerturbation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open ChenFixedOrderSampling LeanInformationAudit MeasureTheory ProbabilityTheory Filter
open scoped Topology

noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ProbabilityMeasure ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ProbabilityMeasure ℝ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ ν expected => ν ≠ expected)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law readout :=
    Tendsto sampleSize atTop atTop ∧
    Tendsto (fun m => Fintype.card (Population m)) atTop atTop ∧
    (∀ m, populationMean m = 0) ∧
    ∀ r : ℕ, 0 < r →
      ∃ (P Q : (m : ℕ) → ProbabilityMeasure (Sample m)) (ν : ProbabilityMeasure ℝ),
        (∀ m, (P m : Measure (Sample m)) = uniformOn Set.univ) ∧
        (∀ m (A : Finset (Population m)), A.card ≤ r →
          (P m : Measure (Sample m)) (inclusion m A) =
          (Q m : Measure (Sample m)) (inclusion m A)) ∧
        Tendsto (fun m => (P m).map (estimator m)) atTop (𝓝 standardGaussian) ∧
        Tendsto (fun m => (Q m).map (estimator m)) atTop (𝓝 ν) ∧
        readout.readout () () ν standardGaussian

theorem bridge : fixedOrderWitness ↔ arena.Law actual :=
  Iff.rfl

theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  obtain ⟨_, _, _, _, _, _, _, hDistinct⟩ := law.2.2.2 1 Nat.one_pos
  exact hDistinct

theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨(), standardGaussian, tilted 2 standardGaussian, ?_⟩
  intro h
  have hSame : (standardGaussian ≠ standardGaussian) =
      (tilted 2 standardGaussian ≠ standardGaussian) := congrFun h standardGaussian
  exact (hSame.mpr (tilted_gaussian_separation 2).2) rfl

def source_registration : Registration arena fixedOrderWitness where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp fixedOrderWitness_holds, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩, fun e => nomatch e⟩
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@fixedOrderWitness_holds) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Estimation.ChenFixedOrder.FixedOrderWitness.unit
  realizationName := `Reg.D5.S3.Estimation.ChenFixedOrder.FixedOrderWitness.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ ν expected => ν ≠ expected) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Estimation.ChenFixedOrder.FixedOrderWitness
    definition := some {
      owner := `D5.S3.Estimation.ChenFixedOrder.FixedOrderWitness
      name := `D5.S3.Estimation.ChenFixedOrder.FixedOrderWitness.fixedOrderWitness
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["arg", "arg", "arg", "body", "body", "arg", "body", "arg", "body",
        "arg", "body", "arg", "arg", "arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end

end Reg.D5.S3.Estimation.ChenFixedOrder.FixedOrderWitness
