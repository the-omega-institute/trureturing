import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourRateSupermodularity
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourRateSupermodularity

open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourRateSupermodularity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Fin 4 → ℝ
  State _ := Fin 4 → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ X => H X) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ X => H X + 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (X Y : Fin 4 → ℝ), InCube X → InCube Y →
    R.readout () Y X + H Y ≤ H (X ⊓ Y) + H (X ⊔ Y)

private def leftPoint : Fin 4 → ℝ := ![lower, upper, lower, lower]
private theorem left_cube : InCube leftPoint := by
  intro i
  fin_cases i <;> norm_num [leftPoint, lower, upper]

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have h := law leftPoint leftPoint left_cube left_cube
  change (H leftPoint + 1) + H leftPoint ≤ H (leftPoint ⊓ leftPoint) + H (leftPoint ⊔ leftPoint) at h
  simp only [inf_idem, sup_idem] at h
  linarith

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨fun _ => lower, fun _ => lower, fun _ => upper, ?_⟩
  norm_num [actual, realize, H, envelope, ceilingRate, lower, upper,
    threshold, tailCap, slope, intercept]

def record : Registration arena (type_of% (@four_rate_supermodular)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨four_rate_supermodular, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact False.elim (hj (@Subsingleton.elim Unit _ j i))
    · intro i
      exact nomatch i
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@four_rate_supermodular)
    (type_of% (realize signature (fun _ _ X => H X) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourRateSupermodularity.fourRate,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourRateSupermodularity.record,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨record⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ X => H X) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourRateSupermodularity,
    definition := none, coordinates := #[1], readouts := #[
      { path := #["body", "body", "body", "body", "fn", "arg", "fn", "arg"],
        stateBinder := 0, functionOperand := false, stateOperand := some #["arg"],
        booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

#print axioms record
end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourRateSupermodularity
