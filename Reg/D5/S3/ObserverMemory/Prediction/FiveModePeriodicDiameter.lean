import D5.S3.ObserverMemory.Prediction.FiveModePeriodicDiameter
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

/-! Source-realized audit of the periodic generated-law obstruction. -/

open _root_.D5.S3.ObserverMemory.Prediction.FiniteStartFiveModeSource
open _root_.D5.S3.ObserverMemory.Prediction.FiveModePredictiveLawGeometry
open _root_.D5.S3.ObserverMemory.Prediction.FiveModeAutonomousSharpCount
open _root_.D5.S3.ObserverMemory.Prediction.FiveModeSelfGeneratedLaws
open _root_.D5.S3.ObserverMemory.Prediction.FiveModePeriodicDiameter
open _root_.D5.S3.TotalVariation.Pinsker _root_.D5.S3.TotalVariation.Metric
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ObserverMemory.Prediction.FiveModePeriodicDiameter
universe u
noncomputable section
attribute [local instance] Classical.propDecidable

@[reducible] def signature : Signature where
  Params := Type u
  State Z := GeneratedObserver Z
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ Z := Z → LawProfile
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} := realize _
  (fun _ _ O => generatedLaw O.update O.row) (fun e => nomatch e)

def rejected : Realization signature.{u} := realize _
  (fun _ _ _ => fun _ => orientedMixture (1/8) (1/8) (1/8) (1/2/2))
  (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature.{u}
  Law F := ∀ {Z : Type u} (O : GeneratedObserver Z) {p q r D : ℝ}
    (_hp : admissible p q r) (_hne : a p q ≠ b r)
    (z : Z) (L : Nat) (_hL : 0 < L)
    (_hper : (fun z => O.update z B)^[L] z = z) (_hD : 0 < D) (_hD1 : D < 1)
    (_h0 : profileDistance (dominantLaw p q r) (F.readout () Z O z) ≤ D/2)
    (_h1 : profileDistance (orientedMixture p q r D) (F.readout () Z O z) ≤ D/2), False

private def delta (y : Visible) : GeneratedObserver (ULift.{u} Unit) where
  initial := ⟨()⟩
  update _ _ := ⟨()⟩
  row _ v := if v = y then 1 else 0
  row_nonneg _ _ := by split_ifs <;> norm_num
  row_sum _ := by simp

private theorem positive : arena.{u}.Law actual := @periodic_diameter_obstruction.{u}

private theorem negative : ¬ arena.{u}.Law rejected := by
  intro law
  have hp : admissible (1/8) (1/8) (1/8) := by norm_num [admissible]
  have hne : a (1/8) (1/8) ≠ b (1/8) := by norm_num [a,b]
  have h0 : profileDistance (dominantLaw (1/8) (1/8) (1/8))
      (orientedMixture (1/8) (1/8) (1/8) (1/2/2)) ≤ (1/2 : ℝ)/2 := by
    rw [dominant_as_zero, (oriented_geometry hp (by norm_num : (0:ℝ) ∈ Set.Icc 0 1)
      (by norm_num : (1/2/2:ℝ) ∈ Set.Icc 0 1)).2.2]
    norm_num
  have h1 : profileDistance (orientedMixture (1/8) (1/8) (1/8) (1/2))
      (orientedMixture (1/8) (1/8) (1/8) (1/2/2)) ≤ (1/2 : ℝ)/2 := by
    rw [(oriented_geometry hp (by norm_num : (1/2:ℝ) ∈ Set.Icc 0 1)
      (by norm_num : (1/2/2:ℝ) ∈ Set.Icc 0 1)).2.2]
    norm_num
  exact law (delta B) (D := 1/2) hp hne ⟨()⟩ 1 (by norm_num) rfl (by norm_num) (by norm_num) h0 h1

private theorem dependent : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨ULift.{u} Unit,delta 0,delta 1,?_⟩
  intro he
  have hh := congrFun (congrFun (congrFun he ⟨()⟩) 1) (fun _ => 0)
  norm_num [actual, realize, generatedLaw, delta] at hh

def evidence : Registration arena.{u} (type_of% (@periodic_diameter_obstruction.{u})) where
  actual := realize signature.{u}
    (fun _ _ O => generatedLaw O.update O.row) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨positive,rejected,negative⟩
  sensitivity := ⟨fun i => ⟨rejected,fun j h => (h (Subsingleton.elim j i)).elim,rfl,negative⟩,
    fun i => nomatch i⟩
  dependence := dependent

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.ObserverMemory.Prediction.FiveModePeriodicDiameter.periodic_diameter_obstruction.{u})
    (type_of% (realize signature.{u}
      (fun _ _ O => generatedLaw O.update O.row) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.ObserverMemory.Prediction.FiveModePeriodicDiameter.periodic_diameter_obstruction,
  realizationName := `Reg.D5.S3.ObserverMemory.Prediction.FiveModePeriodicDiameter.evidence,
  realizationSource := none, generated := false,
  arena := .source ⟨arena.{u}⟩, objectArena := .source ⟨arena.{u}⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena.{u} ⟨evidence.{u}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature.{u}
    (fun _ _ O => generatedLaw O.update O.row) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Prediction.FiveModePeriodicDiameter,
    definition := none, coordinates := #[0],
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body",
        "body","body","body","body","body","body","domain","fn","arg","arg","fn"],
      stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

#print axioms evidence
#print axioms registration
end
end Reg.D5.S3.ObserverMemory.Prediction.FiveModePeriodicDiameter
