import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Fourier.Concentration.CrtMarginalCollision

/-! The mixed Fourier magnitude changes the joint collision mass. -/

namespace Reg.D5.S3.Fourier.Concentration.CrtMarginalCollision

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.Concentration.CrtMarginalCollision
open _root_.D5.S3.Fourier.Concentration.CyclicCollisionCertificate
open _root_.Reg.Support

noncomputable section

abbrev signature := SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ n => (13 / 16 : ℝ) ^ n) (fun e => nomatch e)

def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ (p : ℕ) (_ : 0 < p),
    let coordinatesP : Fin 3 → ℤ := ![0, 3, 4]
    let weightsP : Fin 3 → ℝ := ![1 / 2, 1 / 4, 1 / 4]
    let coordinatesQ : Fin 3 → ℤ := ![0, 1, 0]
    let weightsQ : Fin 3 → ℝ := ![3 / 4, 1 / 4, 0]
    let mixedQ := V.readout () () p
    let A := cyclicCollisionMass 2 coordinatesP weightsP p {0}
    let B := cyclicCollisionMass 3 coordinatesP weightsP p {0}
    A = cyclicCollisionMass 2 coordinatesQ weightsQ p {0} ∧
    B = cyclicCollisionMass 3 coordinatesQ weightsQ p {0} ∧
    cyclicCollisionMass 6 coordinatesP weightsP p {0} < A * B ∧
    A * B < cyclicCollisionMass 6 coordinatesQ weightsQ p {0} ∧
    cyclicCollisionMass 6 coordinatesP weightsP p {0} - A * B =
      ((1 / 16 : ℝ) ^ p - (7 / 64 : ℝ) ^ p) / 3 ∧
    cyclicCollisionMass 6 coordinatesQ weightsQ p {0} - A * B =
      (mixedQ - (7 / 64 : ℝ) ^ p) / 3

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have hbad := (law 1 (by decide)).2.2.2.2.2
  have hactual := (crt_marginal_collision_gap 1 (by decide)).2.2.2.2.2
  norm_num [rejected, realize] at hbad hactual
  linarith only [hbad, hactual]

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨(), 0, 1, ?_⟩
  change (13 / 16 : ℝ) ^ 0 ≠ (13 / 16 : ℝ) ^ 1
  norm_num

def evidence : Registration arena (type_of% @crt_marginal_collision_gap) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@crt_marginal_collision_gap, rejected, rejected_law⟩
  sensitivity := SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@crt_marginal_collision_gap) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Concentration.CrtMarginalCollision.unit
  realizationName := `Reg.D5.S3.Fourier.Concentration.CrtMarginalCollision.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => (13 / 16 : ℝ) ^ n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.Concentration.CrtMarginalCollision
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "value", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Fourier.Concentration.CrtMarginalCollision
