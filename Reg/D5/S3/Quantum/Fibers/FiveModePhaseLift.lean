import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Fibers.FiveModePhaseLift
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped ComplexOrder

namespace Reg.D5.S3.Quantum.Fibers.FiveModePhaseLift
open _root_.D5.S3.Quantum.Fibers.FiveModePhaseLift
open _root_.D5.S3.Quantum.Fibers.FiveModeRealResponse
open _root_.D5.S3.Quantum.Fibers.RankOneFeedbackProtocol
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  (Set.Icc (0 : ℝ) 1) (fun _ => Matrix (Fin 5) (Fin 5) ℂ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ rho => phaseProbability rho) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => (2 : ℝ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ q : Set.Icc (0 : ℝ) 1,
    (phaseState 1).PosSemidef ∧ Matrix.trace (phaseState 1) = 1 ∧
    (phaseState (-1)).PosSemidef ∧ Matrix.trace (phaseState (-1)) = 1 ∧
    phaseState 1 * phaseState 1 = phaseState 1 ∧
    phaseState (-1) * phaseState (-1) = phaseState (-1) ∧
    phaseState 1 * phaseState (-1) = 0 ∧
    (1 - phaseState 1).PosSemidef ∧ ¬ (phaseState 1).IsDiag ∧
    (mixture q).PosSemidef ∧ Matrix.trace (mixture q) = 1 ∧
    (∀ (r : Set.Icc (0 : ℝ) 1) (P : Protocol (Fin 5)) (h : Record P),
      ludersLaw menu P (mixture q) h = ludersLaw menu P (mixture r) h) ∧
    branchMass (mixture q) = (1 : ℂ) / 2 ∧
    R.readout () q (mixture q) = (q : ℝ)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := (h ⟨0, by norm_num⟩).2.2.2.2.2.2.2.2.2.2.2.2.2
  norm_num [rejected, realize] at he

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  let q : Set.Icc (0 : ℝ) 1 := ⟨0, by norm_num⟩
  let r : Set.Icc (0 : ℝ) 1 := ⟨1, by norm_num⟩
  refine ⟨q, mixture q, mixture r, ?_⟩
  change phaseProbability (mixture q) ≠ phaseProbability (mixture r)
  rw [(phase_lift_certificate q).2.2.2.2.2.2.2.2.2.2.2.2.2,
    (phase_lift_certificate r).2.2.2.2.2.2.2.2.2.2.2.2.2]
  norm_num [q, r]

def family : Registration arena (type_of% (@phase_lift_certificate)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨phase_lift_certificate, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Fibers.FiveModePhaseLift.phase_lift_certificate)
    (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Fibers.FiveModePhaseLift.unit
  realizationName := `Reg.D5.S3.Quantum.Fibers.FiveModePhaseLift.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ rho => phaseProbability rho)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fibers.FiveModePhaseLift
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms family
#print axioms registration
end Reg.D5.S3.Quantum.Fibers.FiveModePhaseLift
