import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Fibers.FiveModeTwoCopyPhase
import Reg.Support.SingleDependentReadout

/-! Registration for the two-copy Bell readout certificate. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped ComplexOrder

namespace Reg.D5.S3.Quantum.Fibers.FiveModeTwoCopyPhase
open _root_.D5.S3.Quantum.Fibers.FiveModeTwoCopyPhase
open _root_.D5.S3.Quantum.Fibers.FiveModePhaseLift
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  (Set.Icc (0 : ℝ) 1) (fun _ => Set.Icc (0 : ℝ) 1) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ q => twoCopyProbability q) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (2 : ℝ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ q : Set.Icc (0 : ℝ) 1,
    bellEffect.PosSemidef ∧ Matrix.trace bellEffect = 1 ∧
    bellEffect * bellEffect = bellEffect ∧
    R.readout () q q = (1 + (1 - 2 * (q : ℝ)) ^ 2) / 4

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := (h ⟨0, by norm_num⟩).2.2.2
  norm_num [rejected, realize] at he

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  let q : Set.Icc (0 : ℝ) 1 := ⟨0, by norm_num⟩
  let r : Set.Icc (0 : ℝ) 1 := ⟨1 / 2, by norm_num⟩
  refine ⟨q, q, r, ?_⟩
  have hneq : twoCopyProbability q ≠ twoCopyProbability r := by
    rw [(two_copy_bell_readout q).2.2.2, (two_copy_bell_readout r).2.2.2]
    norm_num [q, r]
  simpa [actual, realize] using hneq

def family : Registration arena (type_of% (@two_copy_bell_readout)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨two_copy_bell_readout, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Fibers.FiveModeTwoCopyPhase.two_copy_bell_readout)
    (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Fibers.FiveModeTwoCopyPhase.unit
  realizationName := `Reg.D5.S3.Quantum.Fibers.FiveModeTwoCopyPhase.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ q => twoCopyProbability q) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fibers.FiveModeTwoCopyPhase
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "arg", "arg", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms family
#print axioms registration
end Reg.D5.S3.Quantum.Fibers.FiveModeTwoCopyPhase
