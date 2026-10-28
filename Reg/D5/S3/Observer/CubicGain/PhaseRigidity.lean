import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.CubicGain.PhaseRigidity
import Reg.Support.SingleDependentReadout

/-! Complete source telescopes for the chronological signed-phase statements. -/

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Observer.CubicGain
open _root_.D5.S3.Observer.CubicGain.CommonWordSensitivity
open _root_.D5.S3.Observer.CubicGain.PrefixKernelSigns
open _root_.D5.S3.Observer.CubicGain.PrimitiveKernelLattice
open _root_.D5.S3.Observer.CubicGain.PhaseRigidity
open scoped Matrix

noncomputable section
namespace Reg.D5.S3.Observer.CubicGain.PhaseRigidity.MixedLevel

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => List Bool) (fun _ => Mat)

def actual : Realization signature :=
  realize signature (fun _ _ u => futureProduct u) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (0 : Mat)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (u : List Bool) (p : PrimitiveCoordinates),
    0 < p.a → 0 < p.b → 0 < p.c → 0 < p.d →
    Mixed (futureProduct u *ᵥ p.column) →
    (p.c:ℝ)*(futureProduct u *ᵥ p.column) 0 -
      (p.d:ℝ)*(futureProduct u *ᵥ p.column) 1 = (p.a:ℝ)*p.c+(p.b:ℝ)*p.d →
    R.readout () () u = 1

private def p : PrimitiveCoordinates := ⟨1,1,1,1,by norm_num,by norm_num,by norm_num⟩

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h [] p (by norm_num [p]) (by norm_num [p])
    (by norm_num [p]) (by norm_num [p])
    (by left; norm_num [p,PrimitiveCoordinates.column,futureProduct])
    (by norm_num [p,PrimitiveCoordinates.column,futureProduct])
  have he := congrArg (fun A : Mat => A 0 0) hh
  norm_num [rejected,realize] at he

def family : Registration arena (type_of% @mixed_level_identity) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨mixed_level_identity,rejected,rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(),[],[false],?_⟩
    intro h
    have he := congrArg (fun A : Mat => A 0 0) h
    norm_num [actual,realize,futureProduct,actionM] at he

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@mixed_level_identity) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Observer.CubicGain.PhaseRigidity.mixed_level_identity.__information_unit
  realizationName := `Reg.D5.S3.Observer.CubicGain.PhaseRigidity.MixedLevel.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ u => futureProduct u) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.CubicGain.PhaseRigidity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms family
#print axioms registration

end Reg.D5.S3.Observer.CubicGain.PhaseRigidity.MixedLevel
