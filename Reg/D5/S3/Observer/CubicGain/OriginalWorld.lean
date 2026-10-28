import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.CubicGain.OriginalWorld
import Reg.Support.SingleDependentReadout

/-! Faithful dependent-readout registration of the source statements. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Reg.D5.S3.Observer.CubicGain.OriginalWorld
open _root_.D5.S3.Observer.CubicGain
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature Unit
  (fun _ => Gain) (fun _ => WithBot ℕ)
def actual : Realization signature :=
  realize signature (fun _ _ c => (Polynomial.ofFn 4 c).degree) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 4) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ c : Gain, R.readout () () c ≤ 3
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 0
  norm_num [rejected,realize] at hh

def family : Registration arena (type_of% @coefficient_degree) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨coefficient_degree,rejected,rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := by
    intro i
    refine ⟨(),![0,0,0,0],![1,0,0,0],?_⟩
    norm_num [actual,realize,Polynomial.ofFn_eq_sum_monomial,Fin.sum_univ_four]
    exact WithBot.bot_ne_coe

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@coefficient_degree) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Observer.CubicGain.OriginalWorld.coefficient_degree.__information_unit
  realizationName := `Reg.D5.S3.Observer.CubicGain.OriginalWorld.family
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
    (fun _ _ c => (Polynomial.ofFn 4 c).degree) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.CubicGain.OriginalWorld
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Reg.D5.S3.Observer.CubicGain.OriginalWorld
