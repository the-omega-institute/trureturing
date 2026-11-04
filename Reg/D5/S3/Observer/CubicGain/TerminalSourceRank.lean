import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.CubicGain.TerminalSourceRank
import Reg.Support.SingleDependentReadout

/-! Faithful dependent-readout registration of the source statements. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Reg.D5.S3.Observer.CubicGain.TerminalSourceRank
open _root_.D5.S3.Observer.CubicGain
open _root_.D5.S3.Observer.CubicGain.TerminalSourceRank
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (Σ _ : FifthAction, ℝ)
    (fun _ => ℝ) (fun _ => Matrix (Fin 6) (Fin 5) ℝ)

def actual : Realization signature :=
  realize signature (fun _ q b => observation q.1 q.2 b) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (F : FifthAction) (r b : ℝ), 0<r → r<1 → 0<b →
    (R.readout () ⟨F,r⟩ b).rank=5 ∧ (reducedObservation F r b).rank=4 ∧
    (residualColumn F r b).rank=1 ∧
    ∀ C z Y p : ℝ,
      Set.Subsingleton {W : OriginalWorld | Compatible F C z Y p W ∧ W.1=r ∧ W.2.1=b}

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h .J (1/2) (1/2) (by norm_num) (by norm_num) (by norm_num)).1
  norm_num [rejected,realize] at hh

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨.J,(1/2 : ℝ)⟩,(1/2 : ℝ),(1 : ℝ),?_⟩
  intro h
  have hh := congrFun (congrFun h (2 : Fin 6)) (1 : Fin 5)
  norm_num [actual,realize,observation,tau,prefixProduct,fifthActionMatrix,
    sourceMatrix,actionJ,actionM,Matrix.mul_apply,Matrix.trace,Fin.sum_univ_two] at hh

def source_registration :
    Registration arena (type_of% @observation_ranks_and_fixed_source_uniqueness) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨observation_ranks_and_fixed_source_uniqueness,rejected,rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@observation_ranks_and_fixed_source_uniqueness) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Observer.CubicGain.TerminalSourceRank.observation_ranks_and_fixed_source_uniqueness.__information_unit
  realizationName := `Reg.D5.S3.Observer.CubicGain.TerminalSourceRank.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ q b => observation q.1 q.2 b)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.CubicGain.TerminalSourceRank
    definition := none
    coordinates := #[0,1]
    readouts := #[{
      path := #["body","body","body","body","body","body","fn","arg","fn","arg","arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration
end Reg.D5.S3.Observer.CubicGain.TerminalSourceRank
