import D5.S3.Combinatorics.Graph.Chordal.Reconstruction.RoundQuaternionLocalPureScore
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! Observational dependence of the pure-mode estimates on the explicit rim potential. -/

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped Quaternion

noncomputable section

namespace Reg.D5.S3.Combinatorics.Graph.Chordal.Reconstruction.RoundQuaternionLocalPureScore

open _root_.RoundQuaternionLocalSharpness

abbrev signature := _root_.Reg.Support.SingleDependentReadout.signature Unit
  (fun _ => ℂ) (fun _ => ℂ → Fin 3 → ℍ[ℝ])

def actual : Realization signature :=
  realize signature (fun _ _ p => localRim p) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law observer := PureScoreEstimates (observer.readout () ())

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have h := law.rim_unit 0 0 (by norm_num [localR]) (by norm_num [localR]) 0
  change ‖(0 : ℍ[ℝ])‖ = 1 at h
  norm_num at h

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), 0, 1, ?_⟩
  intro h
  change localRim 0 = localRim 1 at h
  have h := congrArg (fun x : ℍ[ℝ] => x.re) (congr_fun (congr_fun h (0 : ℂ)) (0 : Fin 3))
  change localReal 0 0 = localReal 1 0 at h
  have ha := pure_score_estimates.constant_bounds.2.2.2.2.1
  norm_num [localReal] at h
  linarith

def family : Registration arena (type_of% @pure_score_estimates) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@pure_score_estimates, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@pure_score_estimates) (Realization signature) Unit Unit where
  unitName := `RoundQuaternionLocalSharpness.pure_score_estimates.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Chordal.Reconstruction.RoundQuaternionLocalPureScore.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Chordal.Reconstruction.RoundQuaternionLocalPureScore
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Graph.Chordal.Reconstruction.RoundQuaternionLocalPureScore
