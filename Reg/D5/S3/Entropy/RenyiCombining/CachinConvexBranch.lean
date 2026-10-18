import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Entropy.RenyiCombining.CachinConvexBranch

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Entropy.RenyiCombining.CachinElasticityMonotone
open LeanInformationAudit

namespace Reg.D5.S3.Entropy.RenyiCombining.CachinConvexBranch
noncomputable section
set_option autoImplicit false

abbrev signature := Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ n r => F n r) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ r => r) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℝ), 0 < n → n ≤ 1 / 4 →
    AntitoneOn (R.readout () n) (Set.Ioo 0 1)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (1 / 4) (by norm_num) (by norm_num)
    (a := 1 / 4) (by norm_num) (b := 1 / 2) (by norm_num) (by norm_num)
  norm_num [rejected, realize] at hh

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 0, 1 / 2, ?_⟩
  norm_num [actual, realize, F, A, B, T]

def family : Registration arena
    (type_of% (@_root_.D5.S3.Entropy.RenyiCombining.CachinConvexCertificate.antitoneOn_F)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Entropy.RenyiCombining.CachinConvexCertificate.antitoneOn_F,
    rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Entropy.RenyiCombining.CachinConvexCertificate.antitoneOn_F)
    (Realization signature) Unit Unit where
  unitName := `D5.S3.Entropy.RenyiCombining.CachinConvexCertificate.antitoneOn_F.__information_unit
  realizationName := `Reg.D5.S3.Entropy.RenyiCombining.CachinConvexBranch.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n r => F n r) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Entropy.RenyiCombining.CachinConvexBranch
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end
end Reg.D5.S3.Entropy.RenyiCombining.CachinConvexBranch
