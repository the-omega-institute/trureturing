import D5.S3.Combinatorics.Graph.Chordal.Reconstruction.ChordalBanachExactStrata
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Combinatorics.Graph.Chordal.Reconstruction.ChordalBanachExactStrata

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit SimpleGraph.BanachPathPower
open Reg.Support.SingleDependentReadout (signature sensitivity)

private abbrev sig := signature Unit (fun _ => ℕ) (fun _ => ℝ)

private def actual : Realization sig :=
  realize sig (fun _ _ k => if k = 1 then 0 else if k = 2 then 1 else 2) (fun e => nomatch e)

private def rejected : Realization sig :=
  realize sig (fun _ _ _ => 0) (fun e => nomatch e)

private abbrev law (R : Realization sig) : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ C : ℝ, GroupUniformBound k C ↔ R.readout () () k ≤ C

private abbrev arena : Arena := ⟨sig, law⟩

private theorem rejected_law : ¬ law rejected := by
  intro h
  have hb : GroupUniformBound 2 0 :=
    (h 2 (by decide) 0).2 (by simp [rejected, realize])
  have hbad := (pathPower_group_exact_strata 2 (by decide) 0).1 hb
  norm_num at hbad

private theorem changes_with_width : ObservationalDependence sig actual := by
  intro _
  refine ⟨(), 1, 2, ?_⟩
  norm_num [actual, realize]

def family : Registration arena (type_of% (@pathPower_group_exact_strata)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨pathPower_group_exact_strata, rejected, rejected_law⟩
  sensitivity := sensitivity law actual rejected rejected_law
  dependence := changes_with_width

noncomputable def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@pathPower_group_exact_strata) (Realization sig) Type Unit where
  unitName := `D5.S3.Combinatorics.Graph.Chordal.Reconstruction.ChordalBanachExactStrata.pathPower_group_exact_strata.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Chordal.Reconstruction.ChordalBanachExactStrata.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize sig
    (fun _ _ k => if k = 1 then 0 else if k = 2 then 1 else 2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Chordal.Reconstruction.ChordalBanachExactStrata
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Graph.Chordal.Reconstruction.ChordalBanachExactStrata

