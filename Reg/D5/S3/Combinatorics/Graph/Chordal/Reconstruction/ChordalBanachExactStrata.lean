import D5.S3.Combinatorics.Graph.Chordal.Reconstruction.ChordalBanachExactStrata
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Combinatorics.Graph.Chordal.Reconstruction.ChordalBanachExactStrata

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit SimpleGraph.BanachPathPower Omega.RollingCliques.SpanOne
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

private abbrev evenL1Law (R : Realization sig) : Prop :=
  ∀ m : ℕ, 0 < m → ∀ C : ℝ,
    (0 ≤ C ∧ ∀ n, SimpleGraph.PairRetention.Upper (pathPower n (2 * m))
      (PiLp 1 (fun _ : ChordalL1.BalancedCutCoordinate m => ℝ)) C) ↔ R.readout () () m ≤ C

private noncomputable def evenL1Actual : Realization sig :=
  realize sig (fun _ _ m => 2 - 2 / (2 * (m : ℝ))) (fun e => nomatch e)

private abbrev evenL1Arena : Arena := ⟨sig, evenL1Law⟩

private theorem evenL1Rejected : ¬ evenL1Law rejected := by
  intro h
  have hf := (h 1 (by decide) 0).2 (by simp [rejected, realize])
  have hbad := (l1_even_powerPath_exact 1 (by decide) 0).1 hf
  norm_num at hbad

private theorem evenL1Dependence : ObservationalDependence sig evenL1Actual := by
  intro _
  refine ⟨(), 1, 2, ?_⟩
  norm_num [evenL1Actual, realize]

noncomputable def evenL1Family : Registration evenL1Arena (type_of% (@l1_even_powerPath_exact)) where
  actual := evenL1Actual
  bridge := Iff.rfl
  variation := ⟨l1_even_powerPath_exact, rejected, evenL1Rejected⟩
  sensitivity := sensitivity evenL1Law evenL1Actual rejected evenL1Rejected
  dependence := evenL1Dependence

noncomputable def evenL1Registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@l1_even_powerPath_exact) (Realization sig) Type Unit where
  unitName := `D5.S3.Combinatorics.Graph.Chordal.Reconstruction.ChordalBanachExactStrata.l1_even_powerPath_exact.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Chordal.Reconstruction.ChordalBanachExactStrata.evenL1Family
  realizationSource := none
  generated := false
  arena := .source ⟨evenL1Arena⟩
  objectArena := .source ⟨evenL1Arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source evenL1Arena ⟨evenL1Family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize sig (fun _ _ m => 2 - 2 / (2 * (m : ℝ))) (fun e => nomatch e))
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

private abbrev rollingL1Law (R : Realization sig) : Prop :=
  ∀ (M : ℕ) (hM : 2 ≤ M), Even M → ∀ C : ℝ,
    IsUniformL1Bound M hM C ↔ R.readout () () M ≤ C

private noncomputable def rollingL1Actual : Realization sig :=
  realize sig (fun _ _ m => 2 - 2 / (m : ℝ)^2) (fun e => nomatch e)

private abbrev rollingL1Arena : Arena := ⟨sig, rollingL1Law⟩

private theorem rollingL1Rejected : ¬ rollingL1Law rejected := by
  intro h
  have he : Even (2 : ℕ) := by decide
  have hf := (h 2 (by decide) he 0).2 (by simp [rejected, realize])
  have hbad := (uniform_l1_exact 2 (by decide) he 0).1 hf
  norm_num at hbad

private theorem rollingL1Dependence : ObservationalDependence sig rollingL1Actual := by
  intro _
  refine ⟨(), 2, 4, ?_⟩
  norm_num [rollingL1Actual, realize]

noncomputable def rollingL1Family : Registration rollingL1Arena (type_of% (@uniform_l1_exact)) where
  actual := rollingL1Actual
  bridge := Iff.rfl
  variation := ⟨uniform_l1_exact, rejected, rollingL1Rejected⟩
  sensitivity := sensitivity rollingL1Law rollingL1Actual rejected rollingL1Rejected
  dependence := rollingL1Dependence

noncomputable def rollingL1Registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@uniform_l1_exact) (Realization sig) Type Unit where
  unitName := `D5.S3.Combinatorics.Graph.Chordal.Reconstruction.ChordalBanachExactStrata.uniform_l1_exact.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Chordal.Reconstruction.ChordalBanachExactStrata.rollingL1Family
  realizationSource := none
  generated := false
  arena := .source ⟨rollingL1Arena⟩
  objectArena := .source ⟨rollingL1Arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source rollingL1Arena ⟨rollingL1Family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize sig (fun _ _ m => 2 - 2 / (m : ℝ)^2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Chordal.Reconstruction.ChordalBanachExactStrata
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Graph.Chordal.Reconstruction.ChordalBanachExactStrata
