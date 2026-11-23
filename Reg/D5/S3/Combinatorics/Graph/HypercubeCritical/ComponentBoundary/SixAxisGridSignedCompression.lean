import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.SixAxisGridSignedCompression
import Reg.Support.SingleDependentReadout

/-! The observations are the full four-sum projection and its mixed profile. -/

set_option autoImplicit false
set_option linter.style.longLine false

namespace Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.SixAxisGridSignedCompression

open _root_.D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCriticalSpectrum (Q)
open _root_.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9IsotropicHuang
  (weightedAction)
open _root_.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.SixAxisGridSignedCompression
  (Profiles project exteriorAction empty single project_weightedAction three_dvd_mixed_of_eigen
    reconstruct_single_profiles_of_eigen)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Project

private abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => Q 9 → ℤ)
    (fun _ => Q 3 → Profiles)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (f : Q 9 → ℤ) (z : Q 3),
    let P := R.readout () () f
    let HP := project (weightedAction (fun _ => (1 : ℤ)) f) z
    HP.p = (P z).r + (P z).q + exteriorAction (fun x => (P x).p) z ∧
    HP.r = 3 * (P z).p - (P z).s - exteriorAction (fun x => (P x).r) z ∧
    HP.q = 3 * (P z).p + (P z).s - exteriorAction (fun x => (P x).q) z ∧
    HP.s = 3 * (P z).q - 3 * (P z).r + exteriorAction (fun x => (P x).s) z

private def actual : Realization signature :=
  realize signature (fun _ _ f => project f) Empty.elim

private def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => ⟨1, 0, 0, 0⟩) Empty.elim

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have h := (law (fun _ => 0) empty).1
  simp only [project, weightedAction, mul_zero, Finset.sum_const_zero] at h
  change (0 : ℤ) = 0 + 0 + exteriorAction (fun _ => 1) empty at h
  have hK : exteriorAction (fun _ => 1) empty = 3 := by decide
  rw [hK] at h
  omega

def sourceEvidence : Registration arena (type_of% @project_weightedAction) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨project_weightedAction, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro role
    refine ⟨(), fun _ => 0, fun _ => 1, ?_⟩
    intro heq
    have hp := congrArg (fun P : Q 3 → Profiles => (P empty).p) heq
    exact zero_ne_one hp

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@project_weightedAction) (Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.SixAxisGridSignedCompression.project_weightedAction.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.SixAxisGridSignedCompression.Project.sourceEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ f => project f) Empty.elim)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.SixAxisGridSignedCompression
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "value"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Project

namespace Mixed

private abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => Q 9 → ℤ)
    (fun _ => Q 3 → ℤ)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (f : Q 9 → ℤ)
    (hf : ∀ x, weightedAction (fun _ => (1 : ℤ)) f x = 3 * f x) (z : Q 3),
    (3 : ℤ) ∣ exteriorAction (R.readout () () f) z

private def actual : Realization signature :=
  realize signature (fun _ _ f x => (project f x).s) Empty.elim

private def rejected : Realization signature :=
  realize signature (fun _ _ _ z => if z = single 0 then 1 else 0) Empty.elim

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have h := law (fun _ => 0) (fun _ => by simp [weightedAction]) empty
  have hK : exteriorAction (fun z => if z = single 0 then 1 else 0) empty = 1 := by decide
  change (3 : ℤ) ∣ exteriorAction (fun z => if z = single 0 then 1 else 0) empty at h
  rw [hK] at h
  omega

def sourceEvidence : Registration arena (type_of% @three_dvd_mixed_of_eigen) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨three_dvd_mixed_of_eigen, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro role
    refine ⟨(), fun _ => 0, fun _ => 1, ?_⟩
    intro heq
    have hs := congrFun heq empty
    change (project (fun _ => 0) empty).s = (project (fun _ => 1) empty).s at hs
    norm_num [project, Fin.sum_univ_three] at hs

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@three_dvd_mixed_of_eigen) (Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.SixAxisGridSignedCompression.three_dvd_mixed_of_eigen.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.SixAxisGridSignedCompression.Mixed.sourceEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ f x => (project f x).s) Empty.elim)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.SixAxisGridSignedCompression
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

end Mixed

namespace Reconstruction

private abbrev arena : Arena where
  signature := Project.signature
  Law R := ∀ (f : Q 9 → ℤ)
    (hf : ∀ x, weightedAction (fun _ => (1 : ℤ)) f x = 3 * f x) (z : Q 3),
    let P := R.readout () () f
    let u := fun x => 3 * (P x).p - (P x).s
    let v := fun x => 3 * (P x).p + (P x).s
    6 * (P z).r = 3 * u z - exteriorAction u z ∧
    6 * (P z).q = 3 * v z - exteriorAction v z

private def rejected : Realization Project.signature :=
  realize Project.signature (fun _ _ _ _ => ⟨0, 1, 0, 0⟩) Empty.elim

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have h := (law (fun _ => 0) (fun _ => by simp [weightedAction]) empty).1
  change (6 : ℤ) * 1 = 3 * (3 * 0 - 0) - exteriorAction (fun _ => 3 * 0 - 0) empty at h
  norm_num [exteriorAction] at h

def sourceEvidence : Registration arena (type_of% @reconstruct_single_profiles_of_eigen) where
  actual := Project.actual
  bridge := Iff.rfl
  variation := ⟨reconstruct_single_profiles_of_eigen, rejected, rejected_law⟩
  sensitivity :=
    Reg.Support.SingleDependentReadout.sensitivity arena.Law Project.actual rejected rejected_law
  dependence := Project.sourceEvidence.dependence

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@reconstruct_single_profiles_of_eigen) (Realization Project.signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.SixAxisGridSignedCompression.reconstruct_single_profiles_of_eigen.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.SixAxisGridSignedCompression.Reconstruction.sourceEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Project.signature (fun _ _ f => project f) Empty.elim)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.SixAxisGridSignedCompression
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reconstruction

/--
info: 'Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.SixAxisGridSignedCompression.Project.registration' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Project.registration
/--
info: 'Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.SixAxisGridSignedCompression.Mixed.registration' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Mixed.registration
/--
info: 'Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.SixAxisGridSignedCompression.Reconstruction.registration' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Reconstruction.registration

end Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.SixAxisGridSignedCompression
