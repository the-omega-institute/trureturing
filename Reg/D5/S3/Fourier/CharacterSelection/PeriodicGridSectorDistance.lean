import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Fourier.CharacterSelection.PeriodicGridSectorDistance
import Reg.Support.DependentFamily

/-! Source-bound distance observation on the full family of periodic grids. -/

open _root_.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy
open _root_.D5.S3.Fourier.CharacterSelection.PeriodicGridSectorDistance
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridSectorDistance

abbrev signature : Signature where
  Params := Σ M : ℕ, Σ N : ℕ, EdgeLabel M N
  State p := EdgeLabel p.1 p.2.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p z => edgeDistance p.2.2 z) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {M N : ℕ} [NeZero M] [NeZero N]
    (y : EdgeLabel M N) (_hy : Flat y) (h v : ZMod 2),
    let d := (if rowHolonomy y 0 = h then 0 else M) +
      (if columnHolonomy y 0 = v then 0 else N)
    (∃ z : EdgeLabel M N, Flat z ∧ rowHolonomy z 0 = h ∧
      columnHolonomy z 0 = v ∧ R.readout () ⟨M, N, y⟩ z = d) ∧
    ∀ z : EdgeLabel M N, Flat z → rowHolonomy z 0 = h →
      columnHolonomy z 0 = v → d ≤ R.readout () ⟨M, N, y⟩ z

theorem actual_law : arena.Law actual := by
  intro M N _ _ y hy h v
  exact flat_sector_distance y hy h v

theorem rejected_law : ¬ arena.Law rejected := by
  intro hr
  obtain ⟨z, _, _, _, hd⟩ :=
    (hr (M := 1) (N := 1) (seam 0 0) (seam_flat 0 0) 1 0).1
  norm_num [rejected, realize, rowHolonomy, columnHolonomy, seam] at hd

theorem sensitivity_proof : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hji
    exact (hji (show j = i from @Subsingleton.elim Unit _ j i)).elim
  · intro i
    exact nomatch i

theorem dependence_proof : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨⟨1, 1, seam 0 0⟩, seam 0 0, seam 1 0, ?_⟩
  decide

def registration : Registration arena (type_of% (@flat_sector_distance)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof

def registration_1 : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@flat_sector_distance)
    (type_of% (realize signature (fun _ p z => edgeDistance p.2.2 z)
      (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str
    `D5.S3.Fourier.CharacterSelection.PeriodicGridSectorDistance.flat_sector_distance
    "information_unit"
  realizationName := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridSectorDistance.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p z => edgeDistance p.2.2 z)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.CharacterSelection.PeriodicGridSectorDistance
    definition := none
    coordinates := #[0, 1, 4]
    readouts := #[
      { path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
          "fn", "arg", "arg", "body", "arg", "arg", "arg", "fn", "arg"]
        stateBinder := 9
        functionOperand := false
        stateOperand := none
        booleanPredicate := false },
      { path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
          "arg", "body", "body", "body", "body", "arg"]
        stateBinder := 9
        functionOperand := false
        stateOperand := none
        booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

#print axioms registration

end Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridSectorDistance
