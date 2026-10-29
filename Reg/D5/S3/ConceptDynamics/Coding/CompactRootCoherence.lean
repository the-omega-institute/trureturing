import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.ConceptDynamics.Coding.CompactRootCoherence

open _root_.D5.S3.ConceptDynamics.Coding.CompactRootCoherence
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Coding.CompactRootCoherence

universe u

structure Inputs where
  H : Type u
  group : Group H
  top : TopologicalSpace H
  topGroup : @IsTopologicalGroup H top group
  t2 : @T2Space H top
  compact : @CompactSpace H top
  h : H

def target (P : Inputs.{u}) : Prop := by
  letI := P.group
  letI := P.top
  letI := P.topGroup
  letI := P.t2
  letI := P.compact
  exact (∀ n : ℕ, 0 < n → ∃ x : P.H, x ^ n = P.h) ↔
    ∃ φ : Multiplicative ℚ →* P.H, φ (Multiplicative.ofAdd 1) = P.h

abbrev signature : Signature where
  Params := Inputs.{u}
  State := fun _ => Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ P b => if b then target P else False)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law := fun R => ∀ P : Inputs.{u}, R.readout () P true

abbrev sourceScope := type_of% (@exists_all_positive_roots_iff_exists_rat_hom.{u})

theorem source_bridge : sourceScope.{u} ↔ arena.{u}.Law actual.{u} := by
  constructor
  · intro h P
    letI := P.group
    letI := P.top
    letI := P.topGroup
    letI := P.t2
    letI := P.compact
    simpa [actual, target, realize] using @h P.H P.group P.top P.topGroup P.t2 P.compact P.h
  · intro h H group top topGroup t2 compact h0
    let P : Inputs.{u} := ⟨H, group, top, topGroup, t2, compact, h0⟩
    simpa [actual, target, realize] using h P

theorem actual_positive : arena.{u}.Law actual.{u} :=
  source_bridge.mp (@exists_all_positive_roots_iff_exists_rat_hom)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

def sample : Inputs.{u} where
  H := ULift.{u} Unit
  group := inferInstance
  top := inferInstance
  topGroup := inferInstance
  t2 := inferInstance
  compact := inferInstance
  h := ULift.up ()

theorem sample_target : target sample := by
  exact @exists_all_positive_roots_iff_exists_rat_hom sample.H sample.group sample.top
    sample.topGroup sample.t2 sample.compact sample.h

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hf : rejected.readout () (sample : Inputs.{u}) true := h sample
  simpa [rejected, realize] using hf

def familyRegistration : Registration arena.{u} sourceScope.{u} where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_positive, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · intro a
      exact nomatch a
  dependence := by
    intro i
    cases i
    refine ⟨sample, true, false, ?_⟩
    intro heq
    have ht : actual.readout () (sample : Inputs.{u}) true := by
      simpa [actual, realize] using sample_target
    have hf : ¬ actual.readout () (sample : Inputs.{u}) false := by
      simp [actual, realize]
    exact Eq.mp heq ht

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@exists_all_positive_roots_iff_exists_rat_hom)
      (Realization signature.{u}) Unit Unit where
  unitName := `D5.S3.ConceptDynamics.Coding.CompactRootCoherence.exists_all_positive_roots_iff_exists_rat_hom.__information_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.CompactRootCoherence.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ P b => if b then target P else False) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration

end Reg.D5.S3.ConceptDynamics.Coding.CompactRootCoherence
