import Mathlib.Tactic.FinCases
import LeanInformationAuditInterface.Contract.NodeFacts
import D5.S3.ConceptDynamics.InformationEscape.ExactRate
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.InformationEscapeCounting.Enumerations
import D5.S3.ConceptDynamics.InformationEscapeCounting.FusedCorrectness
import D5.S3.ConceptDynamics.InformationEscapeHierarchy.HierarchyLaws
import D5.S3.ConceptDynamics.InformationEscapeHierarchy.LayeredCapture
import D5.S3.ConceptDynamics.InformationEscapeHierarchy.RefinementMatrix
import D5.S3.ConceptDynamics.RegistrationWitnesses
import Reg.D5.S0.Certificates.SelfInterestConventionDeviationGain
import Reg.D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling

namespace Reg.Catalogs.IffRegistrations.SealedCatalog
open LeanInformationAudit

def rootCatalog : Contract.RootCatalog := { data := {
  rootId := `Reg.Catalogs.IffRegistrations.SealedCatalog,
  expected := #[{ statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.open_permits_only_unsettled), theoremName := `D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.open_permits_only_unsettled, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.openCodeArena, statementIdentity := some "sha256:48183359aa256091e3dfc2a80a5352b99a62f3ff03446236a0e6d9bd82fa988e", registrationModuleName := `Reg.D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling },
    { statement := (_), proof := (@_root_.D5.S0.Certificates.SelfInterestConventionDeviationGain.dual_fixed_iff), theoremName := `D5.S0.Certificates.SelfInterestConventionDeviationGain.dual_fixed_iff, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.dualArena, statementIdentity := some "sha256:76175c4656a4be731bad802d770e51ed7e427531bf5c0a2577c86dd338299e1f", registrationModuleName := `Reg.D5.S0.Certificates.SelfInterestConventionDeviationGain }],
  source := #[{ statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.open_permits_only_unsettled), theoremName := `D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.open_permits_only_unsettled, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.openCodeArena, statementIdentity := some "sha256:48183359aa256091e3dfc2a80a5352b99a62f3ff03446236a0e6d9bd82fa988e", registrationModuleName := `Reg.D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling },
    { statement := (_), proof := (@_root_.D5.S0.Certificates.SelfInterestConventionDeviationGain.dual_fixed_iff), theoremName := `D5.S0.Certificates.SelfInterestConventionDeviationGain.dual_fixed_iff, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.dualArena, statementIdentity := some "sha256:76175c4656a4be731bad802d770e51ed7e427531bf5c0a2577c86dd338299e1f", registrationModuleName := `Reg.D5.S0.Certificates.SelfInterestConventionDeviationGain }],
  baseline := #[],
  companionPrefix := some `Reg.Catalogs.IffRegistrations } }

noncomputable def dualCatalog : Contract.SealCatalog := {
      arenaName := `D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.dualArena
      catalogId := `D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.dualArena
      arena := (_root_.D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.dualArena).toArena
      size := 1
      units := ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.dualArena).toArena).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.dualRealization)), Statement := _, proof := (@_root_.D5.S0.Certificates.SelfInterestConventionDeviationGain.dual_fixed_iff) }]
      nondegenerate := by decide +kernel
      bundleNonempty := by intro index; fin_cases index <;> decide +kernel
      stateCard := 4
      stateCardEq := by decide +kernel
      full := 4
      fullEq := by decide +kernel
      rows := Fin.cases ({ unique := 8, uniqueEq := by decide +kernel, without := 12, withoutEq := by decide +kernel, roleBins := ![0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0], roleEq := by decide +kernel, roleTotal := by decide +kernel, conclusion := .positive (by decide +kernel) (by exact ((_root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.dualArena).toArena).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.dualRealization)), Statement := _, proof := (@_root_.D5.S0.Certificates.SelfInterestConventionDeviationGain.dual_fixed_iff) }]).lowersEscape_iff_uniqueCaptureCount_pos 0 (by decide +kernel)).mpr (by decide +kernel)) }) (fun i => Fin.elim0 i)
      collisions := #[]
      conclusion := .irredundant (by
        intro index
        fin_cases index
        · exact ((_root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.dualArena).toArena).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.dualRealization)), Statement := _, proof := (@_root_.D5.S0.Certificates.SelfInterestConventionDeviationGain.dual_fixed_iff) }]).lowersEscape_iff_uniqueCaptureCount_pos 0 (by decide +kernel)).mpr (by decide +kernel))
      enumeration := {
        states := [(false,false), (false,true), (true,false), (true,true)]
        nodup := by
          change ([(false,false), (false,true), (true,false), (true,true)] : List (Bool × Bool)).Nodup
          decide +kernel
        complete := by
          change ([(false,false), (false,true), (true,false), (true,true)] :
            List (Bool × Bool)).toFinset = (Finset.univ : Finset (Bool × Bool))
          ext ⟨a,b⟩
          cases a <;> cases b <;> simp }
    }

noncomputable def «seal» : Contract.Seal := {
  rootId := `Reg.Catalogs.IffRegistrations.SealedCatalog
  catalogs := #[
    dualCatalog,
    {
      arenaName := `D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.openCodeArena
      catalogId := `D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.openCodeArena
      arena := (_root_.D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.openCodeArena).toArena
      size := 1
      units := ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.openCodeArena).toArena).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.openRealization)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.open_permits_only_unsettled) }]
      nondegenerate := by decide +kernel
      bundleNonempty := by intro index; fin_cases index <;> decide +kernel
      stateCard := 5
      stateCardEq := by decide +kernel
      full := 12
      fullEq := by decide +kernel
      rows := Fin.cases ({ unique := 8, uniqueEq := by decide +kernel, without := 20, withoutEq := by decide +kernel, roleBins := ![0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0], roleEq := by decide +kernel, roleTotal := by decide +kernel, conclusion := .positive (by decide +kernel) (by exact ((_root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.openCodeArena).toArena).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.openRealization)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.open_permits_only_unsettled) }]).lowersEscape_iff_uniqueCaptureCount_pos 0 (by decide +kernel)).mpr (by decide +kernel)) }) (fun i => Fin.elim0 i)
      collisions := #[]
      conclusion := .irredundant (by
        intro index
        fin_cases index
        · exact ((_root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.openCodeArena).toArena).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.openRealization)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.open_permits_only_unsettled) }]).lowersEscape_iff_uniqueCaptureCount_pos 0 (by decide +kernel)).mpr (by decide +kernel))
      enumeration := by letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.openCodeArena).toArena).stateFintype; letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.openCodeArena).toArena).stateDecidableEq; exact ⟨Finset.univ.toList, Finset.nodup_toList _, by simp⟩
    }
  ]
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


namespace LiteralEvidence
open LeanInformationAudit.Contract
open _root_.D5.S3.ConceptDynamics.InformationEscape
open _root_.D5.S3.ConceptDynamics.InformationEscape.IffRegistrations
open _root_.D5.S0.Certificates.SelfInterestConventionDeviationGain

noncomputable def row : SealRow (Catalog.ofVector dualCatalog.units) (⟨0, by decide +kernel⟩ : Fin dualCatalog.size) where
  unique := 8
  uniqueEq := by decide +kernel
  without := 12
  withoutEq := by decide +kernel
  roleBins := ![0,0,0,0,0,0,0,8,0,0,0,0,0,0,0]
  roleEq := by decide +kernel
  roleTotal := by decide +kernel
  conclusion := .positive (by decide +kernel) (by
    exact (Catalog.lowersEscape_iff_uniqueCaptureCount_pos _ _ (by decide +kernel)).mpr
      (by decide +kernel))

noncomputable def facts : SealFacts dualCatalog where
  units := {
    entries := [{
      position := 0
      within := by decide +kernel
      item := {
        primitives := dualRealization.toPrimitiveBundle
        Statement := _
        proof := @_root_.D5.S0.Certificates.SelfInterestConventionDeviationGain.dual_fixed_iff }
      correct := by rfl }]
    complete := rfl }
  rows := [{
    position := 0
    within := by decide +kernel
    row := row
    correct := by rfl
    bins := {
      entries := [{ position := 0, within := (by decide +kernel), item := 0, correct := (by decide +kernel) },
        { position := 1, within := (by decide +kernel), item := 0, correct := (by decide +kernel) },
        { position := 2, within := (by decide +kernel), item := 0, correct := (by decide +kernel) },
        { position := 3, within := (by decide +kernel), item := 0, correct := (by decide +kernel) },
        { position := 4, within := (by decide +kernel), item := 0, correct := (by decide +kernel) },
        { position := 5, within := (by decide +kernel), item := 0, correct := (by decide +kernel) },
        { position := 6, within := (by decide +kernel), item := 0, correct := (by decide +kernel) },
        { position := 7, within := (by decide +kernel), item := 8, correct := (by decide +kernel) },
        { position := 8, within := (by decide +kernel), item := 0, correct := (by decide +kernel) },
        { position := 9, within := (by decide +kernel), item := 0, correct := (by decide +kernel) },
        { position := 10, within := (by decide +kernel), item := 0, correct := (by decide +kernel) },
        { position := 11, within := (by decide +kernel), item := 0, correct := (by decide +kernel) },
        { position := 12, within := (by decide +kernel), item := 0, correct := (by decide +kernel) },
        { position := 13, within := (by decide +kernel), item := 0, correct := (by decide +kernel) },
        { position := 14, within := (by decide +kernel), item := 0, correct := (by decide +kernel) }]
      complete := rfl }
    axes := {
      rows := [{ index := (by change Bool ⊕ Fin 0; exact Sum.inl false), axis := .cut, correct := (by decide +kernel) },
        { index := (by change Bool ⊕ Fin 0; exact Sum.inl true), axis := .cut, correct := (by decide +kernel) }]
      nodup := by
        change ([Sum.inl false, Sum.inl true] : List (Bool ⊕ Fin 0)).Nodup
        decide +kernel
      complete := by
        change ∀ i : Bool ⊕ Fin 0, i ∈ [Sum.inl false, Sum.inl true]
        intro i
        cases i with
        | inl b => cases b <;> simp
        | inr i => exact Fin.elim0 i }
    partition := {
      rows := [{ item := (false,false), classId := 0 },
        { item := (false,true), classId := 1 },
        { item := (true,false), classId := 1 },
        { item := (true,true), classId := 0 }]
      nodup := by
        change ([(false,false), (false,true), (true,false), (true,true)] : List (Bool × Bool)).Nodup
        decide +kernel
      complete := by
        change ∀ x : Bool × Bool, x ∈ [(false,false), (false,true), (true,false), (true,true)]
        decide +kernel
      classes := by decide +kernel }
    stateOrder := by
      rfl }]
  complete := rfl

end LiteralEvidence

end Reg.Catalogs.IffRegistrations.SealedCatalog
