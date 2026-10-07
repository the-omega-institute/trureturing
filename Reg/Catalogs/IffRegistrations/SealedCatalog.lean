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
        states := ([(@Prod.mk Bool Bool Bool.true Bool.true), (@Prod.mk Bool Bool Bool.true Bool.false), (@Prod.mk Bool Bool Bool.false Bool.true), (@Prod.mk Bool Bool Bool.false Bool.false)] : List (Prod Bool Bool))
        nodup := by letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.dualArena).toArena).stateDecidableEq; letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.dualArena).toArena).stateFintype; decide +kernel
        complete := by letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.dualArena).toArena).stateDecidableEq; letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.dualArena).toArena).stateFintype; decide +kernel }
    }

noncomputable def facts_0 : Contract.SealFacts dualCatalog where
  units := { entries := [{ position := 0, within := by decide +kernel, item := (D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.dual_bridge.toTheoremUnit
           D5.S0.Certificates.SelfInterestConventionDeviationGain.dual_fixed_iff), correct := by rfl }]
             complete := rfl }
  rows := [{
      position := 0
      within := by decide +kernel
      row := {
        unique := 8
        uniqueEq := ((dualCatalog.rows (⟨0, by decide +kernel⟩ : Fin dualCatalog.size)).uniqueEq).trans (by rfl)
        without := 12
        withoutEq := ((dualCatalog.rows (⟨0, by decide +kernel⟩ : Fin dualCatalog.size)).withoutEq).trans (by rfl)
        roleBins := ![0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0]
        roleEq := by intro bucket; exact ((dualCatalog.rows (⟨0, by decide +kernel⟩ : Fin dualCatalog.size)).roleEq bucket).trans (congrFun (by rfl : (dualCatalog.rows (⟨0, by decide +kernel⟩ : Fin dualCatalog.size)).roleBins = ![0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0]) bucket)
        roleTotal := by decide +kernel
        conclusion := .positive (by decide +kernel) (by
          apply (D5.S3.ConceptDynamics.InformationEscape.Catalog.lowersEscape_iff_uniqueCaptureCount_pos _ _ dualCatalog.nondegenerate).mpr
          rw [(dualCatalog.rows (⟨0, by decide +kernel⟩ : Fin dualCatalog.size)).uniqueEq]
          decide +kernel) }
      correct := by rfl
      bins := { entries := [{ position := 0, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 1, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 2, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 3, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 4, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 5, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 6, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 7, within := by decide +kernel, item := 8, correct := by decide +kernel },
                  { position := 8, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 9, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 10, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 11, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 12, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 13, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 14, within := by decide +kernel, item := 0, correct := by decide +kernel }]
                complete := rfl }
      axes := { rows := [{ index := by change Sum _ _; exact (@Sum.inl
               (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
                 D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.dualArena.State
                 (D5.S3.ConceptDynamics.InformationEscape.IffRegistrationTemplates.iffSignature
                   D5.S0.Certificates.SelfInterestConventionDeviationGain.Convention))
               (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
                 D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.dualArena.State
                 (D5.S3.ConceptDynamics.InformationEscape.IffRegistrationTemplates.iffSignature
                   D5.S0.Certificates.SelfInterestConventionDeviationGain.Convention))
               Bool.true), axis := D5.S3.ConceptDynamics.CIRPT.PrimitiveAxis.cut, correct := by decide +kernel },
                  { index := by change Sum _ _; exact (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.dualArena.State
            (D5.S3.ConceptDynamics.InformationEscape.IffRegistrationTemplates.iffSignature
              D5.S0.Certificates.SelfInterestConventionDeviationGain.Convention))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.dualArena.State
            (D5.S3.ConceptDynamics.InformationEscape.IffRegistrationTemplates.iffSignature
              D5.S0.Certificates.SelfInterestConventionDeviationGain.Convention))
          Bool.false), axis := D5.S3.ConceptDynamics.CIRPT.PrimitiveAxis.cut, correct := by decide +kernel }]
                nodup := by
                  change ([(@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.dualArena.State
            (D5.S3.ConceptDynamics.InformationEscape.IffRegistrationTemplates.iffSignature
              D5.S0.Certificates.SelfInterestConventionDeviationGain.Convention))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.dualArena.State
            (D5.S3.ConceptDynamics.InformationEscape.IffRegistrationTemplates.iffSignature
              D5.S0.Certificates.SelfInterestConventionDeviationGain.Convention))
          Bool.true), (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.dualArena.State
            (D5.S3.ConceptDynamics.InformationEscape.IffRegistrationTemplates.iffSignature
              D5.S0.Certificates.SelfInterestConventionDeviationGain.Convention))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.dualArena.State
            (D5.S3.ConceptDynamics.InformationEscape.IffRegistrationTemplates.iffSignature
              D5.S0.Certificates.SelfInterestConventionDeviationGain.Convention))
          Bool.false)] : List (Sum
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.dualArena.State
            (D5.S3.ConceptDynamics.InformationEscape.IffRegistrationTemplates.iffSignature
              D5.S0.Certificates.SelfInterestConventionDeviationGain.Convention))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.dualArena.State
            (D5.S3.ConceptDynamics.InformationEscape.IffRegistrationTemplates.iffSignature
              D5.S0.Certificates.SelfInterestConventionDeviationGain.Convention)))).Nodup
                  letI : DecidableEq (Sum _ _) := (by change DecidableEq ((dualCatalog.units (⟨0, by decide +kernel⟩ : Fin dualCatalog.size)).primitives.Index); exact (dualCatalog.units (⟨0, by decide +kernel⟩ : Fin dualCatalog.size)).primitives.indexDecidableEq); letI : Fintype (Sum _ _) := (by change Fintype ((dualCatalog.units (⟨0, by decide +kernel⟩ : Fin dualCatalog.size)).primitives.Index); exact (dualCatalog.units (⟨0, by decide +kernel⟩ : Fin dualCatalog.size)).primitives.indexFintype)
                  decide +kernel
                complete := by
                  change ∀ i : (Sum
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.dualArena.State
            (D5.S3.ConceptDynamics.InformationEscape.IffRegistrationTemplates.iffSignature
              D5.S0.Certificates.SelfInterestConventionDeviationGain.Convention))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.dualArena.State
            (D5.S3.ConceptDynamics.InformationEscape.IffRegistrationTemplates.iffSignature
              D5.S0.Certificates.SelfInterestConventionDeviationGain.Convention))), i ∈ [(@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.dualArena.State
            (D5.S3.ConceptDynamics.InformationEscape.IffRegistrationTemplates.iffSignature
              D5.S0.Certificates.SelfInterestConventionDeviationGain.Convention))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.dualArena.State
            (D5.S3.ConceptDynamics.InformationEscape.IffRegistrationTemplates.iffSignature
              D5.S0.Certificates.SelfInterestConventionDeviationGain.Convention))
          Bool.true), (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.dualArena.State
            (D5.S3.ConceptDynamics.InformationEscape.IffRegistrationTemplates.iffSignature
              D5.S0.Certificates.SelfInterestConventionDeviationGain.Convention))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.dualArena.State
            (D5.S3.ConceptDynamics.InformationEscape.IffRegistrationTemplates.iffSignature
              D5.S0.Certificates.SelfInterestConventionDeviationGain.Convention))
          Bool.false)]
                  letI : DecidableEq (Sum _ _) := (by change DecidableEq ((dualCatalog.units (⟨0, by decide +kernel⟩ : Fin dualCatalog.size)).primitives.Index); exact (dualCatalog.units (⟨0, by decide +kernel⟩ : Fin dualCatalog.size)).primitives.indexDecidableEq); letI : Fintype (Sum _ _) := (by change Fintype ((dualCatalog.units (⟨0, by decide +kernel⟩ : Fin dualCatalog.size)).primitives.Index); exact (dualCatalog.units (⟨0, by decide +kernel⟩ : Fin dualCatalog.size)).primitives.indexFintype)
                  decide +kernel }
      partition := { rows := [{ item := (@Prod.mk Bool Bool Bool.true Bool.true), classId := 0 },
                       { item := (@Prod.mk Bool Bool Bool.true Bool.false), classId := 1 },
                       { item := (@Prod.mk Bool Bool Bool.false Bool.true), classId := 1 },
                       { item := (@Prod.mk Bool Bool Bool.false Bool.false), classId := 0 }]
                     nodup := by
                       letI := dualCatalog.arena.stateDecidableEq; letI := dualCatalog.arena.stateFintype
                       change ([(@Prod.mk Bool Bool Bool.true Bool.true), (@Prod.mk Bool Bool Bool.true Bool.false), (@Prod.mk Bool Bool Bool.false Bool.true), (@Prod.mk Bool Bool Bool.false Bool.false)] : List (Prod Bool Bool)).Nodup
                       decide +kernel
                     complete := by
                       letI := dualCatalog.arena.stateDecidableEq; letI := dualCatalog.arena.stateFintype
                       change ∀ x : (Prod Bool Bool), x ∈ [(@Prod.mk Bool Bool Bool.true Bool.true), (@Prod.mk Bool Bool Bool.true Bool.false), (@Prod.mk Bool Bool Bool.false Bool.true), (@Prod.mk Bool Bool Bool.false Bool.false)]
                       decide +kernel
                     classes := by letI := dualCatalog.arena.stateDecidableEq; letI := dualCatalog.arena.stateFintype; decide +kernel }
      stateOrder := by rfl }]
  complete := rfl

noncomputable def view_0 : Contract.SealCatalogView := { catalog := dualCatalog, facts := facts_0 }

noncomputable def catalog_1 : Contract.SealCatalog := {
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
      enumeration := {
        states := ([(@Fin.mk (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) (nat_lit 0)
  (@Nat.le_of_lt (nat_lit 1) (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
    (@Nat.le_of_lt (nat_lit 2) (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
      (@Nat.le_of_lt (nat_lit 3) (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
        (@Nat.le_of_lt (nat_lit 4) (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
          (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))))))), (@Fin.mk (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) (nat_lit 1)
  (@Nat.le_of_lt (nat_lit 2) (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
    (@Nat.le_of_lt (nat_lit 3) (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
      (@Nat.le_of_lt (nat_lit 4) (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
        (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))))), (@Fin.mk (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) (nat_lit 2)
  (@Nat.le_of_lt (nat_lit 3) (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
    (@Nat.le_of_lt (nat_lit 4) (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
      (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))))), (@Fin.mk (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) (nat_lit 3)
  (@Nat.le_of_lt (nat_lit 4) (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
    (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))), (@Fin.mk (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) (nat_lit 4)
  (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))] : List (Fin (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))
        nodup := by letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.openCodeArena).toArena).stateDecidableEq; letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.openCodeArena).toArena).stateFintype; decide +kernel
        complete := by letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.openCodeArena).toArena).stateDecidableEq; letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.openCodeArena).toArena).stateFintype; decide +kernel }
    }

noncomputable def facts_1 : Contract.SealFacts catalog_1 where
  units := { entries := [{ position := 0, within := by decide +kernel, item := (D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.open_bridge.toTheoremUnit
           D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.open_permits_only_unsettled), correct := by rfl }]
             complete := rfl }
  rows := [{
      position := 0
      within := by decide +kernel
      row := {
        unique := 8
        uniqueEq := ((catalog_1.rows (⟨0, by decide +kernel⟩ : Fin catalog_1.size)).uniqueEq).trans (by rfl)
        without := 20
        withoutEq := ((catalog_1.rows (⟨0, by decide +kernel⟩ : Fin catalog_1.size)).withoutEq).trans (by rfl)
        roleBins := ![0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0]
        roleEq := by intro bucket; exact ((catalog_1.rows (⟨0, by decide +kernel⟩ : Fin catalog_1.size)).roleEq bucket).trans (congrFun (by rfl : (catalog_1.rows (⟨0, by decide +kernel⟩ : Fin catalog_1.size)).roleBins = ![0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0]) bucket)
        roleTotal := by decide +kernel
        conclusion := .positive (by decide +kernel) (by
          apply (D5.S3.ConceptDynamics.InformationEscape.Catalog.lowersEscape_iff_uniqueCaptureCount_pos _ _ catalog_1.nondegenerate).mpr
          rw [(catalog_1.rows (⟨0, by decide +kernel⟩ : Fin catalog_1.size)).uniqueEq]
          decide +kernel) }
      correct := by rfl
      bins := { entries := [{ position := 0, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 1, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 2, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 3, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 4, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 5, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 6, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 7, within := by decide +kernel, item := 8, correct := by decide +kernel },
                  { position := 8, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 9, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 10, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 11, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 12, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 13, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 14, within := by decide +kernel, item := 0, correct := by decide +kernel }]
                complete := rfl }
      axes := { rows := [{ index := by change Sum _ _; exact (@Sum.inl
               (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
                 D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.openCodeArena.State
                 (D5.S3.ConceptDynamics.InformationEscape.IffRegistrationTemplates.iffSignature
                   (Fin (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))))
               (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
                 D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.openCodeArena.State
                 (D5.S3.ConceptDynamics.InformationEscape.IffRegistrationTemplates.iffSignature
                   (Fin (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))))
               Bool.true), axis := D5.S3.ConceptDynamics.CIRPT.PrimitiveAxis.cut, correct := by decide +kernel },
                  { index := by change Sum _ _; exact (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.openCodeArena.State
            (D5.S3.ConceptDynamics.InformationEscape.IffRegistrationTemplates.iffSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.openCodeArena.State
            (D5.S3.ConceptDynamics.InformationEscape.IffRegistrationTemplates.iffSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))))
          Bool.false), axis := D5.S3.ConceptDynamics.CIRPT.PrimitiveAxis.cut, correct := by decide +kernel }]
                nodup := by
                  change ([(@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.openCodeArena.State
            (D5.S3.ConceptDynamics.InformationEscape.IffRegistrationTemplates.iffSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.openCodeArena.State
            (D5.S3.ConceptDynamics.InformationEscape.IffRegistrationTemplates.iffSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))))
          Bool.true), (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.openCodeArena.State
            (D5.S3.ConceptDynamics.InformationEscape.IffRegistrationTemplates.iffSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.openCodeArena.State
            (D5.S3.ConceptDynamics.InformationEscape.IffRegistrationTemplates.iffSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))))
          Bool.false)] : List (Sum
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.openCodeArena.State
            (D5.S3.ConceptDynamics.InformationEscape.IffRegistrationTemplates.iffSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.openCodeArena.State
            (D5.S3.ConceptDynamics.InformationEscape.IffRegistrationTemplates.iffSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))))).Nodup
                  letI : DecidableEq (Sum _ _) := (by change DecidableEq ((catalog_1.units (⟨0, by decide +kernel⟩ : Fin catalog_1.size)).primitives.Index); exact (catalog_1.units (⟨0, by decide +kernel⟩ : Fin catalog_1.size)).primitives.indexDecidableEq); letI : Fintype (Sum _ _) := (by change Fintype ((catalog_1.units (⟨0, by decide +kernel⟩ : Fin catalog_1.size)).primitives.Index); exact (catalog_1.units (⟨0, by decide +kernel⟩ : Fin catalog_1.size)).primitives.indexFintype)
                  decide +kernel
                complete := by
                  change ∀ i : (Sum
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.openCodeArena.State
            (D5.S3.ConceptDynamics.InformationEscape.IffRegistrationTemplates.iffSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.openCodeArena.State
            (D5.S3.ConceptDynamics.InformationEscape.IffRegistrationTemplates.iffSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))))), i ∈ [(@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.openCodeArena.State
            (D5.S3.ConceptDynamics.InformationEscape.IffRegistrationTemplates.iffSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.openCodeArena.State
            (D5.S3.ConceptDynamics.InformationEscape.IffRegistrationTemplates.iffSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))))
          Bool.true), (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.openCodeArena.State
            (D5.S3.ConceptDynamics.InformationEscape.IffRegistrationTemplates.iffSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.openCodeArena.State
            (D5.S3.ConceptDynamics.InformationEscape.IffRegistrationTemplates.iffSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))))
          Bool.false)]
                  letI : DecidableEq (Sum _ _) := (by change DecidableEq ((catalog_1.units (⟨0, by decide +kernel⟩ : Fin catalog_1.size)).primitives.Index); exact (catalog_1.units (⟨0, by decide +kernel⟩ : Fin catalog_1.size)).primitives.indexDecidableEq); letI : Fintype (Sum _ _) := (by change Fintype ((catalog_1.units (⟨0, by decide +kernel⟩ : Fin catalog_1.size)).primitives.Index); exact (catalog_1.units (⟨0, by decide +kernel⟩ : Fin catalog_1.size)).primitives.indexFintype)
                  decide +kernel }
      partition := { rows := [{ item := (@Fin.mk (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) (nat_lit 0)
               (@Nat.le_of_lt (nat_lit 1) (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                 (@Nat.le_of_lt (nat_lit 2) (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                   (@Nat.le_of_lt (nat_lit 3) (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                     (@Nat.le_of_lt (nat_lit 4) (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                       (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))))))), classId := 0 },
                       { item := (@Fin.mk (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) (nat_lit 1)
               (@Nat.le_of_lt (nat_lit 2) (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                 (@Nat.le_of_lt (nat_lit 3) (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                   (@Nat.le_of_lt (nat_lit 4) (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                     (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))))), classId := 1 },
                       { item := (@Fin.mk (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) (nat_lit 2)
               (@Nat.le_of_lt (nat_lit 3) (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                 (@Nat.le_of_lt (nat_lit 4) (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                   (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))))), classId := 1 },
                       { item := (@Fin.mk (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) (nat_lit 3)
               (@Nat.le_of_lt (nat_lit 4) (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                 (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))), classId := 1 },
                       { item := (@Fin.mk (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) (nat_lit 4)
               (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))), classId := 1 }]
                     nodup := by
                       letI := catalog_1.arena.stateDecidableEq; letI := catalog_1.arena.stateFintype
                       change ([(@Fin.mk (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) (nat_lit 0)
               (@Nat.le_of_lt (nat_lit 1) (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                 (@Nat.le_of_lt (nat_lit 2) (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                   (@Nat.le_of_lt (nat_lit 3) (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                     (@Nat.le_of_lt (nat_lit 4) (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                       (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))))))), (@Fin.mk (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) (nat_lit 1)
               (@Nat.le_of_lt (nat_lit 2) (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                 (@Nat.le_of_lt (nat_lit 3) (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                   (@Nat.le_of_lt (nat_lit 4) (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                     (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))))), (@Fin.mk (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) (nat_lit 2)
               (@Nat.le_of_lt (nat_lit 3) (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                 (@Nat.le_of_lt (nat_lit 4) (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                   (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))))), (@Fin.mk (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) (nat_lit 3)
               (@Nat.le_of_lt (nat_lit 4) (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                 (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))), (@Fin.mk (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) (nat_lit 4)
               (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))] : List (Fin (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))).Nodup
                       decide +kernel
                     complete := by
                       letI := catalog_1.arena.stateDecidableEq; letI := catalog_1.arena.stateFintype
                       change ∀ x : (Fin (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))), x ∈ [(@Fin.mk (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) (nat_lit 0)
               (@Nat.le_of_lt (nat_lit 1) (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                 (@Nat.le_of_lt (nat_lit 2) (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                   (@Nat.le_of_lt (nat_lit 3) (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                     (@Nat.le_of_lt (nat_lit 4) (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                       (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))))))), (@Fin.mk (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) (nat_lit 1)
               (@Nat.le_of_lt (nat_lit 2) (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                 (@Nat.le_of_lt (nat_lit 3) (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                   (@Nat.le_of_lt (nat_lit 4) (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                     (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))))), (@Fin.mk (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) (nat_lit 2)
               (@Nat.le_of_lt (nat_lit 3) (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                 (@Nat.le_of_lt (nat_lit 4) (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                   (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))))), (@Fin.mk (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) (nat_lit 3)
               (@Nat.le_of_lt (nat_lit 4) (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                 (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))), (@Fin.mk (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) (nat_lit 4)
               (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))]
                       decide +kernel
                     classes := by letI := catalog_1.arena.stateDecidableEq; letI := catalog_1.arena.stateFintype; decide +kernel }
      stateOrder := by rfl }]
  complete := rfl

noncomputable def view_1 : Contract.SealCatalogView := { catalog := catalog_1, facts := facts_1 }

noncomputable def «seal» : Contract.Seal := {
  rootId := `Reg.Catalogs.IffRegistrations.SealedCatalog
  catalogs := #[
    view_0,
    view_1
  ]
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }



end Reg.Catalogs.IffRegistrations.SealedCatalog
