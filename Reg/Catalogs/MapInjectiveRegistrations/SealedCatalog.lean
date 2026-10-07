import Mathlib.Tactic.FinCases
import LeanInformationAuditInterface.Contract.Catalog
import D5.S3.ConceptDynamics.InformationEscape.ExactRate
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.InformationEscapeCounting.Enumerations
import D5.S3.ConceptDynamics.InformationEscapeCounting.FusedCorrectness
import D5.S3.ConceptDynamics.InformationEscapeHierarchy.HierarchyLaws
import D5.S3.ConceptDynamics.InformationEscapeHierarchy.LayeredCapture
import D5.S3.ConceptDynamics.InformationEscapeHierarchy.RefinementMatrix
import D5.S3.ConceptDynamics.RegistrationWitnesses
import Reg.D5.S0.History.Coding.EventCodeIntertranslation
import Reg.D5.S3.QuantumContext.ProjectionValuationObstruction
import Reg.Catalogs.MapInjectiveRegistrations.SealData.States0

namespace Reg.Catalogs.MapInjectiveRegistrations.SealedCatalog
open LeanInformationAudit

def rootCatalog : Contract.RootCatalog := { data := {
  rootId := `Reg.Catalogs.MapInjectiveRegistrations.SealedCatalog,
  expected := #[{ statement := (_), proof := (@_root_.D5.S0.History.Coding.EventCodeIntertranslation.marker_digit_injective), theoremName := `D5.S0.History.Coding.EventCodeIntertranslation.marker_digit_injective, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.markerArena, statementIdentity := some "sha256:a8a72984ee6e03fd422c616af7b7d089aa74da390c05f7710cbbbda1537b4e48", registrationModuleName := `Reg.D5.S0.History.Coding.EventCodeIntertranslation },
    { statement := (_), proof := (@_root_.D5.S0.History.Coding.EventCodeIntertranslation.opcode_index_injective), theoremName := `D5.S0.History.Coding.EventCodeIntertranslation.opcode_index_injective, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.opcodeArena, statementIdentity := some "sha256:f6c867468f7db617eb31f910b6c94236158ff940a852c72020b35a0b813d1521", registrationModuleName := `Reg.D5.S0.History.Coding.EventCodeIntertranslation },
    { statement := (_), proof := (@_root_.D5.S3.QuantumContext.ProjectionValuationObstruction.ks_vectors_injective), theoremName := `D5.S3.QuantumContext.ProjectionValuationObstruction.ks_vectors_injective, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.rayArena, statementIdentity := some "sha256:f03e68530cb8bea7d2c635a151ac9a19cafa007d9c4b3c8919636eac11b477f8", registrationModuleName := `Reg.D5.S3.QuantumContext.ProjectionValuationObstruction }],
  source := #[{ statement := (_), proof := (@_root_.D5.S0.History.Coding.EventCodeIntertranslation.marker_digit_injective), theoremName := `D5.S0.History.Coding.EventCodeIntertranslation.marker_digit_injective, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.markerArena, statementIdentity := some "sha256:a8a72984ee6e03fd422c616af7b7d089aa74da390c05f7710cbbbda1537b4e48", registrationModuleName := `Reg.D5.S0.History.Coding.EventCodeIntertranslation },
    { statement := (_), proof := (@_root_.D5.S0.History.Coding.EventCodeIntertranslation.opcode_index_injective), theoremName := `D5.S0.History.Coding.EventCodeIntertranslation.opcode_index_injective, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.opcodeArena, statementIdentity := some "sha256:f6c867468f7db617eb31f910b6c94236158ff940a852c72020b35a0b813d1521", registrationModuleName := `Reg.D5.S0.History.Coding.EventCodeIntertranslation },
    { statement := (_), proof := (@_root_.D5.S3.QuantumContext.ProjectionValuationObstruction.ks_vectors_injective), theoremName := `D5.S3.QuantumContext.ProjectionValuationObstruction.ks_vectors_injective, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.rayArena, statementIdentity := some "sha256:f03e68530cb8bea7d2c635a151ac9a19cafa007d9c4b3c8919636eac11b477f8", registrationModuleName := `Reg.D5.S3.QuantumContext.ProjectionValuationObstruction }],
  baseline := #[],
  companionPrefix := some `Reg.Catalogs.MapInjectiveRegistrations } }

noncomputable def catalog_0 : Contract.SealCatalog := {
      arenaName := `D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.markerArena
      catalogId := `D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.markerArena
      arena := (_root_.D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.markerArena).toArena
      size := 1
      units := ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.markerArena).toArena).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.markerRealization)), Statement := _, proof := (@_root_.D5.S0.History.Coding.EventCodeIntertranslation.marker_digit_injective) }]
      nondegenerate := by decide +kernel
      bundleNonempty := by intro index; fin_cases index <;> decide +kernel
      stateCard := 2
      stateCardEq := by decide +kernel
      full := 0
      fullEq := by decide +kernel
      rows := Fin.cases ({ unique := 2, uniqueEq := by decide +kernel, without := 2, withoutEq := by decide +kernel, roleBins := ![0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0], roleEq := by decide +kernel, roleTotal := by decide +kernel, conclusion := .positive (by decide +kernel) (by exact ((_root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.markerArena).toArena).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.markerRealization)), Statement := _, proof := (@_root_.D5.S0.History.Coding.EventCodeIntertranslation.marker_digit_injective) }]).lowersEscape_iff_uniqueCaptureCount_pos 0 (by decide +kernel)).mpr (by decide +kernel)) }) (fun i => Fin.elim0 i)
      collisions := #[]
      conclusion := .irredundant (by
        intro index
        fin_cases index
        · exact ((_root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.markerArena).toArena).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.markerRealization)), Statement := _, proof := (@_root_.D5.S0.History.Coding.EventCodeIntertranslation.marker_digit_injective) }]).lowersEscape_iff_uniqueCaptureCount_pos 0 (by decide +kernel)).mpr (by decide +kernel))
      enumeration := {
        states := ([(@Fin.mk (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (nat_lit 0)
  (@Nat.le_of_lt (nat_lit 1) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
    (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))), (@Fin.mk (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (nat_lit 1)
  (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))] : List (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        nodup := by letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.markerArena).toArena).stateDecidableEq; letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.markerArena).toArena).stateFintype; decide +kernel
        complete := by letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.markerArena).toArena).stateDecidableEq; letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.markerArena).toArena).stateFintype; decide +kernel }
    }

noncomputable def facts_0 : Contract.SealFacts catalog_0 where
  units := { entries := [{ position := 0, within := by decide +kernel, item := (D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.marker_bridge.toTheoremUnit
           D5.S0.History.Coding.EventCodeIntertranslation.marker_digit_injective), correct := by rfl }]
             complete := rfl }
  rows := [{
      position := 0
      within := by decide +kernel
      row := {
        unique := 2
        uniqueEq := ((catalog_0.rows (⟨0, by decide +kernel⟩ : Fin catalog_0.size)).uniqueEq).trans (by rfl)
        without := 2
        withoutEq := ((catalog_0.rows (⟨0, by decide +kernel⟩ : Fin catalog_0.size)).withoutEq).trans (by rfl)
        roleBins := ![0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0]
        roleEq := by intro bucket; exact ((catalog_0.rows (⟨0, by decide +kernel⟩ : Fin catalog_0.size)).roleEq bucket).trans (congrFun (by rfl : (catalog_0.rows (⟨0, by decide +kernel⟩ : Fin catalog_0.size)).roleBins = ![0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0]) bucket)
        roleTotal := by decide +kernel
        conclusion := .positive (by decide +kernel) (by
          apply (D5.S3.ConceptDynamics.InformationEscape.Catalog.lowersEscape_iff_uniqueCaptureCount_pos _ _ catalog_0.nondegenerate).mpr
          rw [(catalog_0.rows (⟨0, by decide +kernel⟩ : Fin catalog_0.size)).uniqueEq]
          decide +kernel) }
      correct := by rfl
      bins := { entries := [{ position := 0, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 1, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 2, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 3, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 4, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 5, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 6, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 7, within := by decide +kernel, item := 2, correct := by decide +kernel },
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
                D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.markerArena.State
                (@D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrationTemplates.mapInjectiveSignature
                  (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
              (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
                D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.markerArena.State
                (@D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrationTemplates.mapInjectiveSignature
                  (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
              PUnit.unit), axis := D5.S3.ConceptDynamics.CIRPT.PrimitiveAxis.cut, correct := by decide +kernel }]
                nodup := by
                  change ([(@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.markerArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrationTemplates.mapInjectiveSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.markerArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrationTemplates.mapInjectiveSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
          PUnit.unit)] : List (Sum
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.markerArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrationTemplates.mapInjectiveSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.markerArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrationTemplates.mapInjectiveSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))).Nodup
                  letI : DecidableEq (Sum _ _) := (by change DecidableEq ((catalog_0.units (⟨0, by decide +kernel⟩ : Fin catalog_0.size)).primitives.Index); exact (catalog_0.units (⟨0, by decide +kernel⟩ : Fin catalog_0.size)).primitives.indexDecidableEq); letI : Fintype (Sum _ _) := (by change Fintype ((catalog_0.units (⟨0, by decide +kernel⟩ : Fin catalog_0.size)).primitives.Index); exact (catalog_0.units (⟨0, by decide +kernel⟩ : Fin catalog_0.size)).primitives.indexFintype)
                  decide +kernel
                complete := by
                  change ∀ i : (Sum
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.markerArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrationTemplates.mapInjectiveSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.markerArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrationTemplates.mapInjectiveSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))), i ∈ [(@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.markerArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrationTemplates.mapInjectiveSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.markerArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrationTemplates.mapInjectiveSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
          PUnit.unit)]
                  letI : DecidableEq (Sum _ _) := (by change DecidableEq ((catalog_0.units (⟨0, by decide +kernel⟩ : Fin catalog_0.size)).primitives.Index); exact (catalog_0.units (⟨0, by decide +kernel⟩ : Fin catalog_0.size)).primitives.indexDecidableEq); letI : Fintype (Sum _ _) := (by change Fintype ((catalog_0.units (⟨0, by decide +kernel⟩ : Fin catalog_0.size)).primitives.Index); exact (catalog_0.units (⟨0, by decide +kernel⟩ : Fin catalog_0.size)).primitives.indexFintype)
                  decide +kernel }
      partition := { rows := [{ item := (@Fin.mk (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (nat_lit 0)
               (@Nat.le_of_lt (nat_lit 1) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                 (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))), classId := 0 },
                       { item := (@Fin.mk (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (nat_lit 1)
               (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))), classId := 1 }]
                     nodup := by
                       letI := catalog_0.arena.stateDecidableEq; letI := catalog_0.arena.stateFintype
                       change ([(@Fin.mk (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (nat_lit 0)
               (@Nat.le_of_lt (nat_lit 1) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                 (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))), (@Fin.mk (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (nat_lit 1)
               (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))] : List (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))).Nodup
                       decide +kernel
                     complete := by
                       letI := catalog_0.arena.stateDecidableEq; letI := catalog_0.arena.stateFintype
                       change ∀ x : (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))), x ∈ [(@Fin.mk (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (nat_lit 0)
               (@Nat.le_of_lt (nat_lit 1) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                 (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))), (@Fin.mk (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (nat_lit 1)
               (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))]
                       decide +kernel
                     classes := by letI := catalog_0.arena.stateDecidableEq; letI := catalog_0.arena.stateFintype; decide +kernel }
      stateOrder := by rfl }]
  complete := rfl

noncomputable def view_0 : Contract.SealCatalogView := { catalog := catalog_0, facts := facts_0 }

noncomputable def catalog_1 : Contract.SealCatalog := {
      arenaName := `D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.opcodeArena
      catalogId := `D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.opcodeArena
      arena := (_root_.D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.opcodeArena).toArena
      size := 1
      units := ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.opcodeArena).toArena).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.opcodeRealization)), Statement := _, proof := (@_root_.D5.S0.History.Coding.EventCodeIntertranslation.opcode_index_injective) }]
      nondegenerate := by decide +kernel
      bundleNonempty := by intro index; fin_cases index <;> decide +kernel
      stateCard := 12
      stateCardEq := by decide +kernel
      full := 0
      fullEq := by decide +kernel
      rows := Fin.cases ({ unique := 132, uniqueEq := by decide +kernel, without := 132, withoutEq := by decide +kernel, roleBins := ![0, 0, 0, 0, 0, 0, 0, 132, 0, 0, 0, 0, 0, 0, 0], roleEq := by decide +kernel, roleTotal := by decide +kernel, conclusion := .positive (by decide +kernel) (by exact ((_root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.opcodeArena).toArena).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.opcodeRealization)), Statement := _, proof := (@_root_.D5.S0.History.Coding.EventCodeIntertranslation.opcode_index_injective) }]).lowersEscape_iff_uniqueCaptureCount_pos 0 (by decide +kernel)).mpr (by decide +kernel)) }) (fun i => Fin.elim0 i)
      collisions := #[]
      conclusion := .irredundant (by
        intro index
        fin_cases index
        · exact ((_root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.opcodeArena).toArena).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.opcodeRealization)), Statement := _, proof := (@_root_.D5.S0.History.Coding.EventCodeIntertranslation.opcode_index_injective) }]).lowersEscape_iff_uniqueCaptureCount_pos 0 (by decide +kernel)).mpr (by decide +kernel))
      enumeration := {
        states := ([(state_0), (state_1), (state_2), (state_3), (state_4), (state_5), (state_6), (state_7), (state_8), (state_9), (@Fin.mk (@OfNat.ofNat Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) (nat_lit 10)
  (@Nat.le_of_lt (nat_lit 11) (@OfNat.ofNat Nat (nat_lit 12) (instOfNatNat (nat_lit 12)))
    (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 12) (instOfNatNat (nat_lit 12)))))), (@Fin.mk (@OfNat.ofNat Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) (nat_lit 11)
  (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 12) (instOfNatNat (nat_lit 12)))))] : List (Fin (@OfNat.ofNat Nat (nat_lit 12) (instOfNatNat (nat_lit 12)))))
        nodup := by letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.opcodeArena).toArena).stateDecidableEq; letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.opcodeArena).toArena).stateFintype; decide +kernel
        complete := by letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.opcodeArena).toArena).stateDecidableEq; letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.opcodeArena).toArena).stateFintype; decide +kernel }
    }

noncomputable def facts_1 : Contract.SealFacts catalog_1 where
  units := { entries := [{ position := 0, within := by decide +kernel, item := (D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.opcode_bridge.toTheoremUnit
           D5.S0.History.Coding.EventCodeIntertranslation.opcode_index_injective), correct := by rfl }]
             complete := rfl }
  rows := [{
      position := 0
      within := by decide +kernel
      row := {
        unique := 132
        uniqueEq := ((catalog_1.rows (⟨0, by decide +kernel⟩ : Fin catalog_1.size)).uniqueEq).trans (by rfl)
        without := 132
        withoutEq := ((catalog_1.rows (⟨0, by decide +kernel⟩ : Fin catalog_1.size)).withoutEq).trans (by rfl)
        roleBins := ![0, 0, 0, 0, 0, 0, 0, 132, 0, 0, 0, 0, 0, 0, 0]
        roleEq := by intro bucket; exact ((catalog_1.rows (⟨0, by decide +kernel⟩ : Fin catalog_1.size)).roleEq bucket).trans (congrFun (by rfl : (catalog_1.rows (⟨0, by decide +kernel⟩ : Fin catalog_1.size)).roleBins = ![0, 0, 0, 0, 0, 0, 0, 132, 0, 0, 0, 0, 0, 0, 0]) bucket)
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
                  { position := 7, within := by decide +kernel, item := 132, correct := by decide +kernel },
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
                D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.opcodeArena.State
                (@D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrationTemplates.mapInjectiveSignature
                  (Fin (@OfNat.ofNat Nat (nat_lit 12) (instOfNatNat (nat_lit 12))))
                  (Fin (@OfNat.ofNat Nat (nat_lit 12) (instOfNatNat (nat_lit 12))))
                  (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 12) (instOfNatNat (nat_lit 12))))))
              (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
                D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.opcodeArena.State
                (@D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrationTemplates.mapInjectiveSignature
                  (Fin (@OfNat.ofNat Nat (nat_lit 12) (instOfNatNat (nat_lit 12))))
                  (Fin (@OfNat.ofNat Nat (nat_lit 12) (instOfNatNat (nat_lit 12))))
                  (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 12) (instOfNatNat (nat_lit 12))))))
              PUnit.unit), axis := D5.S3.ConceptDynamics.CIRPT.PrimitiveAxis.cut, correct := by decide +kernel }]
                nodup := by
                  change ([(@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.opcodeArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrationTemplates.mapInjectiveSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 12) (instOfNatNat (nat_lit 12))))
              (Fin (@OfNat.ofNat Nat (nat_lit 12) (instOfNatNat (nat_lit 12))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 12) (instOfNatNat (nat_lit 12))))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.opcodeArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrationTemplates.mapInjectiveSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 12) (instOfNatNat (nat_lit 12))))
              (Fin (@OfNat.ofNat Nat (nat_lit 12) (instOfNatNat (nat_lit 12))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 12) (instOfNatNat (nat_lit 12))))))
          PUnit.unit)] : List (Sum
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.opcodeArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrationTemplates.mapInjectiveSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 12) (instOfNatNat (nat_lit 12))))
              (Fin (@OfNat.ofNat Nat (nat_lit 12) (instOfNatNat (nat_lit 12))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 12) (instOfNatNat (nat_lit 12))))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.opcodeArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrationTemplates.mapInjectiveSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 12) (instOfNatNat (nat_lit 12))))
              (Fin (@OfNat.ofNat Nat (nat_lit 12) (instOfNatNat (nat_lit 12))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 12) (instOfNatNat (nat_lit 12)))))))).Nodup
                  letI : DecidableEq (Sum _ _) := (by change DecidableEq ((catalog_1.units (⟨0, by decide +kernel⟩ : Fin catalog_1.size)).primitives.Index); exact (catalog_1.units (⟨0, by decide +kernel⟩ : Fin catalog_1.size)).primitives.indexDecidableEq); letI : Fintype (Sum _ _) := (by change Fintype ((catalog_1.units (⟨0, by decide +kernel⟩ : Fin catalog_1.size)).primitives.Index); exact (catalog_1.units (⟨0, by decide +kernel⟩ : Fin catalog_1.size)).primitives.indexFintype)
                  decide +kernel
                complete := by
                  change ∀ i : (Sum
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.opcodeArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrationTemplates.mapInjectiveSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 12) (instOfNatNat (nat_lit 12))))
              (Fin (@OfNat.ofNat Nat (nat_lit 12) (instOfNatNat (nat_lit 12))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 12) (instOfNatNat (nat_lit 12))))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.opcodeArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrationTemplates.mapInjectiveSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 12) (instOfNatNat (nat_lit 12))))
              (Fin (@OfNat.ofNat Nat (nat_lit 12) (instOfNatNat (nat_lit 12))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 12) (instOfNatNat (nat_lit 12))))))), i ∈ [(@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.opcodeArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrationTemplates.mapInjectiveSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 12) (instOfNatNat (nat_lit 12))))
              (Fin (@OfNat.ofNat Nat (nat_lit 12) (instOfNatNat (nat_lit 12))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 12) (instOfNatNat (nat_lit 12))))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.opcodeArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrationTemplates.mapInjectiveSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 12) (instOfNatNat (nat_lit 12))))
              (Fin (@OfNat.ofNat Nat (nat_lit 12) (instOfNatNat (nat_lit 12))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 12) (instOfNatNat (nat_lit 12))))))
          PUnit.unit)]
                  letI : DecidableEq (Sum _ _) := (by change DecidableEq ((catalog_1.units (⟨0, by decide +kernel⟩ : Fin catalog_1.size)).primitives.Index); exact (catalog_1.units (⟨0, by decide +kernel⟩ : Fin catalog_1.size)).primitives.indexDecidableEq); letI : Fintype (Sum _ _) := (by change Fintype ((catalog_1.units (⟨0, by decide +kernel⟩ : Fin catalog_1.size)).primitives.Index); exact (catalog_1.units (⟨0, by decide +kernel⟩ : Fin catalog_1.size)).primitives.indexFintype)
                  decide +kernel }
      partition := { rows := [{ item := (state_0), classId := 0 },
                       { item := (state_1), classId := 1 },
                       { item := (state_2), classId := 2 },
                       { item := (state_3), classId := 3 },
                       { item := (state_4), classId := 4 },
                       { item := (state_5), classId := 5 },
                       { item := (state_6), classId := 6 },
                       { item := (state_7), classId := 7 },
                       { item := (state_8), classId := 8 },
                       { item := (state_9), classId := 9 },
                       { item := (@Fin.mk (@OfNat.ofNat Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) (nat_lit 10)
               (@Nat.le_of_lt (nat_lit 11) (@OfNat.ofNat Nat (nat_lit 12) (instOfNatNat (nat_lit 12)))
                 (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 12) (instOfNatNat (nat_lit 12)))))), classId := 10 },
                       { item := (@Fin.mk (@OfNat.ofNat Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) (nat_lit 11)
               (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 12) (instOfNatNat (nat_lit 12))))), classId := 11 }]
                     nodup := by
                       letI := catalog_1.arena.stateDecidableEq; letI := catalog_1.arena.stateFintype
                       change ([(state_0), (state_1), (state_2), (state_3), (state_4), (state_5), (state_6), (state_7), (state_8), (state_9), (@Fin.mk (@OfNat.ofNat Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) (nat_lit 10)
               (@Nat.le_of_lt (nat_lit 11) (@OfNat.ofNat Nat (nat_lit 12) (instOfNatNat (nat_lit 12)))
                 (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 12) (instOfNatNat (nat_lit 12)))))), (@Fin.mk (@OfNat.ofNat Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) (nat_lit 11)
               (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 12) (instOfNatNat (nat_lit 12)))))] : List (Fin (@OfNat.ofNat Nat (nat_lit 12) (instOfNatNat (nat_lit 12))))).Nodup
                       decide +kernel
                     complete := by
                       letI := catalog_1.arena.stateDecidableEq; letI := catalog_1.arena.stateFintype
                       change ∀ x : (Fin (@OfNat.ofNat Nat (nat_lit 12) (instOfNatNat (nat_lit 12)))), x ∈ [(state_0), (state_1), (state_2), (state_3), (state_4), (state_5), (state_6), (state_7), (state_8), (state_9), (@Fin.mk (@OfNat.ofNat Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) (nat_lit 10)
               (@Nat.le_of_lt (nat_lit 11) (@OfNat.ofNat Nat (nat_lit 12) (instOfNatNat (nat_lit 12)))
                 (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 12) (instOfNatNat (nat_lit 12)))))), (@Fin.mk (@OfNat.ofNat Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) (nat_lit 11)
               (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 12) (instOfNatNat (nat_lit 12)))))]
                       decide +kernel
                     classes := by letI := catalog_1.arena.stateDecidableEq; letI := catalog_1.arena.stateFintype; decide +kernel }
      stateOrder := by rfl }]
  complete := rfl

noncomputable def view_1 : Contract.SealCatalogView := { catalog := catalog_1, facts := facts_1 }

noncomputable def catalog_2 : Contract.SealCatalog := {
      arenaName := `D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.rayArena
      catalogId := `D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.rayArena
      arena := (_root_.D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.rayArena).toArena
      size := 1
      units := ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.rayArena).toArena).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.rayRealization)), Statement := _, proof := (@_root_.D5.S3.QuantumContext.ProjectionValuationObstruction.ks_vectors_injective) }]
      nondegenerate := by decide +kernel
      bundleNonempty := by intro index; fin_cases index <;> decide +kernel
      stateCard := 18
      stateCardEq := by decide +kernel
      full := 0
      fullEq := by let states : _root_.D5.S3.ConceptDynamics.InformationEscape.Arena.StateEnumeration (_root_.D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.rayArena).toArena := ⟨(List.finRange 18 : List (Fin 18)), (by change (List.finRange 18 : List (Fin 18)).Nodup; decide +kernel), (by change (List.finRange 18 : List (Fin 18)).toFinset = (Finset.univ : Finset (Fin 18)); decide +kernel)⟩; let catalog := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.rayArena).toArena).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.rayRealization)), Statement := _, proof := (@_root_.D5.S3.QuantumContext.ProjectionValuationObstruction.ks_vectors_injective) }]; let indices := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.finIndexEnumeration 1; exact (catalog.fusedFull_eq_escapeNumerator states indices).symm.trans (by decide +kernel)
      rows := Fin.cases ({ unique := 306, uniqueEq := by let states : _root_.D5.S3.ConceptDynamics.InformationEscape.Arena.StateEnumeration (_root_.D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.rayArena).toArena := ⟨(List.finRange 18 : List (Fin 18)), (by change (List.finRange 18 : List (Fin 18)).Nodup; decide +kernel), (by change (List.finRange 18 : List (Fin 18)).toFinset = (Finset.univ : Finset (Fin 18)); decide +kernel)⟩; let catalog := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.rayArena).toArena).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.rayRealization)), Statement := _, proof := (@_root_.D5.S3.QuantumContext.ProjectionValuationObstruction.ks_vectors_injective) }]; let indices := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.finIndexEnumeration 1; exact (catalog.fusedUnique_eq_uniqueCaptureCount states indices (0 : Fin 1)).symm.trans (by decide +kernel), without := 306, withoutEq := by let states : _root_.D5.S3.ConceptDynamics.InformationEscape.Arena.StateEnumeration (_root_.D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.rayArena).toArena := ⟨(List.finRange 18 : List (Fin 18)), (by change (List.finRange 18 : List (Fin 18)).Nodup; decide +kernel), (by change (List.finRange 18 : List (Fin 18)).toFinset = (Finset.univ : Finset (Fin 18)); decide +kernel)⟩; let catalog := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.rayArena).toArena).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.rayRealization)), Statement := _, proof := (@_root_.D5.S3.QuantumContext.ProjectionValuationObstruction.ks_vectors_injective) }]; let indices := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.finIndexEnumeration 1; exact (catalog.fusedWithout_eq_escapeNumerator_without states indices (0 : Fin 1)).symm.trans (by decide +kernel), roleBins := ![0, 0, 0, 0, 0, 0, 0, 306, 0, 0, 0, 0, 0, 0, 0], roleEq := by let states : _root_.D5.S3.ConceptDynamics.InformationEscape.Arena.StateEnumeration (_root_.D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.rayArena).toArena := ⟨(List.finRange 18 : List (Fin 18)), (by change (List.finRange 18 : List (Fin 18)).Nodup; decide +kernel), (by change (List.finRange 18 : List (Fin 18)).toFinset = (Finset.univ : Finset (Fin 18)); decide +kernel)⟩; let catalog := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.rayArena).toArena).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.rayRealization)), Statement := _, proof := (@_root_.D5.S3.QuantumContext.ProjectionValuationObstruction.ks_vectors_injective) }]; let indices := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.finIndexEnumeration 1; exact fun bucket => (catalog.fusedRoleBins_eq_roleHistogram states indices (0 : Fin 1) bucket).symm.trans (congrFun (by decide +kernel : (catalog.fusedCounts states indices).roleBins (0 : Fin 1) = ![0, 0, 0, 0, 0, 0, 0, 306, 0, 0, 0, 0, 0, 0, 0]) bucket), roleTotal := by decide +kernel, conclusion := .positive (by decide +kernel) (by exact ((_root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.rayArena).toArena).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.rayRealization)), Statement := _, proof := (@_root_.D5.S3.QuantumContext.ProjectionValuationObstruction.ks_vectors_injective) }]).lowersEscape_iff_uniqueCaptureCount_pos 0 (by decide +kernel)).mpr (by decide +kernel)) }) (fun i => Fin.elim0 i)
      collisions := #[]
      conclusion := .irredundant (by
        intro index
        fin_cases index
        · exact ((_root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.rayArena).toArena).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.rayRealization)), Statement := _, proof := (@_root_.D5.S3.QuantumContext.ProjectionValuationObstruction.ks_vectors_injective) }]).lowersEscape_iff_uniqueCaptureCount_pos 0 (by decide +kernel)).mpr (by decide +kernel))
      enumeration := {
        states := ([(state_10), (state_11), (state_12), (state_13), (state_14), (state_15), (state_16), (state_17), (state_18), (state_19), (state_20), (state_21), (state_22), (state_23), (state_24), (state_25), (@Fin.mk (@OfNat.ofNat Nat (nat_lit 18) (instOfNatNat (nat_lit 18))) (nat_lit 16)
  (@Nat.le_of_lt (nat_lit 17) (@OfNat.ofNat Nat (nat_lit 18) (instOfNatNat (nat_lit 18)))
    (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 18) (instOfNatNat (nat_lit 18)))))), (@Fin.mk (@OfNat.ofNat Nat (nat_lit 18) (instOfNatNat (nat_lit 18))) (nat_lit 17)
  (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 18) (instOfNatNat (nat_lit 18)))))] : List (Fin (@OfNat.ofNat Nat (nat_lit 18) (instOfNatNat (nat_lit 18)))))
        nodup := by letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.rayArena).toArena).stateDecidableEq; letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.rayArena).toArena).stateFintype; decide +kernel
        complete := by letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.rayArena).toArena).stateDecidableEq; letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.rayArena).toArena).stateFintype; decide +kernel }
    }

noncomputable def facts_2 : Contract.SealFacts catalog_2 where
  units := { entries := [{ position := 0, within := by decide +kernel, item := (D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.ray_bridge.toTheoremUnit
           D5.S3.QuantumContext.ProjectionValuationObstruction.ks_vectors_injective), correct := by rfl }]
             complete := rfl }
  rows := [{
      position := 0
      within := by decide +kernel
      row := {
        unique := 306
        uniqueEq := ((catalog_2.rows (⟨0, by decide +kernel⟩ : Fin catalog_2.size)).uniqueEq).trans (by rfl)
        without := 306
        withoutEq := ((catalog_2.rows (⟨0, by decide +kernel⟩ : Fin catalog_2.size)).withoutEq).trans (by rfl)
        roleBins := ![0, 0, 0, 0, 0, 0, 0, 306, 0, 0, 0, 0, 0, 0, 0]
        roleEq := by intro bucket; exact ((catalog_2.rows (⟨0, by decide +kernel⟩ : Fin catalog_2.size)).roleEq bucket).trans (congrFun (by rfl : (catalog_2.rows (⟨0, by decide +kernel⟩ : Fin catalog_2.size)).roleBins = ![0, 0, 0, 0, 0, 0, 0, 306, 0, 0, 0, 0, 0, 0, 0]) bucket)
        roleTotal := by decide +kernel
        conclusion := .positive (by decide +kernel) (by
          apply (D5.S3.ConceptDynamics.InformationEscape.Catalog.lowersEscape_iff_uniqueCaptureCount_pos _ _ catalog_2.nondegenerate).mpr
          rw [(catalog_2.rows (⟨0, by decide +kernel⟩ : Fin catalog_2.size)).uniqueEq]
          decide +kernel) }
      correct := by rfl
      bins := { entries := [{ position := 0, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 1, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 2, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 3, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 4, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 5, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 6, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 7, within := by decide +kernel, item := 306, correct := by decide +kernel },
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
                D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.rayArena.State
                (@D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrationTemplates.mapInjectiveSignature
                  (Fin (@OfNat.ofNat Nat (nat_lit 18) (instOfNatNat (nat_lit 18))))
                  D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.RayCode
                  (instDecidableEqFin D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.rayCardinality)))
              (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
                D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.rayArena.State
                (@D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrationTemplates.mapInjectiveSignature
                  (Fin (@OfNat.ofNat Nat (nat_lit 18) (instOfNatNat (nat_lit 18))))
                  D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.RayCode
                  (instDecidableEqFin D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.rayCardinality)))
              PUnit.unit), axis := D5.S3.ConceptDynamics.CIRPT.PrimitiveAxis.cut, correct := by decide +kernel }]
                nodup := by
                  change ([(@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.rayArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrationTemplates.mapInjectiveSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 18) (instOfNatNat (nat_lit 18))))
              D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.RayCode
              (instDecidableEqFin D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.rayCardinality)))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.rayArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrationTemplates.mapInjectiveSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 18) (instOfNatNat (nat_lit 18))))
              D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.RayCode
              (instDecidableEqFin D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.rayCardinality)))
          PUnit.unit)] : List (Sum
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.rayArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrationTemplates.mapInjectiveSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 18) (instOfNatNat (nat_lit 18))))
              D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.RayCode
              (instDecidableEqFin D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.rayCardinality)))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.rayArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrationTemplates.mapInjectiveSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 18) (instOfNatNat (nat_lit 18))))
              D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.RayCode
              (instDecidableEqFin D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.rayCardinality))))).Nodup
                  letI : DecidableEq (Sum _ _) := (by change DecidableEq ((catalog_2.units (⟨0, by decide +kernel⟩ : Fin catalog_2.size)).primitives.Index); exact (catalog_2.units (⟨0, by decide +kernel⟩ : Fin catalog_2.size)).primitives.indexDecidableEq); letI : Fintype (Sum _ _) := (by change Fintype ((catalog_2.units (⟨0, by decide +kernel⟩ : Fin catalog_2.size)).primitives.Index); exact (catalog_2.units (⟨0, by decide +kernel⟩ : Fin catalog_2.size)).primitives.indexFintype)
                  decide +kernel
                complete := by
                  change ∀ i : (Sum
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.rayArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrationTemplates.mapInjectiveSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 18) (instOfNatNat (nat_lit 18))))
              D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.RayCode
              (instDecidableEqFin D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.rayCardinality)))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.rayArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrationTemplates.mapInjectiveSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 18) (instOfNatNat (nat_lit 18))))
              D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.RayCode
              (instDecidableEqFin D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.rayCardinality)))), i ∈ [(@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.rayArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrationTemplates.mapInjectiveSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 18) (instOfNatNat (nat_lit 18))))
              D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.RayCode
              (instDecidableEqFin D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.rayCardinality)))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.rayArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrationTemplates.mapInjectiveSignature
              (Fin (@OfNat.ofNat Nat (nat_lit 18) (instOfNatNat (nat_lit 18))))
              D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.RayCode
              (instDecidableEqFin D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.rayCardinality)))
          PUnit.unit)]
                  letI : DecidableEq (Sum _ _) := (by change DecidableEq ((catalog_2.units (⟨0, by decide +kernel⟩ : Fin catalog_2.size)).primitives.Index); exact (catalog_2.units (⟨0, by decide +kernel⟩ : Fin catalog_2.size)).primitives.indexDecidableEq); letI : Fintype (Sum _ _) := (by change Fintype ((catalog_2.units (⟨0, by decide +kernel⟩ : Fin catalog_2.size)).primitives.Index); exact (catalog_2.units (⟨0, by decide +kernel⟩ : Fin catalog_2.size)).primitives.indexFintype)
                  decide +kernel }
      partition := { rows := [{ item := (state_10), classId := 0 },
                       { item := (state_11), classId := 1 },
                       { item := (state_12), classId := 2 },
                       { item := (state_13), classId := 3 },
                       { item := (state_14), classId := 4 },
                       { item := (state_15), classId := 5 },
                       { item := (state_16), classId := 6 },
                       { item := (state_17), classId := 7 },
                       { item := (state_18), classId := 8 },
                       { item := (state_19), classId := 9 },
                       { item := (state_20), classId := 10 },
                       { item := (state_21), classId := 11 },
                       { item := (state_22), classId := 12 },
                       { item := (state_23), classId := 13 },
                       { item := (state_24), classId := 14 },
                       { item := (state_25), classId := 15 },
                       { item := (@Fin.mk (@OfNat.ofNat Nat (nat_lit 18) (instOfNatNat (nat_lit 18))) (nat_lit 16)
               (@Nat.le_of_lt (nat_lit 17) (@OfNat.ofNat Nat (nat_lit 18) (instOfNatNat (nat_lit 18)))
                 (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 18) (instOfNatNat (nat_lit 18)))))), classId := 16 },
                       { item := (@Fin.mk (@OfNat.ofNat Nat (nat_lit 18) (instOfNatNat (nat_lit 18))) (nat_lit 17)
               (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 18) (instOfNatNat (nat_lit 18))))), classId := 17 }]
                     nodup := by
                       letI := catalog_2.arena.stateDecidableEq; letI := catalog_2.arena.stateFintype
                       change ([(state_10), (state_11), (state_12), (state_13), (state_14), (state_15), (state_16), (state_17), (state_18), (state_19), (state_20), (state_21), (state_22), (state_23), (state_24), (state_25), (@Fin.mk (@OfNat.ofNat Nat (nat_lit 18) (instOfNatNat (nat_lit 18))) (nat_lit 16)
               (@Nat.le_of_lt (nat_lit 17) (@OfNat.ofNat Nat (nat_lit 18) (instOfNatNat (nat_lit 18)))
                 (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 18) (instOfNatNat (nat_lit 18)))))), (@Fin.mk (@OfNat.ofNat Nat (nat_lit 18) (instOfNatNat (nat_lit 18))) (nat_lit 17)
               (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 18) (instOfNatNat (nat_lit 18)))))] : List (Fin (@OfNat.ofNat Nat (nat_lit 18) (instOfNatNat (nat_lit 18))))).Nodup
                       decide +kernel
                     complete := by
                       letI := catalog_2.arena.stateDecidableEq; letI := catalog_2.arena.stateFintype
                       change ∀ x : (Fin (@OfNat.ofNat Nat (nat_lit 18) (instOfNatNat (nat_lit 18)))), x ∈ [(state_10), (state_11), (state_12), (state_13), (state_14), (state_15), (state_16), (state_17), (state_18), (state_19), (state_20), (state_21), (state_22), (state_23), (state_24), (state_25), (@Fin.mk (@OfNat.ofNat Nat (nat_lit 18) (instOfNatNat (nat_lit 18))) (nat_lit 16)
               (@Nat.le_of_lt (nat_lit 17) (@OfNat.ofNat Nat (nat_lit 18) (instOfNatNat (nat_lit 18)))
                 (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 18) (instOfNatNat (nat_lit 18)))))), (@Fin.mk (@OfNat.ofNat Nat (nat_lit 18) (instOfNatNat (nat_lit 18))) (nat_lit 17)
               (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 18) (instOfNatNat (nat_lit 18)))))]
                       decide +kernel
                     classes := by letI := catalog_2.arena.stateDecidableEq; letI := catalog_2.arena.stateFintype; decide +kernel }
      stateOrder := by rfl }]
  complete := rfl

noncomputable def view_2 : Contract.SealCatalogView := { catalog := catalog_2, facts := facts_2 }

noncomputable def «seal» : Contract.Seal := {
  rootId := `Reg.Catalogs.MapInjectiveRegistrations.SealedCatalog
  catalogs := #[
    view_0,
    view_1,
    view_2
  ]
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxRecDepth, value := .nat 100000 }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }

end Reg.Catalogs.MapInjectiveRegistrations.SealedCatalog
