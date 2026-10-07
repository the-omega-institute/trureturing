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
import Reg.D5.S0.Diagonal.Lawvere.QualitativeEscape
import Reg.D5.S3.ConceptDynamics.Communication.MutualRecognitionIsJointRealizability
import Reg.Catalogs.ExistentialWitnessRegistrations.SealData.States0
import Reg.Catalogs.ExistentialWitnessRegistrations.SealData.States1
import Reg.Catalogs.ExistentialWitnessRegistrations.SealData.States10
import Reg.Catalogs.ExistentialWitnessRegistrations.SealData.States11
import Reg.Catalogs.ExistentialWitnessRegistrations.SealData.States12
import Reg.Catalogs.ExistentialWitnessRegistrations.SealData.States13
import Reg.Catalogs.ExistentialWitnessRegistrations.SealData.States14
import Reg.Catalogs.ExistentialWitnessRegistrations.SealData.States15
import Reg.Catalogs.ExistentialWitnessRegistrations.SealData.States16
import Reg.Catalogs.ExistentialWitnessRegistrations.SealData.States17
import Reg.Catalogs.ExistentialWitnessRegistrations.SealData.States18
import Reg.Catalogs.ExistentialWitnessRegistrations.SealData.States19
import Reg.Catalogs.ExistentialWitnessRegistrations.SealData.States2
import Reg.Catalogs.ExistentialWitnessRegistrations.SealData.States3
import Reg.Catalogs.ExistentialWitnessRegistrations.SealData.States4
import Reg.Catalogs.ExistentialWitnessRegistrations.SealData.States5
import Reg.Catalogs.ExistentialWitnessRegistrations.SealData.States6
import Reg.Catalogs.ExistentialWitnessRegistrations.SealData.States7
import Reg.Catalogs.ExistentialWitnessRegistrations.SealData.States8
import Reg.Catalogs.ExistentialWitnessRegistrations.SealData.States9

namespace Reg.Catalogs.ExistentialWitnessRegistrations.SealedCatalog
set_option backward.isDefEq.respectTransparency.types false

open LeanInformationAudit

def rootCatalog : Contract.RootCatalog := { data := {
  rootId := `Reg.Catalogs.ExistentialWitnessRegistrations.SealedCatalog,
  expected := #[{ statement := (_), proof := (@_root_.D5.S0.Diagonal.Lawvere.QualitativeEscape.exists_captured_listing_of_fixedPoint), theoremName := `D5.S0.Diagonal.Lawvere.QualitativeEscape.exists_captured_listing_of_fixedPoint, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.capturedArena, statementIdentity := some "sha256:6229f4053788af2b620d04f5df8b8ead8963f1ffb30952697ec73dca847c6886", registrationModuleName := `Reg.D5.S0.Diagonal.Lawvere.QualitativeEscape },
    { statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.Communication.MutualRecognitionIsJointRealizability.mutual_recognition_does_not_require_equal_concepts), theoremName := `D5.S3.ConceptDynamics.Communication.MutualRecognitionIsJointRealizability.mutual_recognition_does_not_require_equal_concepts, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena, statementIdentity := some "sha256:9fe223b46afd61e89e3883878aabd3f4184a39542015b7c4e40ec8c599a7c46c", registrationModuleName := `Reg.D5.S3.ConceptDynamics.Communication.MutualRecognitionIsJointRealizability }],
  source := #[{ statement := (_), proof := (@_root_.D5.S0.Diagonal.Lawvere.QualitativeEscape.exists_captured_listing_of_fixedPoint), theoremName := `D5.S0.Diagonal.Lawvere.QualitativeEscape.exists_captured_listing_of_fixedPoint, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.capturedArena, statementIdentity := some "sha256:6229f4053788af2b620d04f5df8b8ead8963f1ffb30952697ec73dca847c6886", registrationModuleName := `Reg.D5.S0.Diagonal.Lawvere.QualitativeEscape },
    { statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.Communication.MutualRecognitionIsJointRealizability.mutual_recognition_does_not_require_equal_concepts), theoremName := `D5.S3.ConceptDynamics.Communication.MutualRecognitionIsJointRealizability.mutual_recognition_does_not_require_equal_concepts, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena, statementIdentity := some "sha256:9fe223b46afd61e89e3883878aabd3f4184a39542015b7c4e40ec8c599a7c46c", registrationModuleName := `Reg.D5.S3.ConceptDynamics.Communication.MutualRecognitionIsJointRealizability }],
  baseline := #[],
  companionPrefix := some `Reg.Catalogs.ExistentialWitnessRegistrations } }

noncomputable def catalog_0 : Contract.SealCatalog := {
      arenaName := `D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.capturedArena
      catalogId := `D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.capturedArena
      arena := (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.capturedArena).toArena
      size := 1
      units := ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.capturedArena).toArena).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.capturedRealization)), Statement := _, proof := (@_root_.D5.S0.Diagonal.Lawvere.QualitativeEscape.exists_captured_listing_of_fixedPoint) }]
      nondegenerate := by decide +kernel
      bundleNonempty := by intro index; fin_cases index <;> decide +kernel
      stateCard := 8
      stateCardEq := by decide +kernel
      full := 24
      fullEq := by decide +kernel
      rows := Fin.cases ({ unique := 32, uniqueEq := by decide +kernel, without := 56, withoutEq := by decide +kernel, roleBins := ![0, 32, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], roleEq := by decide +kernel, roleTotal := by decide +kernel, conclusion := .positive (by decide +kernel) (by exact ((_root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.capturedArena).toArena).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.capturedRealization)), Statement := _, proof := (@_root_.D5.S0.Diagonal.Lawvere.QualitativeEscape.exists_captured_listing_of_fixedPoint) }]).lowersEscape_iff_uniqueCaptureCount_pos 0 (by decide +kernel)).mpr (by decide +kernel)) }) (fun i => Fin.elim0 i)
      collisions := #[]
      conclusion := .irredundant (by
        intro index
        fin_cases index
        · exact ((_root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.capturedArena).toArena).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.capturedRealization)), Statement := _, proof := (@_root_.D5.S0.Diagonal.Lawvere.QualitativeEscape.exists_captured_listing_of_fixedPoint) }]).lowersEscape_iff_uniqueCaptureCount_pos 0 (by decide +kernel)).mpr (by decide +kernel))
      enumeration := {
        states := ([(state_0), (state_1), (state_2), (state_3), (state_4), (state_5), (state_6), (state_7)] : List (Prod (Bool → Bool) (Unit → Unit → Bool)))
        nodup := by letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.capturedArena).toArena).stateDecidableEq; letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.capturedArena).toArena).stateFintype; decide +kernel
        complete := by letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.capturedArena).toArena).stateDecidableEq; letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.capturedArena).toArena).stateFintype; decide +kernel }
    }

noncomputable def facts_0 : Contract.SealFacts catalog_0 where
  units := { entries := [{ position := 0, within := by decide +kernel, item := (D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.captured_bridge.toTheoremUnit
           D5.S0.Diagonal.Lawvere.QualitativeEscape.exists_captured_listing_of_fixedPoint), correct := by rfl }]
             complete := rfl }
  rows := [{
      position := 0
      within := by decide +kernel
      row := {
        unique := 32
        uniqueEq := ((catalog_0.rows (⟨0, by decide +kernel⟩ : Fin catalog_0.size)).uniqueEq).trans (by rfl)
        without := 56
        withoutEq := ((catalog_0.rows (⟨0, by decide +kernel⟩ : Fin catalog_0.size)).withoutEq).trans (by rfl)
        roleBins := ![0, 32, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
        roleEq := by intro bucket; exact ((catalog_0.rows (⟨0, by decide +kernel⟩ : Fin catalog_0.size)).roleEq bucket).trans (congrFun (by rfl : (catalog_0.rows (⟨0, by decide +kernel⟩ : Fin catalog_0.size)).roleBins = ![0, 32, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) bucket)
        roleTotal := by decide +kernel
        conclusion := .positive (by decide +kernel) (by
          apply (D5.S3.ConceptDynamics.InformationEscape.Catalog.lowersEscape_iff_uniqueCaptureCount_pos _ _ catalog_0.nondegenerate).mpr
          rw [(catalog_0.rows (⟨0, by decide +kernel⟩ : Fin catalog_0.size)).uniqueEq]
          decide +kernel) }
      correct := by rfl
      bins := { entries := [{ position := 0, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 1, within := by decide +kernel, item := 32, correct := by decide +kernel },
                  { position := 2, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 3, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 4, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 5, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 6, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 7, within := by decide +kernel, item := 0, correct := by decide +kernel },
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
                D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.capturedArena.State
                (D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrationTemplates.existentialWitnessSignature
                  (Prod (Bool → Bool) (Unit → Unit → Bool))))
              (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
                D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.capturedArena.State
                (D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrationTemplates.existentialWitnessSignature
                  (Prod (Bool → Bool) (Unit → Unit → Bool))))
              PUnit.unit), axis := D5.S3.ConceptDynamics.CIRPT.PrimitiveAxis.admit, correct := by decide +kernel }]
                nodup := by
                  change ([(@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.capturedArena.State
            (D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrationTemplates.existentialWitnessSignature
              (Prod (Bool → Bool) (Unit → Unit → Bool))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.capturedArena.State
            (D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrationTemplates.existentialWitnessSignature
              (Prod (Bool → Bool) (Unit → Unit → Bool))))
          PUnit.unit)] : List (Sum
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.capturedArena.State
            (D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrationTemplates.existentialWitnessSignature
              (Prod (Bool → Bool) (Unit → Unit → Bool))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.capturedArena.State
            (D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrationTemplates.existentialWitnessSignature
              (Prod (Bool → Bool) (Unit → Unit → Bool)))))).Nodup
                  letI : DecidableEq (Sum _ _) := (by change DecidableEq ((catalog_0.units (⟨0, by decide +kernel⟩ : Fin catalog_0.size)).primitives.Index); exact (catalog_0.units (⟨0, by decide +kernel⟩ : Fin catalog_0.size)).primitives.indexDecidableEq); letI : Fintype (Sum _ _) := (by change Fintype ((catalog_0.units (⟨0, by decide +kernel⟩ : Fin catalog_0.size)).primitives.Index); exact (catalog_0.units (⟨0, by decide +kernel⟩ : Fin catalog_0.size)).primitives.indexFintype)
                  decide +kernel
                complete := by
                  change ∀ i : (Sum
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.capturedArena.State
            (D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrationTemplates.existentialWitnessSignature
              (Prod (Bool → Bool) (Unit → Unit → Bool))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.capturedArena.State
            (D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrationTemplates.existentialWitnessSignature
              (Prod (Bool → Bool) (Unit → Unit → Bool))))), i ∈ [(@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.capturedArena.State
            (D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrationTemplates.existentialWitnessSignature
              (Prod (Bool → Bool) (Unit → Unit → Bool))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.capturedArena.State
            (D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrationTemplates.existentialWitnessSignature
              (Prod (Bool → Bool) (Unit → Unit → Bool))))
          PUnit.unit)]
                  letI : DecidableEq (Sum _ _) := (by change DecidableEq ((catalog_0.units (⟨0, by decide +kernel⟩ : Fin catalog_0.size)).primitives.Index); exact (catalog_0.units (⟨0, by decide +kernel⟩ : Fin catalog_0.size)).primitives.indexDecidableEq); letI : Fintype (Sum _ _) := (by change Fintype ((catalog_0.units (⟨0, by decide +kernel⟩ : Fin catalog_0.size)).primitives.Index); exact (catalog_0.units (⟨0, by decide +kernel⟩ : Fin catalog_0.size)).primitives.indexFintype)
                  decide +kernel }
      partition := { rows := [{ item := (state_0), classId := 0 },
                       { item := (state_1), classId := 1 },
                       { item := (state_2), classId := 0 },
                       { item := (state_3), classId := 0 },
                       { item := (state_4), classId := 1 },
                       { item := (state_5), classId := 1 },
                       { item := (state_6), classId := 1 },
                       { item := (state_7), classId := 0 }]
                     nodup := by
                       letI := catalog_0.arena.stateDecidableEq; letI := catalog_0.arena.stateFintype
                       change ([(state_0), (state_1), (state_2), (state_3), (state_4), (state_5), (state_6), (state_7)] : List (Prod (Bool → Bool) (Unit → Unit → Bool))).Nodup
                       decide +kernel
                     complete := by
                       letI := catalog_0.arena.stateDecidableEq; letI := catalog_0.arena.stateFintype
                       change ∀ x : (Prod (Bool → Bool) (Unit → Unit → Bool)), x ∈ [(state_0), (state_1), (state_2), (state_3), (state_4), (state_5), (state_6), (state_7)]
                       decide +kernel
                     classes := by letI := catalog_0.arena.stateDecidableEq; letI := catalog_0.arena.stateFintype; decide +kernel }
      stateOrder := by rfl }]
  complete := rfl

noncomputable def view_0 : Contract.SealCatalogView := { catalog := catalog_0, facts := facts_0 }

noncomputable def catalog_1 : Contract.SealCatalog := {
      arenaName := `D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena
      catalogId := `D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena
      arena := (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena
      size := 1
      units := ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionRealization)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.Communication.MutualRecognitionIsJointRealizability.mutual_recognition_does_not_require_equal_concepts) }]
      nondegenerate := by decide +kernel
      bundleNonempty := by intro index; fin_cases index <;> decide +kernel
      stateCard := 64
      stateCardEq := by decide +kernel
      full := 2184
      fullEq := by
        let states : _root_.D5.S3.ConceptDynamics.InformationEscape.Arena.StateEnumeration (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena := ⟨(([(fun _ : Bool => false), (fun x : Bool => x), (fun x : Bool => !x), (fun _ : Bool => true)]).flatMap fun f => ([(fun _ : Bool => false), (fun x : Bool => x), (fun x : Bool => !x), (fun _ : Bool => true)]).flatMap fun g => [false, true].flatMap fun a => [false, true].map fun b => (f, g, a, b) : List ((Bool → Bool) × (Bool → Bool) × Bool × Bool)), (by change (([(fun _ : Bool => false), (fun x : Bool => x), (fun x : Bool => !x), (fun _ : Bool => true)]).flatMap fun f => ([(fun _ : Bool => false), (fun x : Bool => x), (fun x : Bool => !x), (fun _ : Bool => true)]).flatMap fun g => [false, true].flatMap fun a => [false, true].map fun b => (f, g, a, b) : List ((Bool → Bool) × (Bool → Bool) × Bool × Bool)).Nodup; decide +kernel), (by change (([(fun _ : Bool => false), (fun x : Bool => x), (fun x : Bool => !x), (fun _ : Bool => true)]).flatMap fun f => ([(fun _ : Bool => false), (fun x : Bool => x), (fun x : Bool => !x), (fun _ : Bool => true)]).flatMap fun g => [false, true].flatMap fun a => [false, true].map fun b => (f, g, a, b) : List ((Bool → Bool) × (Bool → Bool) × Bool × Bool)).toFinset = (Finset.univ : Finset ((Bool → Bool) × (Bool → Bool) × Bool × Bool)); decide +kernel)⟩
        let catalog := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionRealization)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.Communication.MutualRecognitionIsJointRealizability.mutual_recognition_does_not_require_equal_concepts) }]
        let indices := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.finIndexEnumeration 1
        let allStates : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State := [((fun _ : Bool => false), (fun _ : Bool => false), false, false), ((fun _ : Bool => false), (fun _ : Bool => false), false, true), ((fun _ : Bool => false), (fun _ : Bool => false), true, false), ((fun _ : Bool => false), (fun _ : Bool => false), true, true), ((fun _ : Bool => false), (fun x : Bool => x), false, false), ((fun _ : Bool => false), (fun x : Bool => x), false, true), ((fun _ : Bool => false), (fun x : Bool => x), true, false), ((fun _ : Bool => false), (fun x : Bool => x), true, true), ((fun _ : Bool => false), (fun x : Bool => !x), false, false), ((fun _ : Bool => false), (fun x : Bool => !x), false, true), ((fun _ : Bool => false), (fun x : Bool => !x), true, false), ((fun _ : Bool => false), (fun x : Bool => !x), true, true), ((fun _ : Bool => false), (fun _ : Bool => true), false, false), ((fun _ : Bool => false), (fun _ : Bool => true), false, true), ((fun _ : Bool => false), (fun _ : Bool => true), true, false), ((fun _ : Bool => false), (fun _ : Bool => true), true, true), ((fun x : Bool => x), (fun _ : Bool => false), false, false), ((fun x : Bool => x), (fun _ : Bool => false), false, true), ((fun x : Bool => x), (fun _ : Bool => false), true, false), ((fun x : Bool => x), (fun _ : Bool => false), true, true), ((fun x : Bool => x), (fun x : Bool => x), false, false), ((fun x : Bool => x), (fun x : Bool => x), false, true), ((fun x : Bool => x), (fun x : Bool => x), true, false), ((fun x : Bool => x), (fun x : Bool => x), true, true), ((fun x : Bool => x), (fun x : Bool => !x), false, false), ((fun x : Bool => x), (fun x : Bool => !x), false, true), ((fun x : Bool => x), (fun x : Bool => !x), true, false), ((fun x : Bool => x), (fun x : Bool => !x), true, true), ((fun x : Bool => x), (fun _ : Bool => true), false, false), ((fun x : Bool => x), (fun _ : Bool => true), false, true), ((fun x : Bool => x), (fun _ : Bool => true), true, false), ((fun x : Bool => x), (fun _ : Bool => true), true, true), ((fun x : Bool => !x), (fun _ : Bool => false), false, false), ((fun x : Bool => !x), (fun _ : Bool => false), false, true), ((fun x : Bool => !x), (fun _ : Bool => false), true, false), ((fun x : Bool => !x), (fun _ : Bool => false), true, true), ((fun x : Bool => !x), (fun x : Bool => x), false, false), ((fun x : Bool => !x), (fun x : Bool => x), false, true), ((fun x : Bool => !x), (fun x : Bool => x), true, false), ((fun x : Bool => !x), (fun x : Bool => x), true, true), ((fun x : Bool => !x), (fun x : Bool => !x), false, false), ((fun x : Bool => !x), (fun x : Bool => !x), false, true), ((fun x : Bool => !x), (fun x : Bool => !x), true, false), ((fun x : Bool => !x), (fun x : Bool => !x), true, true), ((fun x : Bool => !x), (fun _ : Bool => true), false, false), ((fun x : Bool => !x), (fun _ : Bool => true), false, true), ((fun x : Bool => !x), (fun _ : Bool => true), true, false), ((fun x : Bool => !x), (fun _ : Bool => true), true, true), ((fun _ : Bool => true), (fun _ : Bool => false), false, false), ((fun _ : Bool => true), (fun _ : Bool => false), false, true), ((fun _ : Bool => true), (fun _ : Bool => false), true, false), ((fun _ : Bool => true), (fun _ : Bool => false), true, true), ((fun _ : Bool => true), (fun x : Bool => x), false, false), ((fun _ : Bool => true), (fun x : Bool => x), false, true), ((fun _ : Bool => true), (fun x : Bool => x), true, false), ((fun _ : Bool => true), (fun x : Bool => x), true, true), ((fun _ : Bool => true), (fun x : Bool => !x), false, false), ((fun _ : Bool => true), (fun x : Bool => !x), false, true), ((fun _ : Bool => true), (fun x : Bool => !x), true, false), ((fun _ : Bool => true), (fun x : Bool => !x), true, true), ((fun _ : Bool => true), (fun _ : Bool => true), false, false), ((fun _ : Bool => true), (fun _ : Bool => true), false, true), ((fun _ : Bool => true), (fun _ : Bool => true), true, false), ((fun _ : Bool => true), (fun _ : Bool => true), true, true)]
        let step := fun (counts : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) left =>
          allStates.foldl (fun counts right => catalog.pairStep indices counts left right) counts
        have extCounts (a b : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1))
            (hf : a.full = b.full) (hu : a.unique = b.unique) (hr : a.roleBins = b.roleBins) : a = b := by
          cases a; cases b; cases hf; cases hu; cases hr; rfl
        have block0 : ([((fun _ : Bool => false), (fun _ : Bool => false), false, false), ((fun _ : Bool => false), (fun _ : Bool => false), false, true), ((fun _ : Bool => false), (fun _ : Bool => false), true, false), ((fun _ : Bool => false), (fun _ : Bool => false), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State).foldl step _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts.zero = ({ full := 164, unique := ![88], roleBins := ![![0, 88, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) := by
          apply extCounts
          · decide +kernel
          · apply funext; decide +kernel
          · apply funext; decide +kernel
        have block1 : ([((fun _ : Bool => false), (fun x : Bool => x), false, false), ((fun _ : Bool => false), (fun x : Bool => x), false, true), ((fun _ : Bool => false), (fun x : Bool => x), true, false), ((fun _ : Bool => false), (fun x : Bool => x), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State).foldl step ({ full := 164, unique := ![88], roleBins := ![![0, 88, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) = ({ full := 288, unique := ![216], roleBins := ![![0, 216, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) := by
          apply extCounts
          · decide +kernel
          · apply funext; decide +kernel
          · apply funext; decide +kernel
        have block2 : ([((fun _ : Bool => false), (fun x : Bool => !x), false, false), ((fun _ : Bool => false), (fun x : Bool => !x), false, true), ((fun _ : Bool => false), (fun x : Bool => !x), true, false), ((fun _ : Bool => false), (fun x : Bool => !x), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State).foldl step ({ full := 288, unique := ![216], roleBins := ![![0, 216, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) = ({ full := 412, unique := ![344], roleBins := ![![0, 344, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) := by
          apply extCounts
          · decide +kernel
          · apply funext; decide +kernel
          · apply funext; decide +kernel
        have block3 : ([((fun _ : Bool => false), (fun _ : Bool => true), false, false), ((fun _ : Bool => false), (fun _ : Bool => true), false, true), ((fun _ : Bool => false), (fun _ : Bool => true), true, false), ((fun _ : Bool => false), (fun _ : Bool => true), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State).foldl step ({ full := 412, unique := ![344], roleBins := ![![0, 344, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) = ({ full := 556, unique := ![452], roleBins := ![![0, 452, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) := by
          apply extCounts
          · decide +kernel
          · apply funext; decide +kernel
          · apply funext; decide +kernel
        have block4 : ([((fun x : Bool => x), (fun _ : Bool => false), false, false), ((fun x : Bool => x), (fun _ : Bool => false), false, true), ((fun x : Bool => x), (fun _ : Bool => false), true, false), ((fun x : Bool => x), (fun _ : Bool => false), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State).foldl step ({ full := 556, unique := ![452], roleBins := ![![0, 452, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) = ({ full := 680, unique := ![580], roleBins := ![![0, 580, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) := by
          apply extCounts
          · decide +kernel
          · apply funext; decide +kernel
          · apply funext; decide +kernel
        have block5 : ([((fun x : Bool => x), (fun x : Bool => x), false, false), ((fun x : Bool => x), (fun x : Bool => x), false, true), ((fun x : Bool => x), (fun x : Bool => x), true, false), ((fun x : Bool => x), (fun x : Bool => x), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State).foldl step ({ full := 680, unique := ![580], roleBins := ![![0, 580, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) = ({ full := 844, unique := ![668], roleBins := ![![0, 668, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) := by
          apply extCounts
          · decide +kernel
          · apply funext; decide +kernel
          · apply funext; decide +kernel
        have block6 : ([((fun x : Bool => x), (fun x : Bool => !x), false, false), ((fun x : Bool => x), (fun x : Bool => !x), false, true), ((fun x : Bool => x), (fun x : Bool => !x), true, false), ((fun x : Bool => x), (fun x : Bool => !x), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State).foldl step ({ full := 844, unique := ![668], roleBins := ![![0, 668, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) = ({ full := 968, unique := ![796], roleBins := ![![0, 796, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) := by
          apply extCounts
          · decide +kernel
          · apply funext; decide +kernel
          · apply funext; decide +kernel
        have block7 : ([((fun x : Bool => x), (fun _ : Bool => true), false, false), ((fun x : Bool => x), (fun _ : Bool => true), false, true), ((fun x : Bool => x), (fun _ : Bool => true), true, false), ((fun x : Bool => x), (fun _ : Bool => true), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State).foldl step ({ full := 968, unique := ![796], roleBins := ![![0, 796, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) = ({ full := 1092, unique := ![924], roleBins := ![![0, 924, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) := by
          apply extCounts
          · decide +kernel
          · apply funext; decide +kernel
          · apply funext; decide +kernel
        have block8 : ([((fun x : Bool => !x), (fun _ : Bool => false), false, false), ((fun x : Bool => !x), (fun _ : Bool => false), false, true), ((fun x : Bool => !x), (fun _ : Bool => false), true, false), ((fun x : Bool => !x), (fun _ : Bool => false), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State).foldl step ({ full := 1092, unique := ![924], roleBins := ![![0, 924, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) = ({ full := 1216, unique := ![1052], roleBins := ![![0, 1052, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) := by
          apply extCounts
          · decide +kernel
          · apply funext; decide +kernel
          · apply funext; decide +kernel
        have block9 : ([((fun x : Bool => !x), (fun x : Bool => x), false, false), ((fun x : Bool => !x), (fun x : Bool => x), false, true), ((fun x : Bool => !x), (fun x : Bool => x), true, false), ((fun x : Bool => !x), (fun x : Bool => x), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State).foldl step ({ full := 1216, unique := ![1052], roleBins := ![![0, 1052, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) = ({ full := 1340, unique := ![1180], roleBins := ![![0, 1180, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) := by
          apply extCounts
          · decide +kernel
          · apply funext; decide +kernel
          · apply funext; decide +kernel
        have block10 : ([((fun x : Bool => !x), (fun x : Bool => !x), false, false), ((fun x : Bool => !x), (fun x : Bool => !x), false, true), ((fun x : Bool => !x), (fun x : Bool => !x), true, false), ((fun x : Bool => !x), (fun x : Bool => !x), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State).foldl step ({ full := 1340, unique := ![1180], roleBins := ![![0, 1180, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) = ({ full := 1504, unique := ![1268], roleBins := ![![0, 1268, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) := by
          apply extCounts
          · decide +kernel
          · apply funext; decide +kernel
          · apply funext; decide +kernel
        have block11 : ([((fun x : Bool => !x), (fun _ : Bool => true), false, false), ((fun x : Bool => !x), (fun _ : Bool => true), false, true), ((fun x : Bool => !x), (fun _ : Bool => true), true, false), ((fun x : Bool => !x), (fun _ : Bool => true), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State).foldl step ({ full := 1504, unique := ![1268], roleBins := ![![0, 1268, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) = ({ full := 1628, unique := ![1396], roleBins := ![![0, 1396, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) := by
          apply extCounts
          · decide +kernel
          · apply funext; decide +kernel
          · apply funext; decide +kernel
        have block12 : ([((fun _ : Bool => true), (fun _ : Bool => false), false, false), ((fun _ : Bool => true), (fun _ : Bool => false), false, true), ((fun _ : Bool => true), (fun _ : Bool => false), true, false), ((fun _ : Bool => true), (fun _ : Bool => false), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State).foldl step ({ full := 1628, unique := ![1396], roleBins := ![![0, 1396, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) = ({ full := 1772, unique := ![1504], roleBins := ![![0, 1504, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) := by
          apply extCounts
          · decide +kernel
          · apply funext; decide +kernel
          · apply funext; decide +kernel
        have block13 : ([((fun _ : Bool => true), (fun x : Bool => x), false, false), ((fun _ : Bool => true), (fun x : Bool => x), false, true), ((fun _ : Bool => true), (fun x : Bool => x), true, false), ((fun _ : Bool => true), (fun x : Bool => x), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State).foldl step ({ full := 1772, unique := ![1504], roleBins := ![![0, 1504, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) = ({ full := 1896, unique := ![1632], roleBins := ![![0, 1632, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) := by
          apply extCounts
          · decide +kernel
          · apply funext; decide +kernel
          · apply funext; decide +kernel
        have block14 : ([((fun _ : Bool => true), (fun x : Bool => !x), false, false), ((fun _ : Bool => true), (fun x : Bool => !x), false, true), ((fun _ : Bool => true), (fun x : Bool => !x), true, false), ((fun _ : Bool => true), (fun x : Bool => !x), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State).foldl step ({ full := 1896, unique := ![1632], roleBins := ![![0, 1632, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) = ({ full := 2020, unique := ![1760], roleBins := ![![0, 1760, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) := by
          apply extCounts
          · decide +kernel
          · apply funext; decide +kernel
          · apply funext; decide +kernel
        have block15 : ([((fun _ : Bool => true), (fun _ : Bool => true), false, false), ((fun _ : Bool => true), (fun _ : Bool => true), false, true), ((fun _ : Bool => true), (fun _ : Bool => true), true, false), ((fun _ : Bool => true), (fun _ : Bool => true), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State).foldl step ({ full := 2020, unique := ![1760], roleBins := ![![0, 1760, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) = ({ full := 2184, unique := ![1848], roleBins := ![![0, 1848, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) := by
          apply extCounts
          · decide +kernel
          · apply funext; decide +kernel
          · apply funext; decide +kernel
        have computed : catalog.fusedCounts states indices = ({ full := 2184, unique := ![1848], roleBins := ![![0, 1848, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) := by
          change (([((fun _ : Bool => false), (fun _ : Bool => false), false, false), ((fun _ : Bool => false), (fun _ : Bool => false), false, true), ((fun _ : Bool => false), (fun _ : Bool => false), true, false), ((fun _ : Bool => false), (fun _ : Bool => false), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State) ++ ([((fun _ : Bool => false), (fun x : Bool => x), false, false), ((fun _ : Bool => false), (fun x : Bool => x), false, true), ((fun _ : Bool => false), (fun x : Bool => x), true, false), ((fun _ : Bool => false), (fun x : Bool => x), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State) ++ ([((fun _ : Bool => false), (fun x : Bool => !x), false, false), ((fun _ : Bool => false), (fun x : Bool => !x), false, true), ((fun _ : Bool => false), (fun x : Bool => !x), true, false), ((fun _ : Bool => false), (fun x : Bool => !x), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State) ++ ([((fun _ : Bool => false), (fun _ : Bool => true), false, false), ((fun _ : Bool => false), (fun _ : Bool => true), false, true), ((fun _ : Bool => false), (fun _ : Bool => true), true, false), ((fun _ : Bool => false), (fun _ : Bool => true), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State) ++ ([((fun x : Bool => x), (fun _ : Bool => false), false, false), ((fun x : Bool => x), (fun _ : Bool => false), false, true), ((fun x : Bool => x), (fun _ : Bool => false), true, false), ((fun x : Bool => x), (fun _ : Bool => false), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State) ++ ([((fun x : Bool => x), (fun x : Bool => x), false, false), ((fun x : Bool => x), (fun x : Bool => x), false, true), ((fun x : Bool => x), (fun x : Bool => x), true, false), ((fun x : Bool => x), (fun x : Bool => x), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State) ++ ([((fun x : Bool => x), (fun x : Bool => !x), false, false), ((fun x : Bool => x), (fun x : Bool => !x), false, true), ((fun x : Bool => x), (fun x : Bool => !x), true, false), ((fun x : Bool => x), (fun x : Bool => !x), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State) ++ ([((fun x : Bool => x), (fun _ : Bool => true), false, false), ((fun x : Bool => x), (fun _ : Bool => true), false, true), ((fun x : Bool => x), (fun _ : Bool => true), true, false), ((fun x : Bool => x), (fun _ : Bool => true), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State) ++ ([((fun x : Bool => !x), (fun _ : Bool => false), false, false), ((fun x : Bool => !x), (fun _ : Bool => false), false, true), ((fun x : Bool => !x), (fun _ : Bool => false), true, false), ((fun x : Bool => !x), (fun _ : Bool => false), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State) ++ ([((fun x : Bool => !x), (fun x : Bool => x), false, false), ((fun x : Bool => !x), (fun x : Bool => x), false, true), ((fun x : Bool => !x), (fun x : Bool => x), true, false), ((fun x : Bool => !x), (fun x : Bool => x), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State) ++ ([((fun x : Bool => !x), (fun x : Bool => !x), false, false), ((fun x : Bool => !x), (fun x : Bool => !x), false, true), ((fun x : Bool => !x), (fun x : Bool => !x), true, false), ((fun x : Bool => !x), (fun x : Bool => !x), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State) ++ ([((fun x : Bool => !x), (fun _ : Bool => true), false, false), ((fun x : Bool => !x), (fun _ : Bool => true), false, true), ((fun x : Bool => !x), (fun _ : Bool => true), true, false), ((fun x : Bool => !x), (fun _ : Bool => true), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State) ++ ([((fun _ : Bool => true), (fun _ : Bool => false), false, false), ((fun _ : Bool => true), (fun _ : Bool => false), false, true), ((fun _ : Bool => true), (fun _ : Bool => false), true, false), ((fun _ : Bool => true), (fun _ : Bool => false), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State) ++ ([((fun _ : Bool => true), (fun x : Bool => x), false, false), ((fun _ : Bool => true), (fun x : Bool => x), false, true), ((fun _ : Bool => true), (fun x : Bool => x), true, false), ((fun _ : Bool => true), (fun x : Bool => x), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State) ++ ([((fun _ : Bool => true), (fun x : Bool => !x), false, false), ((fun _ : Bool => true), (fun x : Bool => !x), false, true), ((fun _ : Bool => true), (fun x : Bool => !x), true, false), ((fun _ : Bool => true), (fun x : Bool => !x), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State) ++ ([((fun _ : Bool => true), (fun _ : Bool => true), false, false), ((fun _ : Bool => true), (fun _ : Bool => true), false, true), ((fun _ : Bool => true), (fun _ : Bool => true), true, false), ((fun _ : Bool => true), (fun _ : Bool => true), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State)).foldl step _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts.zero = _
          simp only [List.foldl_append, block0, block1, block2, block3, block4, block5, block6, block7, block8, block9, block10, block11, block12, block13, block14, block15]
        exact (catalog.fusedFull_eq_escapeNumerator states indices).symm.trans (congrArg (fun c => c.full) computed)
      rows := by
        let states : _root_.D5.S3.ConceptDynamics.InformationEscape.Arena.StateEnumeration (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena := ⟨(([(fun _ : Bool => false), (fun x : Bool => x), (fun x : Bool => !x), (fun _ : Bool => true)]).flatMap fun f => ([(fun _ : Bool => false), (fun x : Bool => x), (fun x : Bool => !x), (fun _ : Bool => true)]).flatMap fun g => [false, true].flatMap fun a => [false, true].map fun b => (f, g, a, b) : List ((Bool → Bool) × (Bool → Bool) × Bool × Bool)), (by change (([(fun _ : Bool => false), (fun x : Bool => x), (fun x : Bool => !x), (fun _ : Bool => true)]).flatMap fun f => ([(fun _ : Bool => false), (fun x : Bool => x), (fun x : Bool => !x), (fun _ : Bool => true)]).flatMap fun g => [false, true].flatMap fun a => [false, true].map fun b => (f, g, a, b) : List ((Bool → Bool) × (Bool → Bool) × Bool × Bool)).Nodup; decide +kernel), (by change (([(fun _ : Bool => false), (fun x : Bool => x), (fun x : Bool => !x), (fun _ : Bool => true)]).flatMap fun f => ([(fun _ : Bool => false), (fun x : Bool => x), (fun x : Bool => !x), (fun _ : Bool => true)]).flatMap fun g => [false, true].flatMap fun a => [false, true].map fun b => (f, g, a, b) : List ((Bool → Bool) × (Bool → Bool) × Bool × Bool)).toFinset = (Finset.univ : Finset ((Bool → Bool) × (Bool → Bool) × Bool × Bool)); decide +kernel)⟩
        let catalog := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionRealization)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.Communication.MutualRecognitionIsJointRealizability.mutual_recognition_does_not_require_equal_concepts) }]
        let indices := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.finIndexEnumeration 1
        let allStates : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State := [((fun _ : Bool => false), (fun _ : Bool => false), false, false), ((fun _ : Bool => false), (fun _ : Bool => false), false, true), ((fun _ : Bool => false), (fun _ : Bool => false), true, false), ((fun _ : Bool => false), (fun _ : Bool => false), true, true), ((fun _ : Bool => false), (fun x : Bool => x), false, false), ((fun _ : Bool => false), (fun x : Bool => x), false, true), ((fun _ : Bool => false), (fun x : Bool => x), true, false), ((fun _ : Bool => false), (fun x : Bool => x), true, true), ((fun _ : Bool => false), (fun x : Bool => !x), false, false), ((fun _ : Bool => false), (fun x : Bool => !x), false, true), ((fun _ : Bool => false), (fun x : Bool => !x), true, false), ((fun _ : Bool => false), (fun x : Bool => !x), true, true), ((fun _ : Bool => false), (fun _ : Bool => true), false, false), ((fun _ : Bool => false), (fun _ : Bool => true), false, true), ((fun _ : Bool => false), (fun _ : Bool => true), true, false), ((fun _ : Bool => false), (fun _ : Bool => true), true, true), ((fun x : Bool => x), (fun _ : Bool => false), false, false), ((fun x : Bool => x), (fun _ : Bool => false), false, true), ((fun x : Bool => x), (fun _ : Bool => false), true, false), ((fun x : Bool => x), (fun _ : Bool => false), true, true), ((fun x : Bool => x), (fun x : Bool => x), false, false), ((fun x : Bool => x), (fun x : Bool => x), false, true), ((fun x : Bool => x), (fun x : Bool => x), true, false), ((fun x : Bool => x), (fun x : Bool => x), true, true), ((fun x : Bool => x), (fun x : Bool => !x), false, false), ((fun x : Bool => x), (fun x : Bool => !x), false, true), ((fun x : Bool => x), (fun x : Bool => !x), true, false), ((fun x : Bool => x), (fun x : Bool => !x), true, true), ((fun x : Bool => x), (fun _ : Bool => true), false, false), ((fun x : Bool => x), (fun _ : Bool => true), false, true), ((fun x : Bool => x), (fun _ : Bool => true), true, false), ((fun x : Bool => x), (fun _ : Bool => true), true, true), ((fun x : Bool => !x), (fun _ : Bool => false), false, false), ((fun x : Bool => !x), (fun _ : Bool => false), false, true), ((fun x : Bool => !x), (fun _ : Bool => false), true, false), ((fun x : Bool => !x), (fun _ : Bool => false), true, true), ((fun x : Bool => !x), (fun x : Bool => x), false, false), ((fun x : Bool => !x), (fun x : Bool => x), false, true), ((fun x : Bool => !x), (fun x : Bool => x), true, false), ((fun x : Bool => !x), (fun x : Bool => x), true, true), ((fun x : Bool => !x), (fun x : Bool => !x), false, false), ((fun x : Bool => !x), (fun x : Bool => !x), false, true), ((fun x : Bool => !x), (fun x : Bool => !x), true, false), ((fun x : Bool => !x), (fun x : Bool => !x), true, true), ((fun x : Bool => !x), (fun _ : Bool => true), false, false), ((fun x : Bool => !x), (fun _ : Bool => true), false, true), ((fun x : Bool => !x), (fun _ : Bool => true), true, false), ((fun x : Bool => !x), (fun _ : Bool => true), true, true), ((fun _ : Bool => true), (fun _ : Bool => false), false, false), ((fun _ : Bool => true), (fun _ : Bool => false), false, true), ((fun _ : Bool => true), (fun _ : Bool => false), true, false), ((fun _ : Bool => true), (fun _ : Bool => false), true, true), ((fun _ : Bool => true), (fun x : Bool => x), false, false), ((fun _ : Bool => true), (fun x : Bool => x), false, true), ((fun _ : Bool => true), (fun x : Bool => x), true, false), ((fun _ : Bool => true), (fun x : Bool => x), true, true), ((fun _ : Bool => true), (fun x : Bool => !x), false, false), ((fun _ : Bool => true), (fun x : Bool => !x), false, true), ((fun _ : Bool => true), (fun x : Bool => !x), true, false), ((fun _ : Bool => true), (fun x : Bool => !x), true, true), ((fun _ : Bool => true), (fun _ : Bool => true), false, false), ((fun _ : Bool => true), (fun _ : Bool => true), false, true), ((fun _ : Bool => true), (fun _ : Bool => true), true, false), ((fun _ : Bool => true), (fun _ : Bool => true), true, true)]
        let step := fun (counts : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) left =>
          allStates.foldl (fun counts right => catalog.pairStep indices counts left right) counts
        have extCounts (a b : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1))
            (hf : a.full = b.full) (hu : a.unique = b.unique) (hr : a.roleBins = b.roleBins) : a = b := by
          cases a; cases b; cases hf; cases hu; cases hr; rfl
        have block0 : ([((fun _ : Bool => false), (fun _ : Bool => false), false, false), ((fun _ : Bool => false), (fun _ : Bool => false), false, true), ((fun _ : Bool => false), (fun _ : Bool => false), true, false), ((fun _ : Bool => false), (fun _ : Bool => false), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State).foldl step _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts.zero = ({ full := 164, unique := ![88], roleBins := ![![0, 88, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) := by
          apply extCounts
          · decide +kernel
          · apply funext; decide +kernel
          · apply funext; decide +kernel
        have block1 : ([((fun _ : Bool => false), (fun x : Bool => x), false, false), ((fun _ : Bool => false), (fun x : Bool => x), false, true), ((fun _ : Bool => false), (fun x : Bool => x), true, false), ((fun _ : Bool => false), (fun x : Bool => x), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State).foldl step ({ full := 164, unique := ![88], roleBins := ![![0, 88, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) = ({ full := 288, unique := ![216], roleBins := ![![0, 216, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) := by
          apply extCounts
          · decide +kernel
          · apply funext; decide +kernel
          · apply funext; decide +kernel
        have block2 : ([((fun _ : Bool => false), (fun x : Bool => !x), false, false), ((fun _ : Bool => false), (fun x : Bool => !x), false, true), ((fun _ : Bool => false), (fun x : Bool => !x), true, false), ((fun _ : Bool => false), (fun x : Bool => !x), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State).foldl step ({ full := 288, unique := ![216], roleBins := ![![0, 216, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) = ({ full := 412, unique := ![344], roleBins := ![![0, 344, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) := by
          apply extCounts
          · decide +kernel
          · apply funext; decide +kernel
          · apply funext; decide +kernel
        have block3 : ([((fun _ : Bool => false), (fun _ : Bool => true), false, false), ((fun _ : Bool => false), (fun _ : Bool => true), false, true), ((fun _ : Bool => false), (fun _ : Bool => true), true, false), ((fun _ : Bool => false), (fun _ : Bool => true), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State).foldl step ({ full := 412, unique := ![344], roleBins := ![![0, 344, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) = ({ full := 556, unique := ![452], roleBins := ![![0, 452, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) := by
          apply extCounts
          · decide +kernel
          · apply funext; decide +kernel
          · apply funext; decide +kernel
        have block4 : ([((fun x : Bool => x), (fun _ : Bool => false), false, false), ((fun x : Bool => x), (fun _ : Bool => false), false, true), ((fun x : Bool => x), (fun _ : Bool => false), true, false), ((fun x : Bool => x), (fun _ : Bool => false), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State).foldl step ({ full := 556, unique := ![452], roleBins := ![![0, 452, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) = ({ full := 680, unique := ![580], roleBins := ![![0, 580, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) := by
          apply extCounts
          · decide +kernel
          · apply funext; decide +kernel
          · apply funext; decide +kernel
        have block5 : ([((fun x : Bool => x), (fun x : Bool => x), false, false), ((fun x : Bool => x), (fun x : Bool => x), false, true), ((fun x : Bool => x), (fun x : Bool => x), true, false), ((fun x : Bool => x), (fun x : Bool => x), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State).foldl step ({ full := 680, unique := ![580], roleBins := ![![0, 580, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) = ({ full := 844, unique := ![668], roleBins := ![![0, 668, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) := by
          apply extCounts
          · decide +kernel
          · apply funext; decide +kernel
          · apply funext; decide +kernel
        have block6 : ([((fun x : Bool => x), (fun x : Bool => !x), false, false), ((fun x : Bool => x), (fun x : Bool => !x), false, true), ((fun x : Bool => x), (fun x : Bool => !x), true, false), ((fun x : Bool => x), (fun x : Bool => !x), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State).foldl step ({ full := 844, unique := ![668], roleBins := ![![0, 668, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) = ({ full := 968, unique := ![796], roleBins := ![![0, 796, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) := by
          apply extCounts
          · decide +kernel
          · apply funext; decide +kernel
          · apply funext; decide +kernel
        have block7 : ([((fun x : Bool => x), (fun _ : Bool => true), false, false), ((fun x : Bool => x), (fun _ : Bool => true), false, true), ((fun x : Bool => x), (fun _ : Bool => true), true, false), ((fun x : Bool => x), (fun _ : Bool => true), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State).foldl step ({ full := 968, unique := ![796], roleBins := ![![0, 796, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) = ({ full := 1092, unique := ![924], roleBins := ![![0, 924, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) := by
          apply extCounts
          · decide +kernel
          · apply funext; decide +kernel
          · apply funext; decide +kernel
        have block8 : ([((fun x : Bool => !x), (fun _ : Bool => false), false, false), ((fun x : Bool => !x), (fun _ : Bool => false), false, true), ((fun x : Bool => !x), (fun _ : Bool => false), true, false), ((fun x : Bool => !x), (fun _ : Bool => false), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State).foldl step ({ full := 1092, unique := ![924], roleBins := ![![0, 924, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) = ({ full := 1216, unique := ![1052], roleBins := ![![0, 1052, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) := by
          apply extCounts
          · decide +kernel
          · apply funext; decide +kernel
          · apply funext; decide +kernel
        have block9 : ([((fun x : Bool => !x), (fun x : Bool => x), false, false), ((fun x : Bool => !x), (fun x : Bool => x), false, true), ((fun x : Bool => !x), (fun x : Bool => x), true, false), ((fun x : Bool => !x), (fun x : Bool => x), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State).foldl step ({ full := 1216, unique := ![1052], roleBins := ![![0, 1052, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) = ({ full := 1340, unique := ![1180], roleBins := ![![0, 1180, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) := by
          apply extCounts
          · decide +kernel
          · apply funext; decide +kernel
          · apply funext; decide +kernel
        have block10 : ([((fun x : Bool => !x), (fun x : Bool => !x), false, false), ((fun x : Bool => !x), (fun x : Bool => !x), false, true), ((fun x : Bool => !x), (fun x : Bool => !x), true, false), ((fun x : Bool => !x), (fun x : Bool => !x), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State).foldl step ({ full := 1340, unique := ![1180], roleBins := ![![0, 1180, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) = ({ full := 1504, unique := ![1268], roleBins := ![![0, 1268, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) := by
          apply extCounts
          · decide +kernel
          · apply funext; decide +kernel
          · apply funext; decide +kernel
        have block11 : ([((fun x : Bool => !x), (fun _ : Bool => true), false, false), ((fun x : Bool => !x), (fun _ : Bool => true), false, true), ((fun x : Bool => !x), (fun _ : Bool => true), true, false), ((fun x : Bool => !x), (fun _ : Bool => true), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State).foldl step ({ full := 1504, unique := ![1268], roleBins := ![![0, 1268, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) = ({ full := 1628, unique := ![1396], roleBins := ![![0, 1396, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) := by
          apply extCounts
          · decide +kernel
          · apply funext; decide +kernel
          · apply funext; decide +kernel
        have block12 : ([((fun _ : Bool => true), (fun _ : Bool => false), false, false), ((fun _ : Bool => true), (fun _ : Bool => false), false, true), ((fun _ : Bool => true), (fun _ : Bool => false), true, false), ((fun _ : Bool => true), (fun _ : Bool => false), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State).foldl step ({ full := 1628, unique := ![1396], roleBins := ![![0, 1396, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) = ({ full := 1772, unique := ![1504], roleBins := ![![0, 1504, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) := by
          apply extCounts
          · decide +kernel
          · apply funext; decide +kernel
          · apply funext; decide +kernel
        have block13 : ([((fun _ : Bool => true), (fun x : Bool => x), false, false), ((fun _ : Bool => true), (fun x : Bool => x), false, true), ((fun _ : Bool => true), (fun x : Bool => x), true, false), ((fun _ : Bool => true), (fun x : Bool => x), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State).foldl step ({ full := 1772, unique := ![1504], roleBins := ![![0, 1504, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) = ({ full := 1896, unique := ![1632], roleBins := ![![0, 1632, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) := by
          apply extCounts
          · decide +kernel
          · apply funext; decide +kernel
          · apply funext; decide +kernel
        have block14 : ([((fun _ : Bool => true), (fun x : Bool => !x), false, false), ((fun _ : Bool => true), (fun x : Bool => !x), false, true), ((fun _ : Bool => true), (fun x : Bool => !x), true, false), ((fun _ : Bool => true), (fun x : Bool => !x), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State).foldl step ({ full := 1896, unique := ![1632], roleBins := ![![0, 1632, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) = ({ full := 2020, unique := ![1760], roleBins := ![![0, 1760, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) := by
          apply extCounts
          · decide +kernel
          · apply funext; decide +kernel
          · apply funext; decide +kernel
        have block15 : ([((fun _ : Bool => true), (fun _ : Bool => true), false, false), ((fun _ : Bool => true), (fun _ : Bool => true), false, true), ((fun _ : Bool => true), (fun _ : Bool => true), true, false), ((fun _ : Bool => true), (fun _ : Bool => true), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State).foldl step ({ full := 2020, unique := ![1760], roleBins := ![![0, 1760, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) = ({ full := 2184, unique := ![1848], roleBins := ![![0, 1848, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) := by
          apply extCounts
          · decide +kernel
          · apply funext; decide +kernel
          · apply funext; decide +kernel
        have computed : catalog.fusedCounts states indices = ({ full := 2184, unique := ![1848], roleBins := ![![0, 1848, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) := by
          change (([((fun _ : Bool => false), (fun _ : Bool => false), false, false), ((fun _ : Bool => false), (fun _ : Bool => false), false, true), ((fun _ : Bool => false), (fun _ : Bool => false), true, false), ((fun _ : Bool => false), (fun _ : Bool => false), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State) ++ ([((fun _ : Bool => false), (fun x : Bool => x), false, false), ((fun _ : Bool => false), (fun x : Bool => x), false, true), ((fun _ : Bool => false), (fun x : Bool => x), true, false), ((fun _ : Bool => false), (fun x : Bool => x), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State) ++ ([((fun _ : Bool => false), (fun x : Bool => !x), false, false), ((fun _ : Bool => false), (fun x : Bool => !x), false, true), ((fun _ : Bool => false), (fun x : Bool => !x), true, false), ((fun _ : Bool => false), (fun x : Bool => !x), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State) ++ ([((fun _ : Bool => false), (fun _ : Bool => true), false, false), ((fun _ : Bool => false), (fun _ : Bool => true), false, true), ((fun _ : Bool => false), (fun _ : Bool => true), true, false), ((fun _ : Bool => false), (fun _ : Bool => true), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State) ++ ([((fun x : Bool => x), (fun _ : Bool => false), false, false), ((fun x : Bool => x), (fun _ : Bool => false), false, true), ((fun x : Bool => x), (fun _ : Bool => false), true, false), ((fun x : Bool => x), (fun _ : Bool => false), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State) ++ ([((fun x : Bool => x), (fun x : Bool => x), false, false), ((fun x : Bool => x), (fun x : Bool => x), false, true), ((fun x : Bool => x), (fun x : Bool => x), true, false), ((fun x : Bool => x), (fun x : Bool => x), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State) ++ ([((fun x : Bool => x), (fun x : Bool => !x), false, false), ((fun x : Bool => x), (fun x : Bool => !x), false, true), ((fun x : Bool => x), (fun x : Bool => !x), true, false), ((fun x : Bool => x), (fun x : Bool => !x), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State) ++ ([((fun x : Bool => x), (fun _ : Bool => true), false, false), ((fun x : Bool => x), (fun _ : Bool => true), false, true), ((fun x : Bool => x), (fun _ : Bool => true), true, false), ((fun x : Bool => x), (fun _ : Bool => true), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State) ++ ([((fun x : Bool => !x), (fun _ : Bool => false), false, false), ((fun x : Bool => !x), (fun _ : Bool => false), false, true), ((fun x : Bool => !x), (fun _ : Bool => false), true, false), ((fun x : Bool => !x), (fun _ : Bool => false), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State) ++ ([((fun x : Bool => !x), (fun x : Bool => x), false, false), ((fun x : Bool => !x), (fun x : Bool => x), false, true), ((fun x : Bool => !x), (fun x : Bool => x), true, false), ((fun x : Bool => !x), (fun x : Bool => x), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State) ++ ([((fun x : Bool => !x), (fun x : Bool => !x), false, false), ((fun x : Bool => !x), (fun x : Bool => !x), false, true), ((fun x : Bool => !x), (fun x : Bool => !x), true, false), ((fun x : Bool => !x), (fun x : Bool => !x), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State) ++ ([((fun x : Bool => !x), (fun _ : Bool => true), false, false), ((fun x : Bool => !x), (fun _ : Bool => true), false, true), ((fun x : Bool => !x), (fun _ : Bool => true), true, false), ((fun x : Bool => !x), (fun _ : Bool => true), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State) ++ ([((fun _ : Bool => true), (fun _ : Bool => false), false, false), ((fun _ : Bool => true), (fun _ : Bool => false), false, true), ((fun _ : Bool => true), (fun _ : Bool => false), true, false), ((fun _ : Bool => true), (fun _ : Bool => false), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State) ++ ([((fun _ : Bool => true), (fun x : Bool => x), false, false), ((fun _ : Bool => true), (fun x : Bool => x), false, true), ((fun _ : Bool => true), (fun x : Bool => x), true, false), ((fun _ : Bool => true), (fun x : Bool => x), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State) ++ ([((fun _ : Bool => true), (fun x : Bool => !x), false, false), ((fun _ : Bool => true), (fun x : Bool => !x), false, true), ((fun _ : Bool => true), (fun x : Bool => !x), true, false), ((fun _ : Bool => true), (fun x : Bool => !x), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State) ++ ([((fun _ : Bool => true), (fun _ : Bool => true), false, false), ((fun _ : Bool => true), (fun _ : Bool => true), false, true), ((fun _ : Bool => true), (fun _ : Bool => true), true, false), ((fun _ : Bool => true), (fun _ : Bool => true), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State)).foldl step _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts.zero = _
          simp only [List.foldl_append, block0, block1, block2, block3, block4, block5, block6, block7, block8, block9, block10, block11, block12, block13, block14, block15]
        have uniqueEq := (catalog.fusedUnique_eq_uniqueCaptureCount states indices (0 : Fin 1)).symm.trans (congrFun (congrArg (fun c => c.unique) computed) 0)
        have lowering := (catalog.lowersEscape_iff_uniqueCaptureCount_pos 0 (by decide +kernel)).mpr (by rw [uniqueEq]; decide)
        exact Fin.cases
          ({ unique := 1848
             uniqueEq := uniqueEq
             without := 4032
             withoutEq := (catalog.fusedWithout_eq_escapeNumerator_without states indices 0).symm.trans (congrArg (fun c => c.without 0) computed)
             roleBins := ![0, 1848, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
             roleEq := fun bucket => (catalog.fusedRoleBins_eq_roleHistogram states indices 0 bucket).symm.trans (congrFun (congrFun (congrArg (fun c => c.roleBins) computed) 0) bucket)
             roleTotal := by decide +kernel
             conclusion := .positive (by decide +kernel) lowering } : Contract.SealRow catalog 0)
          (fun i => Fin.elim0 i)
      collisions := #[]
      conclusion := .irredundant (by
        let states : _root_.D5.S3.ConceptDynamics.InformationEscape.Arena.StateEnumeration (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena := ⟨(([(fun _ : Bool => false), (fun x : Bool => x), (fun x : Bool => !x), (fun _ : Bool => true)]).flatMap fun f => ([(fun _ : Bool => false), (fun x : Bool => x), (fun x : Bool => !x), (fun _ : Bool => true)]).flatMap fun g => [false, true].flatMap fun a => [false, true].map fun b => (f, g, a, b) : List ((Bool → Bool) × (Bool → Bool) × Bool × Bool)), (by change (([(fun _ : Bool => false), (fun x : Bool => x), (fun x : Bool => !x), (fun _ : Bool => true)]).flatMap fun f => ([(fun _ : Bool => false), (fun x : Bool => x), (fun x : Bool => !x), (fun _ : Bool => true)]).flatMap fun g => [false, true].flatMap fun a => [false, true].map fun b => (f, g, a, b) : List ((Bool → Bool) × (Bool → Bool) × Bool × Bool)).Nodup; decide +kernel), (by change (([(fun _ : Bool => false), (fun x : Bool => x), (fun x : Bool => !x), (fun _ : Bool => true)]).flatMap fun f => ([(fun _ : Bool => false), (fun x : Bool => x), (fun x : Bool => !x), (fun _ : Bool => true)]).flatMap fun g => [false, true].flatMap fun a => [false, true].map fun b => (f, g, a, b) : List ((Bool → Bool) × (Bool → Bool) × Bool × Bool)).toFinset = (Finset.univ : Finset ((Bool → Bool) × (Bool → Bool) × Bool × Bool)); decide +kernel)⟩
        let catalog := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionRealization)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.Communication.MutualRecognitionIsJointRealizability.mutual_recognition_does_not_require_equal_concepts) }]
        let indices := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.finIndexEnumeration 1
        let allStates : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State := [((fun _ : Bool => false), (fun _ : Bool => false), false, false), ((fun _ : Bool => false), (fun _ : Bool => false), false, true), ((fun _ : Bool => false), (fun _ : Bool => false), true, false), ((fun _ : Bool => false), (fun _ : Bool => false), true, true), ((fun _ : Bool => false), (fun x : Bool => x), false, false), ((fun _ : Bool => false), (fun x : Bool => x), false, true), ((fun _ : Bool => false), (fun x : Bool => x), true, false), ((fun _ : Bool => false), (fun x : Bool => x), true, true), ((fun _ : Bool => false), (fun x : Bool => !x), false, false), ((fun _ : Bool => false), (fun x : Bool => !x), false, true), ((fun _ : Bool => false), (fun x : Bool => !x), true, false), ((fun _ : Bool => false), (fun x : Bool => !x), true, true), ((fun _ : Bool => false), (fun _ : Bool => true), false, false), ((fun _ : Bool => false), (fun _ : Bool => true), false, true), ((fun _ : Bool => false), (fun _ : Bool => true), true, false), ((fun _ : Bool => false), (fun _ : Bool => true), true, true), ((fun x : Bool => x), (fun _ : Bool => false), false, false), ((fun x : Bool => x), (fun _ : Bool => false), false, true), ((fun x : Bool => x), (fun _ : Bool => false), true, false), ((fun x : Bool => x), (fun _ : Bool => false), true, true), ((fun x : Bool => x), (fun x : Bool => x), false, false), ((fun x : Bool => x), (fun x : Bool => x), false, true), ((fun x : Bool => x), (fun x : Bool => x), true, false), ((fun x : Bool => x), (fun x : Bool => x), true, true), ((fun x : Bool => x), (fun x : Bool => !x), false, false), ((fun x : Bool => x), (fun x : Bool => !x), false, true), ((fun x : Bool => x), (fun x : Bool => !x), true, false), ((fun x : Bool => x), (fun x : Bool => !x), true, true), ((fun x : Bool => x), (fun _ : Bool => true), false, false), ((fun x : Bool => x), (fun _ : Bool => true), false, true), ((fun x : Bool => x), (fun _ : Bool => true), true, false), ((fun x : Bool => x), (fun _ : Bool => true), true, true), ((fun x : Bool => !x), (fun _ : Bool => false), false, false), ((fun x : Bool => !x), (fun _ : Bool => false), false, true), ((fun x : Bool => !x), (fun _ : Bool => false), true, false), ((fun x : Bool => !x), (fun _ : Bool => false), true, true), ((fun x : Bool => !x), (fun x : Bool => x), false, false), ((fun x : Bool => !x), (fun x : Bool => x), false, true), ((fun x : Bool => !x), (fun x : Bool => x), true, false), ((fun x : Bool => !x), (fun x : Bool => x), true, true), ((fun x : Bool => !x), (fun x : Bool => !x), false, false), ((fun x : Bool => !x), (fun x : Bool => !x), false, true), ((fun x : Bool => !x), (fun x : Bool => !x), true, false), ((fun x : Bool => !x), (fun x : Bool => !x), true, true), ((fun x : Bool => !x), (fun _ : Bool => true), false, false), ((fun x : Bool => !x), (fun _ : Bool => true), false, true), ((fun x : Bool => !x), (fun _ : Bool => true), true, false), ((fun x : Bool => !x), (fun _ : Bool => true), true, true), ((fun _ : Bool => true), (fun _ : Bool => false), false, false), ((fun _ : Bool => true), (fun _ : Bool => false), false, true), ((fun _ : Bool => true), (fun _ : Bool => false), true, false), ((fun _ : Bool => true), (fun _ : Bool => false), true, true), ((fun _ : Bool => true), (fun x : Bool => x), false, false), ((fun _ : Bool => true), (fun x : Bool => x), false, true), ((fun _ : Bool => true), (fun x : Bool => x), true, false), ((fun _ : Bool => true), (fun x : Bool => x), true, true), ((fun _ : Bool => true), (fun x : Bool => !x), false, false), ((fun _ : Bool => true), (fun x : Bool => !x), false, true), ((fun _ : Bool => true), (fun x : Bool => !x), true, false), ((fun _ : Bool => true), (fun x : Bool => !x), true, true), ((fun _ : Bool => true), (fun _ : Bool => true), false, false), ((fun _ : Bool => true), (fun _ : Bool => true), false, true), ((fun _ : Bool => true), (fun _ : Bool => true), true, false), ((fun _ : Bool => true), (fun _ : Bool => true), true, true)]
        let step := fun (counts : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) left =>
          allStates.foldl (fun counts right => catalog.pairStep indices counts left right) counts
        have extCounts (a b : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1))
            (hf : a.full = b.full) (hu : a.unique = b.unique) (hr : a.roleBins = b.roleBins) : a = b := by
          cases a; cases b; cases hf; cases hu; cases hr; rfl
        have block0 : ([((fun _ : Bool => false), (fun _ : Bool => false), false, false), ((fun _ : Bool => false), (fun _ : Bool => false), false, true), ((fun _ : Bool => false), (fun _ : Bool => false), true, false), ((fun _ : Bool => false), (fun _ : Bool => false), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State).foldl step _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts.zero = ({ full := 164, unique := ![88], roleBins := ![![0, 88, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) := by
          apply extCounts
          · decide +kernel
          · apply funext; decide +kernel
          · apply funext; decide +kernel
        have block1 : ([((fun _ : Bool => false), (fun x : Bool => x), false, false), ((fun _ : Bool => false), (fun x : Bool => x), false, true), ((fun _ : Bool => false), (fun x : Bool => x), true, false), ((fun _ : Bool => false), (fun x : Bool => x), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State).foldl step ({ full := 164, unique := ![88], roleBins := ![![0, 88, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) = ({ full := 288, unique := ![216], roleBins := ![![0, 216, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) := by
          apply extCounts
          · decide +kernel
          · apply funext; decide +kernel
          · apply funext; decide +kernel
        have block2 : ([((fun _ : Bool => false), (fun x : Bool => !x), false, false), ((fun _ : Bool => false), (fun x : Bool => !x), false, true), ((fun _ : Bool => false), (fun x : Bool => !x), true, false), ((fun _ : Bool => false), (fun x : Bool => !x), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State).foldl step ({ full := 288, unique := ![216], roleBins := ![![0, 216, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) = ({ full := 412, unique := ![344], roleBins := ![![0, 344, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) := by
          apply extCounts
          · decide +kernel
          · apply funext; decide +kernel
          · apply funext; decide +kernel
        have block3 : ([((fun _ : Bool => false), (fun _ : Bool => true), false, false), ((fun _ : Bool => false), (fun _ : Bool => true), false, true), ((fun _ : Bool => false), (fun _ : Bool => true), true, false), ((fun _ : Bool => false), (fun _ : Bool => true), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State).foldl step ({ full := 412, unique := ![344], roleBins := ![![0, 344, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) = ({ full := 556, unique := ![452], roleBins := ![![0, 452, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) := by
          apply extCounts
          · decide +kernel
          · apply funext; decide +kernel
          · apply funext; decide +kernel
        have block4 : ([((fun x : Bool => x), (fun _ : Bool => false), false, false), ((fun x : Bool => x), (fun _ : Bool => false), false, true), ((fun x : Bool => x), (fun _ : Bool => false), true, false), ((fun x : Bool => x), (fun _ : Bool => false), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State).foldl step ({ full := 556, unique := ![452], roleBins := ![![0, 452, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) = ({ full := 680, unique := ![580], roleBins := ![![0, 580, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) := by
          apply extCounts
          · decide +kernel
          · apply funext; decide +kernel
          · apply funext; decide +kernel
        have block5 : ([((fun x : Bool => x), (fun x : Bool => x), false, false), ((fun x : Bool => x), (fun x : Bool => x), false, true), ((fun x : Bool => x), (fun x : Bool => x), true, false), ((fun x : Bool => x), (fun x : Bool => x), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State).foldl step ({ full := 680, unique := ![580], roleBins := ![![0, 580, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) = ({ full := 844, unique := ![668], roleBins := ![![0, 668, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) := by
          apply extCounts
          · decide +kernel
          · apply funext; decide +kernel
          · apply funext; decide +kernel
        have block6 : ([((fun x : Bool => x), (fun x : Bool => !x), false, false), ((fun x : Bool => x), (fun x : Bool => !x), false, true), ((fun x : Bool => x), (fun x : Bool => !x), true, false), ((fun x : Bool => x), (fun x : Bool => !x), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State).foldl step ({ full := 844, unique := ![668], roleBins := ![![0, 668, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) = ({ full := 968, unique := ![796], roleBins := ![![0, 796, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) := by
          apply extCounts
          · decide +kernel
          · apply funext; decide +kernel
          · apply funext; decide +kernel
        have block7 : ([((fun x : Bool => x), (fun _ : Bool => true), false, false), ((fun x : Bool => x), (fun _ : Bool => true), false, true), ((fun x : Bool => x), (fun _ : Bool => true), true, false), ((fun x : Bool => x), (fun _ : Bool => true), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State).foldl step ({ full := 968, unique := ![796], roleBins := ![![0, 796, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) = ({ full := 1092, unique := ![924], roleBins := ![![0, 924, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) := by
          apply extCounts
          · decide +kernel
          · apply funext; decide +kernel
          · apply funext; decide +kernel
        have block8 : ([((fun x : Bool => !x), (fun _ : Bool => false), false, false), ((fun x : Bool => !x), (fun _ : Bool => false), false, true), ((fun x : Bool => !x), (fun _ : Bool => false), true, false), ((fun x : Bool => !x), (fun _ : Bool => false), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State).foldl step ({ full := 1092, unique := ![924], roleBins := ![![0, 924, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) = ({ full := 1216, unique := ![1052], roleBins := ![![0, 1052, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) := by
          apply extCounts
          · decide +kernel
          · apply funext; decide +kernel
          · apply funext; decide +kernel
        have block9 : ([((fun x : Bool => !x), (fun x : Bool => x), false, false), ((fun x : Bool => !x), (fun x : Bool => x), false, true), ((fun x : Bool => !x), (fun x : Bool => x), true, false), ((fun x : Bool => !x), (fun x : Bool => x), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State).foldl step ({ full := 1216, unique := ![1052], roleBins := ![![0, 1052, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) = ({ full := 1340, unique := ![1180], roleBins := ![![0, 1180, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) := by
          apply extCounts
          · decide +kernel
          · apply funext; decide +kernel
          · apply funext; decide +kernel
        have block10 : ([((fun x : Bool => !x), (fun x : Bool => !x), false, false), ((fun x : Bool => !x), (fun x : Bool => !x), false, true), ((fun x : Bool => !x), (fun x : Bool => !x), true, false), ((fun x : Bool => !x), (fun x : Bool => !x), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State).foldl step ({ full := 1340, unique := ![1180], roleBins := ![![0, 1180, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) = ({ full := 1504, unique := ![1268], roleBins := ![![0, 1268, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) := by
          apply extCounts
          · decide +kernel
          · apply funext; decide +kernel
          · apply funext; decide +kernel
        have block11 : ([((fun x : Bool => !x), (fun _ : Bool => true), false, false), ((fun x : Bool => !x), (fun _ : Bool => true), false, true), ((fun x : Bool => !x), (fun _ : Bool => true), true, false), ((fun x : Bool => !x), (fun _ : Bool => true), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State).foldl step ({ full := 1504, unique := ![1268], roleBins := ![![0, 1268, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) = ({ full := 1628, unique := ![1396], roleBins := ![![0, 1396, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) := by
          apply extCounts
          · decide +kernel
          · apply funext; decide +kernel
          · apply funext; decide +kernel
        have block12 : ([((fun _ : Bool => true), (fun _ : Bool => false), false, false), ((fun _ : Bool => true), (fun _ : Bool => false), false, true), ((fun _ : Bool => true), (fun _ : Bool => false), true, false), ((fun _ : Bool => true), (fun _ : Bool => false), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State).foldl step ({ full := 1628, unique := ![1396], roleBins := ![![0, 1396, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) = ({ full := 1772, unique := ![1504], roleBins := ![![0, 1504, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) := by
          apply extCounts
          · decide +kernel
          · apply funext; decide +kernel
          · apply funext; decide +kernel
        have block13 : ([((fun _ : Bool => true), (fun x : Bool => x), false, false), ((fun _ : Bool => true), (fun x : Bool => x), false, true), ((fun _ : Bool => true), (fun x : Bool => x), true, false), ((fun _ : Bool => true), (fun x : Bool => x), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State).foldl step ({ full := 1772, unique := ![1504], roleBins := ![![0, 1504, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) = ({ full := 1896, unique := ![1632], roleBins := ![![0, 1632, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) := by
          apply extCounts
          · decide +kernel
          · apply funext; decide +kernel
          · apply funext; decide +kernel
        have block14 : ([((fun _ : Bool => true), (fun x : Bool => !x), false, false), ((fun _ : Bool => true), (fun x : Bool => !x), false, true), ((fun _ : Bool => true), (fun x : Bool => !x), true, false), ((fun _ : Bool => true), (fun x : Bool => !x), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State).foldl step ({ full := 1896, unique := ![1632], roleBins := ![![0, 1632, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) = ({ full := 2020, unique := ![1760], roleBins := ![![0, 1760, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) := by
          apply extCounts
          · decide +kernel
          · apply funext; decide +kernel
          · apply funext; decide +kernel
        have block15 : ([((fun _ : Bool => true), (fun _ : Bool => true), false, false), ((fun _ : Bool => true), (fun _ : Bool => true), false, true), ((fun _ : Bool => true), (fun _ : Bool => true), true, false), ((fun _ : Bool => true), (fun _ : Bool => true), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State).foldl step ({ full := 2020, unique := ![1760], roleBins := ![![0, 1760, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) = ({ full := 2184, unique := ![1848], roleBins := ![![0, 1848, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) := by
          apply extCounts
          · decide +kernel
          · apply funext; decide +kernel
          · apply funext; decide +kernel
        have computed : catalog.fusedCounts states indices = ({ full := 2184, unique := ![1848], roleBins := ![![0, 1848, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 1)) := by
          change (([((fun _ : Bool => false), (fun _ : Bool => false), false, false), ((fun _ : Bool => false), (fun _ : Bool => false), false, true), ((fun _ : Bool => false), (fun _ : Bool => false), true, false), ((fun _ : Bool => false), (fun _ : Bool => false), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State) ++ ([((fun _ : Bool => false), (fun x : Bool => x), false, false), ((fun _ : Bool => false), (fun x : Bool => x), false, true), ((fun _ : Bool => false), (fun x : Bool => x), true, false), ((fun _ : Bool => false), (fun x : Bool => x), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State) ++ ([((fun _ : Bool => false), (fun x : Bool => !x), false, false), ((fun _ : Bool => false), (fun x : Bool => !x), false, true), ((fun _ : Bool => false), (fun x : Bool => !x), true, false), ((fun _ : Bool => false), (fun x : Bool => !x), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State) ++ ([((fun _ : Bool => false), (fun _ : Bool => true), false, false), ((fun _ : Bool => false), (fun _ : Bool => true), false, true), ((fun _ : Bool => false), (fun _ : Bool => true), true, false), ((fun _ : Bool => false), (fun _ : Bool => true), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State) ++ ([((fun x : Bool => x), (fun _ : Bool => false), false, false), ((fun x : Bool => x), (fun _ : Bool => false), false, true), ((fun x : Bool => x), (fun _ : Bool => false), true, false), ((fun x : Bool => x), (fun _ : Bool => false), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State) ++ ([((fun x : Bool => x), (fun x : Bool => x), false, false), ((fun x : Bool => x), (fun x : Bool => x), false, true), ((fun x : Bool => x), (fun x : Bool => x), true, false), ((fun x : Bool => x), (fun x : Bool => x), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State) ++ ([((fun x : Bool => x), (fun x : Bool => !x), false, false), ((fun x : Bool => x), (fun x : Bool => !x), false, true), ((fun x : Bool => x), (fun x : Bool => !x), true, false), ((fun x : Bool => x), (fun x : Bool => !x), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State) ++ ([((fun x : Bool => x), (fun _ : Bool => true), false, false), ((fun x : Bool => x), (fun _ : Bool => true), false, true), ((fun x : Bool => x), (fun _ : Bool => true), true, false), ((fun x : Bool => x), (fun _ : Bool => true), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State) ++ ([((fun x : Bool => !x), (fun _ : Bool => false), false, false), ((fun x : Bool => !x), (fun _ : Bool => false), false, true), ((fun x : Bool => !x), (fun _ : Bool => false), true, false), ((fun x : Bool => !x), (fun _ : Bool => false), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State) ++ ([((fun x : Bool => !x), (fun x : Bool => x), false, false), ((fun x : Bool => !x), (fun x : Bool => x), false, true), ((fun x : Bool => !x), (fun x : Bool => x), true, false), ((fun x : Bool => !x), (fun x : Bool => x), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State) ++ ([((fun x : Bool => !x), (fun x : Bool => !x), false, false), ((fun x : Bool => !x), (fun x : Bool => !x), false, true), ((fun x : Bool => !x), (fun x : Bool => !x), true, false), ((fun x : Bool => !x), (fun x : Bool => !x), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State) ++ ([((fun x : Bool => !x), (fun _ : Bool => true), false, false), ((fun x : Bool => !x), (fun _ : Bool => true), false, true), ((fun x : Bool => !x), (fun _ : Bool => true), true, false), ((fun x : Bool => !x), (fun _ : Bool => true), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State) ++ ([((fun _ : Bool => true), (fun _ : Bool => false), false, false), ((fun _ : Bool => true), (fun _ : Bool => false), false, true), ((fun _ : Bool => true), (fun _ : Bool => false), true, false), ((fun _ : Bool => true), (fun _ : Bool => false), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State) ++ ([((fun _ : Bool => true), (fun x : Bool => x), false, false), ((fun _ : Bool => true), (fun x : Bool => x), false, true), ((fun _ : Bool => true), (fun x : Bool => x), true, false), ((fun _ : Bool => true), (fun x : Bool => x), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State) ++ ([((fun _ : Bool => true), (fun x : Bool => !x), false, false), ((fun _ : Bool => true), (fun x : Bool => !x), false, true), ((fun _ : Bool => true), (fun x : Bool => !x), true, false), ((fun _ : Bool => true), (fun x : Bool => !x), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State) ++ ([((fun _ : Bool => true), (fun _ : Bool => true), false, false), ((fun _ : Bool => true), (fun _ : Bool => true), false, true), ((fun _ : Bool => true), (fun _ : Bool => true), true, false), ((fun _ : Bool => true), (fun _ : Bool => true), true, true)] : List (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena.State)).foldl step _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts.zero = _
          simp only [List.foldl_append, block0, block1, block2, block3, block4, block5, block6, block7, block8, block9, block10, block11, block12, block13, block14, block15]
        have uniqueEq := (catalog.fusedUnique_eq_uniqueCaptureCount states indices (0 : Fin 1)).symm.trans (congrFun (congrArg (fun c => c.unique) computed) 0)
        intro index; fin_cases index
        exact (catalog.lowersEscape_iff_uniqueCaptureCount_pos 0 (by decide +kernel)).mpr (by rw [uniqueEq]; decide))
      enumeration := {
        states := ([(state_8), (state_9), (state_10), (state_11), (state_12), (state_13), (state_14), (state_15), (state_16), (state_17), (state_18), (state_19), (state_20), (state_21), (state_22), (state_23), (state_24), (state_25), (state_26), (state_27), (state_28), (state_29), (state_30), (state_31), (state_32), (state_33), (state_34), (state_35), (state_36), (state_37), (state_38), (state_39), (state_40), (state_41), (state_42), (state_43), (state_44), (state_45), (state_46), (state_47), (state_48), (state_49), (state_50), (state_51), (state_52), (state_53), (state_54), (state_55), (state_56), (state_57), (state_58), (state_59), (state_60), (state_61), (state_62), (state_63), (state_64), (state_65), (state_66), (state_67), (state_68), (state_69), (state_70), (state_71)] : List (Prod (Bool → Bool) (Prod (Bool → Bool) (Prod Bool Bool))))
        nodup := by letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena).stateDecidableEq; letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena).stateFintype; decide +kernel
        complete := by letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena).stateDecidableEq; letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena).toArena).stateFintype; decide +kernel }
    }

noncomputable def facts_1 : Contract.SealFacts catalog_1 where
  units := { entries := [{ position := 0, within := by decide +kernel, item := (D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognition_bridge.toTheoremUnit
           D5.S3.ConceptDynamics.Communication.MutualRecognitionIsJointRealizability.mutual_recognition_does_not_require_equal_concepts), correct := by rfl }]
             complete := rfl }
  rows := [{
      position := 0
      within := by decide +kernel
      row := {
        unique := 1848
        uniqueEq := ((catalog_1.rows (⟨0, by decide +kernel⟩ : Fin catalog_1.size)).uniqueEq).trans (by rfl)
        without := 4032
        withoutEq := ((catalog_1.rows (⟨0, by decide +kernel⟩ : Fin catalog_1.size)).withoutEq).trans (by rfl)
        roleBins := ![0, 1848, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
        roleEq := by intro bucket; exact ((catalog_1.rows (⟨0, by decide +kernel⟩ : Fin catalog_1.size)).roleEq bucket).trans (congrFun (by rfl : (catalog_1.rows (⟨0, by decide +kernel⟩ : Fin catalog_1.size)).roleBins = ![0, 1848, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) bucket)
        roleTotal := by decide +kernel
        conclusion := .positive (by decide +kernel) (by
          apply (D5.S3.ConceptDynamics.InformationEscape.Catalog.lowersEscape_iff_uniqueCaptureCount_pos _ _ catalog_1.nondegenerate).mpr
          rw [(catalog_1.rows (⟨0, by decide +kernel⟩ : Fin catalog_1.size)).uniqueEq]
          decide +kernel) }
      correct := by rfl
      bins := { entries := [{ position := 0, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 1, within := by decide +kernel, item := 1848, correct := by decide +kernel },
                  { position := 2, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 3, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 4, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 5, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 6, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 7, within := by decide +kernel, item := 0, correct := by decide +kernel },
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
                D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena.State
                (D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrationTemplates.existentialWitnessSignature
                  (Prod (Bool → Bool) (Prod (Bool → Bool) (Prod Bool Bool)))))
              (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
                D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena.State
                (D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrationTemplates.existentialWitnessSignature
                  (Prod (Bool → Bool) (Prod (Bool → Bool) (Prod Bool Bool)))))
              PUnit.unit), axis := D5.S3.ConceptDynamics.CIRPT.PrimitiveAxis.admit, correct := by decide +kernel }]
                nodup := by
                  change ([(@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrationTemplates.existentialWitnessSignature
              (Prod (Bool → Bool) (Prod (Bool → Bool) (Prod Bool Bool)))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrationTemplates.existentialWitnessSignature
              (Prod (Bool → Bool) (Prod (Bool → Bool) (Prod Bool Bool)))))
          PUnit.unit)] : List (Sum
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrationTemplates.existentialWitnessSignature
              (Prod (Bool → Bool) (Prod (Bool → Bool) (Prod Bool Bool)))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrationTemplates.existentialWitnessSignature
              (Prod (Bool → Bool) (Prod (Bool → Bool) (Prod Bool Bool))))))).Nodup
                  letI : DecidableEq (Sum _ _) := (by change DecidableEq ((catalog_1.units (⟨0, by decide +kernel⟩ : Fin catalog_1.size)).primitives.Index); exact (catalog_1.units (⟨0, by decide +kernel⟩ : Fin catalog_1.size)).primitives.indexDecidableEq); letI : Fintype (Sum _ _) := (by change Fintype ((catalog_1.units (⟨0, by decide +kernel⟩ : Fin catalog_1.size)).primitives.Index); exact (catalog_1.units (⟨0, by decide +kernel⟩ : Fin catalog_1.size)).primitives.indexFintype)
                  decide +kernel
                complete := by
                  change ∀ i : (Sum
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrationTemplates.existentialWitnessSignature
              (Prod (Bool → Bool) (Prod (Bool → Bool) (Prod Bool Bool)))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrationTemplates.existentialWitnessSignature
              (Prod (Bool → Bool) (Prod (Bool → Bool) (Prod Bool Bool)))))), i ∈ [(@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrationTemplates.existentialWitnessSignature
              (Prod (Bool → Bool) (Prod (Bool → Bool) (Prod Bool Bool)))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena.State
            (D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrationTemplates.existentialWitnessSignature
              (Prod (Bool → Bool) (Prod (Bool → Bool) (Prod Bool Bool)))))
          PUnit.unit)]
                  letI : DecidableEq (Sum _ _) := (by change DecidableEq ((catalog_1.units (⟨0, by decide +kernel⟩ : Fin catalog_1.size)).primitives.Index); exact (catalog_1.units (⟨0, by decide +kernel⟩ : Fin catalog_1.size)).primitives.indexDecidableEq); letI : Fintype (Sum _ _) := (by change Fintype ((catalog_1.units (⟨0, by decide +kernel⟩ : Fin catalog_1.size)).primitives.Index); exact (catalog_1.units (⟨0, by decide +kernel⟩ : Fin catalog_1.size)).primitives.indexFintype)
                  decide +kernel }
      partition := { rows := [{ item := (state_8), classId := 0 },
                       { item := (state_9), classId := 0 },
                       { item := (state_10), classId := 0 },
                       { item := (state_11), classId := 0 },
                       { item := (state_12), classId := 1 },
                       { item := (state_13), classId := 1 },
                       { item := (state_14), classId := 0 },
                       { item := (state_15), classId := 0 },
                       { item := (state_16), classId := 1 },
                       { item := (state_17), classId := 1 },
                       { item := (state_18), classId := 0 },
                       { item := (state_19), classId := 0 },
                       { item := (state_20), classId := 0 },
                       { item := (state_21), classId := 1 },
                       { item := (state_22), classId := 0 },
                       { item := (state_23), classId := 0 },
                       { item := (state_24), classId := 1 },
                       { item := (state_25), classId := 0 },
                       { item := (state_26), classId := 1 },
                       { item := (state_27), classId := 0 },
                       { item := (state_28), classId := 0 },
                       { item := (state_29), classId := 0 },
                       { item := (state_30), classId := 0 },
                       { item := (state_31), classId := 0 },
                       { item := (state_32), classId := 0 },
                       { item := (state_33), classId := 1 },
                       { item := (state_34), classId := 1 },
                       { item := (state_35), classId := 0 },
                       { item := (state_36), classId := 0 },
                       { item := (state_37), classId := 1 },
                       { item := (state_38), classId := 0 },
                       { item := (state_39), classId := 1 },
                       { item := (state_40), classId := 1 },
                       { item := (state_41), classId := 0 },
                       { item := (state_42), classId := 1 },
                       { item := (state_43), classId := 0 },
                       { item := (state_44), classId := 0 },
                       { item := (state_45), classId := 1 },
                       { item := (state_46), classId := 1 },
                       { item := (state_47), classId := 0 },
                       { item := (state_48), classId := 0 },
                       { item := (state_49), classId := 0 },
                       { item := (state_50), classId := 0 },
                       { item := (state_51), classId := 0 },
                       { item := (state_52), classId := 0 },
                       { item := (state_53), classId := 1 },
                       { item := (state_54), classId := 0 },
                       { item := (state_55), classId := 1 },
                       { item := (state_56), classId := 0 },
                       { item := (state_57), classId := 0 },
                       { item := (state_58), classId := 1 },
                       { item := (state_59), classId := 0 },
                       { item := (state_60), classId := 0 },
                       { item := (state_61), classId := 0 },
                       { item := (state_62), classId := 1 },
                       { item := (state_63), classId := 1 },
                       { item := (state_64), classId := 0 },
                       { item := (state_65), classId := 0 },
                       { item := (state_66), classId := 1 },
                       { item := (state_67), classId := 1 },
                       { item := (state_68), classId := 0 },
                       { item := (state_69), classId := 0 },
                       { item := (state_70), classId := 0 },
                       { item := (state_71), classId := 0 }]
                     nodup := by
                       letI := catalog_1.arena.stateDecidableEq; letI := catalog_1.arena.stateFintype
                       change ([(state_8), (state_9), (state_10), (state_11), (state_12), (state_13), (state_14), (state_15), (state_16), (state_17), (state_18), (state_19), (state_20), (state_21), (state_22), (state_23), (state_24), (state_25), (state_26), (state_27), (state_28), (state_29), (state_30), (state_31), (state_32), (state_33), (state_34), (state_35), (state_36), (state_37), (state_38), (state_39), (state_40), (state_41), (state_42), (state_43), (state_44), (state_45), (state_46), (state_47), (state_48), (state_49), (state_50), (state_51), (state_52), (state_53), (state_54), (state_55), (state_56), (state_57), (state_58), (state_59), (state_60), (state_61), (state_62), (state_63), (state_64), (state_65), (state_66), (state_67), (state_68), (state_69), (state_70), (state_71)] : List (Prod (Bool → Bool) (Prod (Bool → Bool) (Prod Bool Bool)))).Nodup
                       decide +kernel
                     complete := by
                       letI := catalog_1.arena.stateDecidableEq; letI := catalog_1.arena.stateFintype
                       change ∀ x : (Prod (Bool → Bool) (Prod (Bool → Bool) (Prod Bool Bool))), x ∈ [(state_8), (state_9), (state_10), (state_11), (state_12), (state_13), (state_14), (state_15), (state_16), (state_17), (state_18), (state_19), (state_20), (state_21), (state_22), (state_23), (state_24), (state_25), (state_26), (state_27), (state_28), (state_29), (state_30), (state_31), (state_32), (state_33), (state_34), (state_35), (state_36), (state_37), (state_38), (state_39), (state_40), (state_41), (state_42), (state_43), (state_44), (state_45), (state_46), (state_47), (state_48), (state_49), (state_50), (state_51), (state_52), (state_53), (state_54), (state_55), (state_56), (state_57), (state_58), (state_59), (state_60), (state_61), (state_62), (state_63), (state_64), (state_65), (state_66), (state_67), (state_68), (state_69), (state_70), (state_71)]
                       decide +kernel
                     classes := by letI := catalog_1.arena.stateDecidableEq; letI := catalog_1.arena.stateFintype; decide +kernel }
      stateOrder := by rfl }]
  complete := rfl

noncomputable def view_1 : Contract.SealCatalogView := { catalog := catalog_1, facts := facts_1 }

noncomputable def «seal» : Contract.Seal := {
  rootId := `Reg.Catalogs.ExistentialWitnessRegistrations.SealedCatalog
  catalogs := #[
    view_0,
    view_1
  ]
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxHeartbeats, value := .nat 2000000 }, { name := `maxRecDepth, value := .nat 100000 }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }

end Reg.Catalogs.ExistentialWitnessRegistrations.SealedCatalog
