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

noncomputable def «seal» : Contract.Seal := {
  rootId := `Reg.Catalogs.MapInjectiveRegistrations.SealedCatalog
  catalogs := #[
    {
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
      enumeration := by letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.markerArena).toArena).stateFintype; letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.markerArena).toArena).stateDecidableEq; exact ⟨Finset.univ.toList, Finset.nodup_toList _, by simp⟩
    },
    {
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
      enumeration := by letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.opcodeArena).toArena).stateFintype; letI := ((_root_.D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.opcodeArena).toArena).stateDecidableEq; exact ⟨Finset.univ.toList, Finset.nodup_toList _, by simp⟩
    },
    {
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
      enumeration := ⟨(List.finRange 18 : List (Fin 18)), (by change (List.finRange 18 : List (Fin 18)).Nodup; decide +kernel), (by change (List.finRange 18 : List (Fin 18)).toFinset = (Finset.univ : Finset (Fin 18)); decide +kernel)⟩
    }
  ]
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxRecDepth, value := .nat 100000 }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }

end Reg.Catalogs.MapInjectiveRegistrations.SealedCatalog
