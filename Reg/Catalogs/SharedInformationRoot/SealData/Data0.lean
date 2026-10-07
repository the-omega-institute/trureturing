import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import LeanInformationAuditInterface.Contract.Catalog
import D5.S3.ConceptDynamics.CIRPT.PrimitiveKernel
import D5.S3.ConceptDynamics.InformationEscape.ExactRate
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.InformationEscapeCounting.Fused
import D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation
import D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation
import Reg.Catalogs.SharedInformationRoot.SealData.States0
import Reg.Support.LegacyCausalCoordinates
import Reg.Support.LegacyCausalFinite
import Reg.Support.LegacyCausalSlots

set_option backward.isDefEq.respectTransparency.types false

namespace Reg.Catalogs.SharedInformationRoot.SealedCatalog
open LeanInformationAudit

noncomputable def catalog_0 : Contract.SealCatalog := {
      arenaName := `Reg.Support.LegacyCausalCoordinates.objectArena
      catalogId := `«causal-unified-transitions»
      arena := (_root_.Reg.Support.LegacyCausalCoordinates.objectArena)
      size := 2
      units := ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.Reg.Support.LegacyCausalCoordinates.objectArena)).stateDecidableEq (Reg.Support.LegacyCausalFinite.icActual)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.intervention_strictly_weaker_than_counterfactual) }, { primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.Reg.Support.LegacyCausalCoordinates.objectArena)).stateDecidableEq (Reg.Support.LegacyCausalFinite.oiActual)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.observation_strictly_weaker_than_intervention) }]
      nondegenerate := _root_.Reg.Support.LegacyCausalFinite.unified_nondegenerate
      bundleNonempty := by intro index; fin_cases index <;> decide +kernel
      stateCard := 48
      stateCardEq := by decide +kernel
      full := 24
      fullEq := by let states := _root_.Reg.Support.LegacyCausalFinite.unifiedEnumeration; let catalog := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.Reg.Support.LegacyCausalCoordinates.objectArena)).stateDecidableEq (Reg.Support.LegacyCausalFinite.icActual)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.intervention_strictly_weaker_than_counterfactual) }, { primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.Reg.Support.LegacyCausalCoordinates.objectArena)).stateDecidableEq (Reg.Support.LegacyCausalFinite.oiActual)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.observation_strictly_weaker_than_intervention) }]; let indices := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.finIndexEnumeration 2; exact (catalog.fusedFull_eq_escapeNumerator states indices).symm.trans (by decide +kernel)
      rows := Fin.cases (by
        let states := _root_.Reg.Support.LegacyCausalFinite.unifiedEnumeration
        let catalog := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.Reg.Support.LegacyCausalCoordinates.objectArena)).stateDecidableEq (Reg.Support.LegacyCausalFinite.icActual)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.intervention_strictly_weaker_than_counterfactual) }, { primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.Reg.Support.LegacyCausalCoordinates.objectArena)).stateDecidableEq (Reg.Support.LegacyCausalFinite.oiActual)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.observation_strictly_weaker_than_intervention) }]
        let indices := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.finIndexEnumeration 2
        let allStates : List (_root_.Reg.Support.LegacyCausalCoordinates.objectArena).State := [Sum.inl (false, false, false, false), Sum.inl (false, false, false, true), Sum.inl (false, false, true, false), Sum.inl (false, false, true, true), Sum.inl (false, true, false, false), Sum.inl (false, true, false, true), Sum.inl (false, true, true, false), Sum.inl (false, true, true, true), Sum.inl (true, false, false, false), Sum.inl (true, false, false, true), Sum.inl (true, false, true, false), Sum.inl (true, false, true, true), Sum.inl (true, true, false, false), Sum.inl (true, true, false, true), Sum.inl (true, true, true, false), Sum.inl (true, true, true, true), Sum.inr (false, (false, false), (false, false)), Sum.inr (false, (false, false), (false, true)), Sum.inr (false, (false, false), (true, false)), Sum.inr (false, (false, false), (true, true)), Sum.inr (false, (false, true), (false, false)), Sum.inr (false, (false, true), (false, true)), Sum.inr (false, (false, true), (true, false)), Sum.inr (false, (false, true), (true, true)), Sum.inr (false, (true, false), (false, false)), Sum.inr (false, (true, false), (false, true)), Sum.inr (false, (true, false), (true, false)), Sum.inr (false, (true, false), (true, true)), Sum.inr (false, (true, true), (false, false)), Sum.inr (false, (true, true), (false, true)), Sum.inr (false, (true, true), (true, false)), Sum.inr (false, (true, true), (true, true)), Sum.inr (true, (false, false), (false, false)), Sum.inr (true, (false, false), (false, true)), Sum.inr (true, (false, false), (true, false)), Sum.inr (true, (false, false), (true, true)), Sum.inr (true, (false, true), (false, false)), Sum.inr (true, (false, true), (false, true)), Sum.inr (true, (false, true), (true, false)), Sum.inr (true, (false, true), (true, true)), Sum.inr (true, (true, false), (false, false)), Sum.inr (true, (true, false), (false, true)), Sum.inr (true, (true, false), (true, false)), Sum.inr (true, (true, false), (true, true)), Sum.inr (true, (true, true), (false, false)), Sum.inr (true, (true, true), (false, true)), Sum.inr (true, (true, true), (true, false)), Sum.inr (true, (true, true), (true, true))]
        let step := fun (counts : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 2)) left =>
          allStates.foldl (fun counts right => catalog.pairStep indices counts left right) counts
        have extCounts (a b : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 2))
            (hf : a.full = b.full) (hu : a.unique = b.unique) (hr : a.roleBins = b.roleBins) : a = b := by
          cases a; cases b; cases hf; cases hu; cases hr; rfl
        have block0 : ([Sum.inl (false, false, false, false), Sum.inl (false, false, false, true), Sum.inl (false, false, true, false), Sum.inl (false, false, true, true), Sum.inl (false, true, false, false), Sum.inl (false, true, false, true), Sum.inl (false, true, true, false), Sum.inl (false, true, true, true)] : List (_root_.Reg.Support.LegacyCausalCoordinates.objectArena).State).foldl step _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts.zero = ({ full := 0, unique := ![120, 0], roleBins := ![![0, 0, 0, 0, 0, 0, 0, 120, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 2)) := by
          apply extCounts
          · decide +kernel
          · apply funext; decide +kernel
          · apply funext; decide +kernel
        have block1 : ([Sum.inl (true, false, false, false), Sum.inl (true, false, false, true), Sum.inl (true, false, true, false), Sum.inl (true, false, true, true), Sum.inl (true, true, false, false), Sum.inl (true, true, false, true), Sum.inl (true, true, true, false), Sum.inl (true, true, true, true)] : List (_root_.Reg.Support.LegacyCausalCoordinates.objectArena).State).foldl step ({ full := 0, unique := ![120, 0], roleBins := ![![0, 0, 0, 0, 0, 0, 0, 120, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 2)) = ({ full := 0, unique := ![240, 0], roleBins := ![![0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 2)) := by
          apply extCounts
          · decide +kernel
          · apply funext; decide +kernel
          · apply funext; decide +kernel
        have block2 : ([Sum.inr (false, (false, false), (false, false)), Sum.inr (false, (false, false), (false, true)), Sum.inr (false, (false, false), (true, false)), Sum.inr (false, (false, false), (true, true)), Sum.inr (false, (false, true), (false, false)), Sum.inr (false, (false, true), (false, true)), Sum.inr (false, (false, true), (true, false)), Sum.inr (false, (false, true), (true, true))] : List (_root_.Reg.Support.LegacyCausalCoordinates.objectArena).State).foldl step ({ full := 0, unique := ![240, 0], roleBins := ![![0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 2)) = ({ full := 4, unique := ![240, 244], roleBins := ![![0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 244, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 2)) := by
          apply extCounts
          · decide +kernel
          · apply funext; decide +kernel
          · apply funext; decide +kernel
        have block3 : ([Sum.inr (false, (true, false), (false, false)), Sum.inr (false, (true, false), (false, true)), Sum.inr (false, (true, false), (true, false)), Sum.inr (false, (true, false), (true, true)), Sum.inr (false, (true, true), (false, false)), Sum.inr (false, (true, true), (false, true)), Sum.inr (false, (true, true), (true, false)), Sum.inr (false, (true, true), (true, true))] : List (_root_.Reg.Support.LegacyCausalCoordinates.objectArena).State).foldl step ({ full := 4, unique := ![240, 244], roleBins := ![![0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 244, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 2)) = ({ full := 8, unique := ![240, 488], roleBins := ![![0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 488, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 2)) := by
          apply extCounts
          · decide +kernel
          · apply funext; decide +kernel
          · apply funext; decide +kernel
        have block4 : ([Sum.inr (true, (false, false), (false, false)), Sum.inr (true, (false, false), (false, true)), Sum.inr (true, (false, false), (true, false)), Sum.inr (true, (false, false), (true, true)), Sum.inr (true, (false, true), (false, false)), Sum.inr (true, (false, true), (false, true)), Sum.inr (true, (false, true), (true, false)), Sum.inr (true, (false, true), (true, true))] : List (_root_.Reg.Support.LegacyCausalCoordinates.objectArena).State).foldl step ({ full := 8, unique := ![240, 488], roleBins := ![![0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 488, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 2)) = ({ full := 16, unique := ![240, 728], roleBins := ![![0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 728, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 2)) := by
          apply extCounts
          · decide +kernel
          · apply funext; decide +kernel
          · apply funext; decide +kernel
        have block5 : ([Sum.inr (true, (true, false), (false, false)), Sum.inr (true, (true, false), (false, true)), Sum.inr (true, (true, false), (true, false)), Sum.inr (true, (true, false), (true, true)), Sum.inr (true, (true, true), (false, false)), Sum.inr (true, (true, true), (false, true)), Sum.inr (true, (true, true), (true, false)), Sum.inr (true, (true, true), (true, true))] : List (_root_.Reg.Support.LegacyCausalCoordinates.objectArena).State).foldl step ({ full := 16, unique := ![240, 728], roleBins := ![![0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 728, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 2)) = ({ full := 24, unique := ![240, 968], roleBins := ![![0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 968, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 2)) := by
          apply extCounts
          · decide +kernel
          · apply funext; decide +kernel
          · apply funext; decide +kernel
        have computed : catalog.fusedCounts states indices = ({ full := 24, unique := ![240, 968], roleBins := ![![0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 968, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 2)) := by
          change (([Sum.inl (false, false, false, false), Sum.inl (false, false, false, true), Sum.inl (false, false, true, false), Sum.inl (false, false, true, true), Sum.inl (false, true, false, false), Sum.inl (false, true, false, true), Sum.inl (false, true, true, false), Sum.inl (false, true, true, true)] : List (_root_.Reg.Support.LegacyCausalCoordinates.objectArena).State) ++ ([Sum.inl (true, false, false, false), Sum.inl (true, false, false, true), Sum.inl (true, false, true, false), Sum.inl (true, false, true, true), Sum.inl (true, true, false, false), Sum.inl (true, true, false, true), Sum.inl (true, true, true, false), Sum.inl (true, true, true, true)] : List (_root_.Reg.Support.LegacyCausalCoordinates.objectArena).State) ++ ([Sum.inr (false, (false, false), (false, false)), Sum.inr (false, (false, false), (false, true)), Sum.inr (false, (false, false), (true, false)), Sum.inr (false, (false, false), (true, true)), Sum.inr (false, (false, true), (false, false)), Sum.inr (false, (false, true), (false, true)), Sum.inr (false, (false, true), (true, false)), Sum.inr (false, (false, true), (true, true))] : List (_root_.Reg.Support.LegacyCausalCoordinates.objectArena).State) ++ ([Sum.inr (false, (true, false), (false, false)), Sum.inr (false, (true, false), (false, true)), Sum.inr (false, (true, false), (true, false)), Sum.inr (false, (true, false), (true, true)), Sum.inr (false, (true, true), (false, false)), Sum.inr (false, (true, true), (false, true)), Sum.inr (false, (true, true), (true, false)), Sum.inr (false, (true, true), (true, true))] : List (_root_.Reg.Support.LegacyCausalCoordinates.objectArena).State) ++ ([Sum.inr (true, (false, false), (false, false)), Sum.inr (true, (false, false), (false, true)), Sum.inr (true, (false, false), (true, false)), Sum.inr (true, (false, false), (true, true)), Sum.inr (true, (false, true), (false, false)), Sum.inr (true, (false, true), (false, true)), Sum.inr (true, (false, true), (true, false)), Sum.inr (true, (false, true), (true, true))] : List (_root_.Reg.Support.LegacyCausalCoordinates.objectArena).State) ++ ([Sum.inr (true, (true, false), (false, false)), Sum.inr (true, (true, false), (false, true)), Sum.inr (true, (true, false), (true, false)), Sum.inr (true, (true, false), (true, true)), Sum.inr (true, (true, true), (false, false)), Sum.inr (true, (true, true), (false, true)), Sum.inr (true, (true, true), (true, false)), Sum.inr (true, (true, true), (true, true))] : List (_root_.Reg.Support.LegacyCausalCoordinates.objectArena).State)).foldl step _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts.zero = _
          simp only [List.foldl_append, block0, block1, block2, block3, block4, block5]
        have uniqueEq0 := (catalog.fusedUnique_eq_uniqueCaptureCount states indices (0 : Fin 2)).symm.trans (congrFun (congrArg (fun c => c.unique) computed) 0)
        have lowering0 := (catalog.lowersEscape_iff_uniqueCaptureCount_pos 0 (by decide +kernel)).mpr (by rw [uniqueEq0]; decide)
        have uniqueEq1 := (catalog.fusedUnique_eq_uniqueCaptureCount states indices (1 : Fin 2)).symm.trans (congrFun (congrArg (fun c => c.unique) computed) 1)
        have lowering1 := (catalog.lowersEscape_iff_uniqueCaptureCount_pos 1 (by decide +kernel)).mpr (by rw [uniqueEq1]; decide)
        exact
          ({ unique := 240
             uniqueEq := uniqueEq0
             without := 264
             withoutEq := (catalog.fusedWithout_eq_escapeNumerator_without states indices 0).symm.trans (congrArg (fun c => c.without 0) computed)
             roleBins := ![0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0]
             roleEq := fun bucket => (catalog.fusedRoleBins_eq_roleHistogram states indices 0 bucket).symm.trans (congrFun (congrFun (congrArg (fun c => c.roleBins) computed) 0) bucket)
             roleTotal := by decide +kernel
             conclusion := .positive (by decide +kernel) lowering0 } : Contract.SealRow catalog 0))
        (fun i => Fin.cases (by
        let states := _root_.Reg.Support.LegacyCausalFinite.unifiedEnumeration
        let catalog := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.Reg.Support.LegacyCausalCoordinates.objectArena)).stateDecidableEq (Reg.Support.LegacyCausalFinite.icActual)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.intervention_strictly_weaker_than_counterfactual) }, { primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.Reg.Support.LegacyCausalCoordinates.objectArena)).stateDecidableEq (Reg.Support.LegacyCausalFinite.oiActual)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.observation_strictly_weaker_than_intervention) }]
        let indices := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.finIndexEnumeration 2
        let allStates : List (_root_.Reg.Support.LegacyCausalCoordinates.objectArena).State := [Sum.inl (false, false, false, false), Sum.inl (false, false, false, true), Sum.inl (false, false, true, false), Sum.inl (false, false, true, true), Sum.inl (false, true, false, false), Sum.inl (false, true, false, true), Sum.inl (false, true, true, false), Sum.inl (false, true, true, true), Sum.inl (true, false, false, false), Sum.inl (true, false, false, true), Sum.inl (true, false, true, false), Sum.inl (true, false, true, true), Sum.inl (true, true, false, false), Sum.inl (true, true, false, true), Sum.inl (true, true, true, false), Sum.inl (true, true, true, true), Sum.inr (false, (false, false), (false, false)), Sum.inr (false, (false, false), (false, true)), Sum.inr (false, (false, false), (true, false)), Sum.inr (false, (false, false), (true, true)), Sum.inr (false, (false, true), (false, false)), Sum.inr (false, (false, true), (false, true)), Sum.inr (false, (false, true), (true, false)), Sum.inr (false, (false, true), (true, true)), Sum.inr (false, (true, false), (false, false)), Sum.inr (false, (true, false), (false, true)), Sum.inr (false, (true, false), (true, false)), Sum.inr (false, (true, false), (true, true)), Sum.inr (false, (true, true), (false, false)), Sum.inr (false, (true, true), (false, true)), Sum.inr (false, (true, true), (true, false)), Sum.inr (false, (true, true), (true, true)), Sum.inr (true, (false, false), (false, false)), Sum.inr (true, (false, false), (false, true)), Sum.inr (true, (false, false), (true, false)), Sum.inr (true, (false, false), (true, true)), Sum.inr (true, (false, true), (false, false)), Sum.inr (true, (false, true), (false, true)), Sum.inr (true, (false, true), (true, false)), Sum.inr (true, (false, true), (true, true)), Sum.inr (true, (true, false), (false, false)), Sum.inr (true, (true, false), (false, true)), Sum.inr (true, (true, false), (true, false)), Sum.inr (true, (true, false), (true, true)), Sum.inr (true, (true, true), (false, false)), Sum.inr (true, (true, true), (false, true)), Sum.inr (true, (true, true), (true, false)), Sum.inr (true, (true, true), (true, true))]
        let step := fun (counts : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 2)) left =>
          allStates.foldl (fun counts right => catalog.pairStep indices counts left right) counts
        have extCounts (a b : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 2))
            (hf : a.full = b.full) (hu : a.unique = b.unique) (hr : a.roleBins = b.roleBins) : a = b := by
          cases a; cases b; cases hf; cases hu; cases hr; rfl
        have block0 : ([Sum.inl (false, false, false, false), Sum.inl (false, false, false, true), Sum.inl (false, false, true, false), Sum.inl (false, false, true, true), Sum.inl (false, true, false, false), Sum.inl (false, true, false, true), Sum.inl (false, true, true, false), Sum.inl (false, true, true, true)] : List (_root_.Reg.Support.LegacyCausalCoordinates.objectArena).State).foldl step _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts.zero = ({ full := 0, unique := ![120, 0], roleBins := ![![0, 0, 0, 0, 0, 0, 0, 120, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 2)) := by
          apply extCounts
          · decide +kernel
          · apply funext; decide +kernel
          · apply funext; decide +kernel
        have block1 : ([Sum.inl (true, false, false, false), Sum.inl (true, false, false, true), Sum.inl (true, false, true, false), Sum.inl (true, false, true, true), Sum.inl (true, true, false, false), Sum.inl (true, true, false, true), Sum.inl (true, true, true, false), Sum.inl (true, true, true, true)] : List (_root_.Reg.Support.LegacyCausalCoordinates.objectArena).State).foldl step ({ full := 0, unique := ![120, 0], roleBins := ![![0, 0, 0, 0, 0, 0, 0, 120, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 2)) = ({ full := 0, unique := ![240, 0], roleBins := ![![0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 2)) := by
          apply extCounts
          · decide +kernel
          · apply funext; decide +kernel
          · apply funext; decide +kernel
        have block2 : ([Sum.inr (false, (false, false), (false, false)), Sum.inr (false, (false, false), (false, true)), Sum.inr (false, (false, false), (true, false)), Sum.inr (false, (false, false), (true, true)), Sum.inr (false, (false, true), (false, false)), Sum.inr (false, (false, true), (false, true)), Sum.inr (false, (false, true), (true, false)), Sum.inr (false, (false, true), (true, true))] : List (_root_.Reg.Support.LegacyCausalCoordinates.objectArena).State).foldl step ({ full := 0, unique := ![240, 0], roleBins := ![![0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 2)) = ({ full := 4, unique := ![240, 244], roleBins := ![![0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 244, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 2)) := by
          apply extCounts
          · decide +kernel
          · apply funext; decide +kernel
          · apply funext; decide +kernel
        have block3 : ([Sum.inr (false, (true, false), (false, false)), Sum.inr (false, (true, false), (false, true)), Sum.inr (false, (true, false), (true, false)), Sum.inr (false, (true, false), (true, true)), Sum.inr (false, (true, true), (false, false)), Sum.inr (false, (true, true), (false, true)), Sum.inr (false, (true, true), (true, false)), Sum.inr (false, (true, true), (true, true))] : List (_root_.Reg.Support.LegacyCausalCoordinates.objectArena).State).foldl step ({ full := 4, unique := ![240, 244], roleBins := ![![0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 244, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 2)) = ({ full := 8, unique := ![240, 488], roleBins := ![![0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 488, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 2)) := by
          apply extCounts
          · decide +kernel
          · apply funext; decide +kernel
          · apply funext; decide +kernel
        have block4 : ([Sum.inr (true, (false, false), (false, false)), Sum.inr (true, (false, false), (false, true)), Sum.inr (true, (false, false), (true, false)), Sum.inr (true, (false, false), (true, true)), Sum.inr (true, (false, true), (false, false)), Sum.inr (true, (false, true), (false, true)), Sum.inr (true, (false, true), (true, false)), Sum.inr (true, (false, true), (true, true))] : List (_root_.Reg.Support.LegacyCausalCoordinates.objectArena).State).foldl step ({ full := 8, unique := ![240, 488], roleBins := ![![0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 488, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 2)) = ({ full := 16, unique := ![240, 728], roleBins := ![![0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 728, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 2)) := by
          apply extCounts
          · decide +kernel
          · apply funext; decide +kernel
          · apply funext; decide +kernel
        have block5 : ([Sum.inr (true, (true, false), (false, false)), Sum.inr (true, (true, false), (false, true)), Sum.inr (true, (true, false), (true, false)), Sum.inr (true, (true, false), (true, true)), Sum.inr (true, (true, true), (false, false)), Sum.inr (true, (true, true), (false, true)), Sum.inr (true, (true, true), (true, false)), Sum.inr (true, (true, true), (true, true))] : List (_root_.Reg.Support.LegacyCausalCoordinates.objectArena).State).foldl step ({ full := 16, unique := ![240, 728], roleBins := ![![0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 728, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 2)) = ({ full := 24, unique := ![240, 968], roleBins := ![![0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 968, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 2)) := by
          apply extCounts
          · decide +kernel
          · apply funext; decide +kernel
          · apply funext; decide +kernel
        have computed : catalog.fusedCounts states indices = ({ full := 24, unique := ![240, 968], roleBins := ![![0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 968, 0, 0, 0, 0, 0, 0, 0]] } : _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts (Fin 2)) := by
          change (([Sum.inl (false, false, false, false), Sum.inl (false, false, false, true), Sum.inl (false, false, true, false), Sum.inl (false, false, true, true), Sum.inl (false, true, false, false), Sum.inl (false, true, false, true), Sum.inl (false, true, true, false), Sum.inl (false, true, true, true)] : List (_root_.Reg.Support.LegacyCausalCoordinates.objectArena).State) ++ ([Sum.inl (true, false, false, false), Sum.inl (true, false, false, true), Sum.inl (true, false, true, false), Sum.inl (true, false, true, true), Sum.inl (true, true, false, false), Sum.inl (true, true, false, true), Sum.inl (true, true, true, false), Sum.inl (true, true, true, true)] : List (_root_.Reg.Support.LegacyCausalCoordinates.objectArena).State) ++ ([Sum.inr (false, (false, false), (false, false)), Sum.inr (false, (false, false), (false, true)), Sum.inr (false, (false, false), (true, false)), Sum.inr (false, (false, false), (true, true)), Sum.inr (false, (false, true), (false, false)), Sum.inr (false, (false, true), (false, true)), Sum.inr (false, (false, true), (true, false)), Sum.inr (false, (false, true), (true, true))] : List (_root_.Reg.Support.LegacyCausalCoordinates.objectArena).State) ++ ([Sum.inr (false, (true, false), (false, false)), Sum.inr (false, (true, false), (false, true)), Sum.inr (false, (true, false), (true, false)), Sum.inr (false, (true, false), (true, true)), Sum.inr (false, (true, true), (false, false)), Sum.inr (false, (true, true), (false, true)), Sum.inr (false, (true, true), (true, false)), Sum.inr (false, (true, true), (true, true))] : List (_root_.Reg.Support.LegacyCausalCoordinates.objectArena).State) ++ ([Sum.inr (true, (false, false), (false, false)), Sum.inr (true, (false, false), (false, true)), Sum.inr (true, (false, false), (true, false)), Sum.inr (true, (false, false), (true, true)), Sum.inr (true, (false, true), (false, false)), Sum.inr (true, (false, true), (false, true)), Sum.inr (true, (false, true), (true, false)), Sum.inr (true, (false, true), (true, true))] : List (_root_.Reg.Support.LegacyCausalCoordinates.objectArena).State) ++ ([Sum.inr (true, (true, false), (false, false)), Sum.inr (true, (true, false), (false, true)), Sum.inr (true, (true, false), (true, false)), Sum.inr (true, (true, false), (true, true)), Sum.inr (true, (true, true), (false, false)), Sum.inr (true, (true, true), (false, true)), Sum.inr (true, (true, true), (true, false)), Sum.inr (true, (true, true), (true, true))] : List (_root_.Reg.Support.LegacyCausalCoordinates.objectArena).State)).foldl step _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.FusedCounts.zero = _
          simp only [List.foldl_append, block0, block1, block2, block3, block4, block5]
        have uniqueEq0 := (catalog.fusedUnique_eq_uniqueCaptureCount states indices (0 : Fin 2)).symm.trans (congrFun (congrArg (fun c => c.unique) computed) 0)
        have lowering0 := (catalog.lowersEscape_iff_uniqueCaptureCount_pos 0 (by decide +kernel)).mpr (by rw [uniqueEq0]; decide)
        have uniqueEq1 := (catalog.fusedUnique_eq_uniqueCaptureCount states indices (1 : Fin 2)).symm.trans (congrFun (congrArg (fun c => c.unique) computed) 1)
        have lowering1 := (catalog.lowersEscape_iff_uniqueCaptureCount_pos 1 (by decide +kernel)).mpr (by rw [uniqueEq1]; decide)
        exact
          ({ unique := 968
             uniqueEq := uniqueEq1
             without := 992
             withoutEq := (catalog.fusedWithout_eq_escapeNumerator_without states indices 1).symm.trans (congrArg (fun c => c.without 1) computed)
             roleBins := ![0, 0, 0, 0, 0, 0, 0, 968, 0, 0, 0, 0, 0, 0, 0]
             roleEq := fun bucket => (catalog.fusedRoleBins_eq_roleHistogram states indices 1 bucket).symm.trans (congrFun (congrFun (congrArg (fun c => c.roleBins) computed) 1) bucket)
             roleTotal := by decide +kernel
             conclusion := .positive (by decide +kernel) lowering1 } : Contract.SealRow catalog 1))
          (fun j => Fin.elim0 j) i)
      collisions := #[]
      conclusion := .irredundant (by
        let catalog := _root_.D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.Reg.Support.LegacyCausalCoordinates.objectArena)).stateDecidableEq (Reg.Support.LegacyCausalFinite.icActual)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.intervention_strictly_weaker_than_counterfactual) }, { primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.Reg.Support.LegacyCausalCoordinates.objectArena)).stateDecidableEq (Reg.Support.LegacyCausalFinite.oiActual)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.observation_strictly_weaker_than_intervention) }]
        intro index
        fin_cases index
        · apply (catalog.lowersEscape_iff_uniqueCaptureCount_pos 0 Reg.Support.LegacyCausalFinite.unified_nondegenerate).mpr
          apply (catalog.uniqueCaptureCount_pos_iff_witness 0).mpr
          refine ⟨Sum.inl (false, false, false, false), Sum.inl (false, false, false, true), ?_⟩
          refine ⟨?_, ?_, ?_⟩
          · change (Sum.inl (false, false, false, false) : ((Bool × Bool × Bool × Bool) ⊕ (Bool × (Bool × Bool) × (Bool × Bool)))) ≠ Sum.inl (false, false, false, true)
            decide +kernel
          · intro candidate different
            change Fin 2 at candidate
            fin_cases candidate
            · exact (different rfl).elim
            · decide +kernel
          · decide +kernel
        · apply (catalog.lowersEscape_iff_uniqueCaptureCount_pos 1 Reg.Support.LegacyCausalFinite.unified_nondegenerate).mpr
          apply (catalog.uniqueCaptureCount_pos_iff_witness 1).mpr
          refine ⟨Sum.inr (false, (false, false), (false, false)), Sum.inr (false, (false, false), (false, true)), ?_⟩
          refine ⟨?_, ?_, ?_⟩
          · change (Sum.inr (false, (false, false), (false, false)) : ((Bool × Bool × Bool × Bool) ⊕ (Bool × (Bool × Bool) × (Bool × Bool)))) ≠ Sum.inr (false, (false, false), (false, true))
            decide +kernel
          · intro candidate different
            change Fin 2 at candidate
            fin_cases candidate
            · decide +kernel
            · exact (different rfl).elim
          · decide +kernel)
      enumeration := {
        states := ([(@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
  (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.true
    (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.true Bool.true)))), (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
  (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.true
    (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.true Bool.false)))), (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
  (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.true
    (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.false Bool.true)))), (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
  (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.true
    (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.false Bool.false)))), (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
  (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.true
    (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.true Bool.true)))), (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
  (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.true
    (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.true Bool.false)))), (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
  (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.true
    (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.false Bool.true)))), (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
  (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.true
    (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.false Bool.false)))), (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
  (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.false
    (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.true Bool.true)))), (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
  (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.false
    (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.true Bool.false)))), (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
  (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.false
    (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.false Bool.true)))), (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
  (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.false
    (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.false Bool.false)))), (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
  (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.false
    (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.true Bool.true)))), (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
  (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.false
    (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.true Bool.false)))), (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
  (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.false
    (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.false Bool.true)))), (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
  (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.false
    (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.false Bool.false)))), (state_0), (state_1), (state_2), (state_3), (state_4), (state_5), (state_6), (state_7), (state_8), (state_9), (state_10), (state_11), (state_12), (state_13), (state_14), (state_15), (state_16), (state_17), (state_18), (state_19), (state_20), (state_21), (state_22), (state_23), (state_24), (state_25), (state_26), (state_27), (state_28), (state_29), (state_30), (state_31)] : List (Sum Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData))
        nodup := by letI := ((_root_.Reg.Support.LegacyCausalCoordinates.objectArena)).stateDecidableEq; letI := ((_root_.Reg.Support.LegacyCausalCoordinates.objectArena)).stateFintype; apply of_decide_eq_true; decide +kernel
        complete := by letI := ((_root_.Reg.Support.LegacyCausalCoordinates.objectArena)).stateDecidableEq; letI := ((_root_.Reg.Support.LegacyCausalCoordinates.objectArena)).stateFintype; apply of_decide_eq_true; decide +kernel }
    }

noncomputable def facts_0_row_0 : Contract.SealFactRow catalog_0 :=
  {
      position := 0
      within := by decide +kernel
      row := {
        unique := 240
        uniqueEq := ((catalog_0.rows (⟨0, by decide +kernel⟩ : Fin catalog_0.size)).uniqueEq).trans (by rfl)
        without := 264
        withoutEq := ((catalog_0.rows (⟨0, by decide +kernel⟩ : Fin catalog_0.size)).withoutEq).trans (by rfl)
        roleBins := ![0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0]
        roleEq := by intro bucket; exact ((catalog_0.rows (⟨0, by decide +kernel⟩ : Fin catalog_0.size)).roleEq bucket).trans (congrFun (by rfl : (catalog_0.rows (⟨0, by decide +kernel⟩ : Fin catalog_0.size)).roleBins = ![0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0]) bucket)
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
                  { position := 7, within := by decide +kernel, item := 240, correct := by decide +kernel },
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
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) (nat_lit 0)
            (@Nat.le_of_lt (nat_lit 1) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
              (@Nat.le_of_lt (nat_lit 2) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                (@Nat.le_of_lt (nat_lit 3) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                  (@Nat.le_of_lt (nat_lit 4) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                    (@Nat.le_of_lt (nat_lit 5) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                      (@Nat.le_of_lt (nat_lit 6) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                        (@Nat.le_of_lt (nat_lit 7) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                          (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))))))))))), axis := D5.S3.ConceptDynamics.CIRPT.PrimitiveAxis.cut, correct := by decide +kernel },
                  { index := by change Sum _ _; exact (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) (nat_lit 1)
            (@Nat.le_of_lt (nat_lit 2) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
              (@Nat.le_of_lt (nat_lit 3) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                (@Nat.le_of_lt (nat_lit 4) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                  (@Nat.le_of_lt (nat_lit 5) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                    (@Nat.le_of_lt (nat_lit 6) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                      (@Nat.le_of_lt (nat_lit 7) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                        (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))))))))))), axis := D5.S3.ConceptDynamics.CIRPT.PrimitiveAxis.cut, correct := by decide +kernel },
                  { index := by change Sum _ _; exact (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) (nat_lit 2)
            (@Nat.le_of_lt (nat_lit 3) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
              (@Nat.le_of_lt (nat_lit 4) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                (@Nat.le_of_lt (nat_lit 5) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                  (@Nat.le_of_lt (nat_lit 6) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                    (@Nat.le_of_lt (nat_lit 7) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                      (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))))))))), axis := D5.S3.ConceptDynamics.CIRPT.PrimitiveAxis.cut, correct := by decide +kernel },
                  { index := by change Sum _ _; exact (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) (nat_lit 3)
            (@Nat.le_of_lt (nat_lit 4) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
              (@Nat.le_of_lt (nat_lit 5) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                (@Nat.le_of_lt (nat_lit 6) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                  (@Nat.le_of_lt (nat_lit 7) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                    (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))))))))), axis := D5.S3.ConceptDynamics.CIRPT.PrimitiveAxis.cut, correct := by decide +kernel },
                  { index := by change Sum _ _; exact (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) (nat_lit 4)
            (@Nat.le_of_lt (nat_lit 5) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
              (@Nat.le_of_lt (nat_lit 6) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                (@Nat.le_of_lt (nat_lit 7) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                  (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))))))), axis := D5.S3.ConceptDynamics.CIRPT.PrimitiveAxis.cut, correct := by decide +kernel },
                  { index := by change Sum _ _; exact (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) (nat_lit 5)
            (@Nat.le_of_lt (nat_lit 6) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
              (@Nat.le_of_lt (nat_lit 7) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))))))), axis := D5.S3.ConceptDynamics.CIRPT.PrimitiveAxis.cut, correct := by decide +kernel },
                  { index := by change Sum _ _; exact (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) (nat_lit 6)
            (@Nat.le_of_lt (nat_lit 7) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
              (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))))), axis := D5.S3.ConceptDynamics.CIRPT.PrimitiveAxis.cut, correct := by decide +kernel },
                  { index := by change Sum _ _; exact (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) (nat_lit 7)
            (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))))), axis := D5.S3.ConceptDynamics.CIRPT.PrimitiveAxis.cut, correct := by decide +kernel }]
                nodup := by
                  change ([(@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) (nat_lit 0)
            (@Nat.le_of_lt (nat_lit 1) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
              (@Nat.le_of_lt (nat_lit 2) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                (@Nat.le_of_lt (nat_lit 3) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                  (@Nat.le_of_lt (nat_lit 4) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                    (@Nat.le_of_lt (nat_lit 5) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                      (@Nat.le_of_lt (nat_lit 6) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                        (@Nat.le_of_lt (nat_lit 7) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                          (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))))))))))), (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) (nat_lit 1)
            (@Nat.le_of_lt (nat_lit 2) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
              (@Nat.le_of_lt (nat_lit 3) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                (@Nat.le_of_lt (nat_lit 4) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                  (@Nat.le_of_lt (nat_lit 5) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                    (@Nat.le_of_lt (nat_lit 6) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                      (@Nat.le_of_lt (nat_lit 7) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                        (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))))))))))), (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) (nat_lit 2)
            (@Nat.le_of_lt (nat_lit 3) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
              (@Nat.le_of_lt (nat_lit 4) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                (@Nat.le_of_lt (nat_lit 5) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                  (@Nat.le_of_lt (nat_lit 6) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                    (@Nat.le_of_lt (nat_lit 7) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                      (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))))))))), (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) (nat_lit 3)
            (@Nat.le_of_lt (nat_lit 4) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
              (@Nat.le_of_lt (nat_lit 5) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                (@Nat.le_of_lt (nat_lit 6) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                  (@Nat.le_of_lt (nat_lit 7) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                    (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))))))))), (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) (nat_lit 4)
            (@Nat.le_of_lt (nat_lit 5) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
              (@Nat.le_of_lt (nat_lit 6) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                (@Nat.le_of_lt (nat_lit 7) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                  (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))))))), (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) (nat_lit 5)
            (@Nat.le_of_lt (nat_lit 6) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
              (@Nat.le_of_lt (nat_lit 7) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))))))), (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) (nat_lit 6)
            (@Nat.le_of_lt (nat_lit 7) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
              (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))))), (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) (nat_lit 7)
            (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))))] : List (Sum
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b)))).Nodup
                  letI : DecidableEq (Sum _ _) := (by change DecidableEq ((catalog_0.units (⟨0, by decide +kernel⟩ : Fin catalog_0.size)).primitives.Index); exact (catalog_0.units (⟨0, by decide +kernel⟩ : Fin catalog_0.size)).primitives.indexDecidableEq); letI : Fintype (Sum _ _) := (by change Fintype ((catalog_0.units (⟨0, by decide +kernel⟩ : Fin catalog_0.size)).primitives.Index); exact (catalog_0.units (⟨0, by decide +kernel⟩ : Fin catalog_0.size)).primitives.indexFintype)
                  apply of_decide_eq_true; decide +kernel
                complete := by
                  change ∀ i : (Sum
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))), i ∈ [(@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) (nat_lit 0)
            (@Nat.le_of_lt (nat_lit 1) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
              (@Nat.le_of_lt (nat_lit 2) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                (@Nat.le_of_lt (nat_lit 3) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                  (@Nat.le_of_lt (nat_lit 4) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                    (@Nat.le_of_lt (nat_lit 5) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                      (@Nat.le_of_lt (nat_lit 6) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                        (@Nat.le_of_lt (nat_lit 7) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                          (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))))))))))), (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) (nat_lit 1)
            (@Nat.le_of_lt (nat_lit 2) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
              (@Nat.le_of_lt (nat_lit 3) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                (@Nat.le_of_lt (nat_lit 4) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                  (@Nat.le_of_lt (nat_lit 5) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                    (@Nat.le_of_lt (nat_lit 6) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                      (@Nat.le_of_lt (nat_lit 7) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                        (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))))))))))), (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) (nat_lit 2)
            (@Nat.le_of_lt (nat_lit 3) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
              (@Nat.le_of_lt (nat_lit 4) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                (@Nat.le_of_lt (nat_lit 5) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                  (@Nat.le_of_lt (nat_lit 6) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                    (@Nat.le_of_lt (nat_lit 7) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                      (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))))))))), (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) (nat_lit 3)
            (@Nat.le_of_lt (nat_lit 4) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
              (@Nat.le_of_lt (nat_lit 5) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                (@Nat.le_of_lt (nat_lit 6) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                  (@Nat.le_of_lt (nat_lit 7) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                    (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))))))))), (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) (nat_lit 4)
            (@Nat.le_of_lt (nat_lit 5) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
              (@Nat.le_of_lt (nat_lit 6) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                (@Nat.le_of_lt (nat_lit 7) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                  (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))))))), (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) (nat_lit 5)
            (@Nat.le_of_lt (nat_lit 6) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
              (@Nat.le_of_lt (nat_lit 7) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))))))), (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) (nat_lit 6)
            (@Nat.le_of_lt (nat_lit 7) (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
              (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))))), (@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            Reg.Support.LegacyCausalCoordinates.objectArena.State
            (@Reg.Support.LegacyCausalSlots.signature Reg.Support.LegacyCausalCoordinates.UnifiedData (Option Bool) fun a b =>
              @Option.instDecidableEq Bool instDecidableEqBool a b))
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) (nat_lit 7)
            (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))))]
                  letI : DecidableEq (Sum _ _) := (by change DecidableEq ((catalog_0.units (⟨0, by decide +kernel⟩ : Fin catalog_0.size)).primitives.Index); exact (catalog_0.units (⟨0, by decide +kernel⟩ : Fin catalog_0.size)).primitives.indexDecidableEq); letI : Fintype (Sum _ _) := (by change Fintype ((catalog_0.units (⟨0, by decide +kernel⟩ : Fin catalog_0.size)).primitives.Index); exact (catalog_0.units (⟨0, by decide +kernel⟩ : Fin catalog_0.size)).primitives.indexFintype)
                  apply of_decide_eq_true; decide +kernel }
      partition := { rows := [{ item := (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.true
                 (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.true Bool.true)))), classId := 0 },
                       { item := (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.true
                 (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.true Bool.false)))), classId := 1 },
                       { item := (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.true
                 (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.false Bool.true)))), classId := 2 },
                       { item := (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.true
                 (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.false Bool.false)))), classId := 3 },
                       { item := (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.true
                 (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.true Bool.true)))), classId := 4 },
                       { item := (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.true
                 (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.true Bool.false)))), classId := 5 },
                       { item := (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.true
                 (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.false Bool.true)))), classId := 6 },
                       { item := (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.true
                 (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.false Bool.false)))), classId := 7 },
                       { item := (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.false
                 (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.true Bool.true)))), classId := 8 },
                       { item := (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.false
                 (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.true Bool.false)))), classId := 9 },
                       { item := (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.false
                 (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.false Bool.true)))), classId := 10 },
                       { item := (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.false
                 (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.false Bool.false)))), classId := 11 },
                       { item := (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.false
                 (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.true Bool.true)))), classId := 12 },
                       { item := (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.false
                 (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.true Bool.false)))), classId := 13 },
                       { item := (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.false
                 (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.false Bool.true)))), classId := 14 },
                       { item := (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.false
                 (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.false Bool.false)))), classId := 15 },
                       { item := (state_0), classId := 16 },
                       { item := (state_1), classId := 16 },
                       { item := (state_2), classId := 16 },
                       { item := (state_3), classId := 16 },
                       { item := (state_4), classId := 16 },
                       { item := (state_5), classId := 16 },
                       { item := (state_6), classId := 16 },
                       { item := (state_7), classId := 16 },
                       { item := (state_8), classId := 16 },
                       { item := (state_9), classId := 16 },
                       { item := (state_10), classId := 16 },
                       { item := (state_11), classId := 16 },
                       { item := (state_12), classId := 16 },
                       { item := (state_13), classId := 16 },
                       { item := (state_14), classId := 16 },
                       { item := (state_15), classId := 16 },
                       { item := (state_16), classId := 16 },
                       { item := (state_17), classId := 16 },
                       { item := (state_18), classId := 16 },
                       { item := (state_19), classId := 16 },
                       { item := (state_20), classId := 16 },
                       { item := (state_21), classId := 16 },
                       { item := (state_22), classId := 16 },
                       { item := (state_23), classId := 16 },
                       { item := (state_24), classId := 16 },
                       { item := (state_25), classId := 16 },
                       { item := (state_26), classId := 16 },
                       { item := (state_27), classId := 16 },
                       { item := (state_28), classId := 16 },
                       { item := (state_29), classId := 16 },
                       { item := (state_30), classId := 16 },
                       { item := (state_31), classId := 16 }]
                     nodup := by
                       letI := catalog_0.arena.stateDecidableEq; letI := catalog_0.arena.stateFintype
                       change ([(@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.true
                 (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.true Bool.true)))), (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.true
                 (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.true Bool.false)))), (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.true
                 (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.false Bool.true)))), (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.true
                 (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.false Bool.false)))), (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.true
                 (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.true Bool.true)))), (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.true
                 (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.true Bool.false)))), (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.true
                 (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.false Bool.true)))), (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.true
                 (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.false Bool.false)))), (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.false
                 (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.true Bool.true)))), (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.false
                 (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.true Bool.false)))), (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.false
                 (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.false Bool.true)))), (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.false
                 (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.false Bool.false)))), (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.false
                 (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.true Bool.true)))), (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.false
                 (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.true Bool.false)))), (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.false
                 (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.false Bool.true)))), (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.false
                 (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.false Bool.false)))), (state_0), (state_1), (state_2), (state_3), (state_4), (state_5), (state_6), (state_7), (state_8), (state_9), (state_10), (state_11), (state_12), (state_13), (state_14), (state_15), (state_16), (state_17), (state_18), (state_19), (state_20), (state_21), (state_22), (state_23), (state_24), (state_25), (state_26), (state_27), (state_28), (state_29), (state_30), (state_31)] : List (Sum Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData)).Nodup
                       apply of_decide_eq_true; decide +kernel
                     complete := by
                       letI := catalog_0.arena.stateDecidableEq; letI := catalog_0.arena.stateFintype
                       change ∀ x : (Sum Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData), x ∈ [(@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.true
                 (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.true Bool.true)))), (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.true
                 (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.true Bool.false)))), (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.true
                 (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.false Bool.true)))), (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.true
                 (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.false Bool.false)))), (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.true
                 (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.true Bool.true)))), (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.true
                 (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.true Bool.false)))), (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.true
                 (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.false Bool.true)))), (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.true
                 (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.false Bool.false)))), (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.false
                 (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.true Bool.true)))), (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.false
                 (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.true Bool.false)))), (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.false
                 (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.false Bool.true)))), (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.false
                 (@Prod.mk Bool (Prod Bool Bool) Bool.true (@Prod.mk Bool Bool Bool.false Bool.false)))), (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.false
                 (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.true Bool.true)))), (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.false
                 (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.true Bool.false)))), (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.false
                 (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.false Bool.true)))), (@Sum.inl Reg.Support.LegacyCausalCoordinates.ICData Reg.Support.LegacyCausalCoordinates.OIData
               (@Prod.mk Bool (Prod Bool (Prod Bool Bool)) Bool.false
                 (@Prod.mk Bool (Prod Bool Bool) Bool.false (@Prod.mk Bool Bool Bool.false Bool.false)))), (state_0), (state_1), (state_2), (state_3), (state_4), (state_5), (state_6), (state_7), (state_8), (state_9), (state_10), (state_11), (state_12), (state_13), (state_14), (state_15), (state_16), (state_17), (state_18), (state_19), (state_20), (state_21), (state_22), (state_23), (state_24), (state_25), (state_26), (state_27), (state_28), (state_29), (state_30), (state_31)]
                       apply of_decide_eq_true; decide +kernel
                     classes := by letI := catalog_0.arena.stateDecidableEq; letI := catalog_0.arena.stateFintype; apply of_decide_eq_true; decide +kernel }
      stateOrder := by rfl }

end Reg.Catalogs.SharedInformationRoot.SealedCatalog
