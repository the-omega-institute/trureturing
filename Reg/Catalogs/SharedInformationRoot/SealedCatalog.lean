import D5.S3.ConceptDynamics.Aggregation.AgendaPower
import D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause
import D5.S3.ConceptDynamics.CIRPT.PrimitiveKernel
import D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification
import D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange
import D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope
import D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign
import D5.S3.ConceptDynamics.Gluing.LocalLawGluingObstruction
import D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates
import D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates
import D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers
import D5.S3.ConceptDynamics.InformationEscape.SystemUnit
import D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange
import D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause
import D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas
import D5.S3.ConceptDynamics.InformationEscapeCounting.Fused
import D5.S3.ConceptDynamics.InformationEscapeRealizations.CommutingCompletionExchange
import D5.S3.ConceptDynamics.InformationEscapeRealizations.EndStateOmitsPreemptingCause
import D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint
import D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation
import D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Defs
import Reg.Support.LegacyAgenda
import Reg.Support.LegacyCausalCoordinates
import Reg.Support.LegacyCausalFinite
import Reg.Support.LegacyCausalSlots
import Reg.Support.LegacyContextReplacement
import Reg.Support.LegacyFiniteTransport
import Reg.Support.LegacyGluing
import Reg.Support.LegacyResidue
import Reg.Support.LegacySpectrum
import Reg.Support.LegacyStaticDesign
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
import Reg.Catalogs.InformationRoot
import Reg.Catalogs.InformationRoot.SealedCatalog
import Reg.Catalogs.UnifiedCausalRegistration


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
      enumeration := _root_.Reg.Support.LegacyCausalFinite.unifiedEnumeration
    }

noncomputable def facts_0 : Contract.SealFacts catalog_0 where
  units := { entries := [{ position := 0, within := by decide +kernel, item := (Reg.Support.LegacyCausalFinite.ic_bridge.toTheoremUnit
           D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.intervention_strictly_weaker_than_counterfactual), correct := by rfl }, { position := 1, within := by decide +kernel, item := (Reg.Support.LegacyCausalFinite.oi_bridge.toTheoremUnit
                                        D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.observation_strictly_weaker_than_intervention), correct := by rfl }]
             complete := rfl }

noncomputable def catalog_1 : Contract.SealCatalog := {
      arenaName := `Reg.Support.LegacyAgenda.arena
      catalogId := `Reg.Support.LegacyAgenda.arena
      arena := (_root_.Reg.Support.LegacyAgenda.arena).toArena
      size := 1
      units := ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.Reg.Support.LegacyAgenda.arena).toArena).stateDecidableEq (Reg.Support.LegacyAgenda.actual)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.Aggregation.AgendaPower.agenda_power) }]
      nondegenerate := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[0]'(by decide))).catalog.nondegenerate
      bundleNonempty := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[0]'(by decide))).catalog.bundleNonempty
      stateCard := 27
      stateCardEq := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[0]'(by decide))).catalog.stateCardEq
      full := 132
      fullEq := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[0]'(by decide))).catalog.fullEq
      rows := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[0]'(by decide))).catalog.rows
      collisions := #[]
      conclusion := .irredundant (by
        cases h : ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[0]'(by decide))).catalog.conclusion with
        | irredundant proof => exact proof
        | redundant _ => contradiction)
      enumeration := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[0]'(by decide))).catalog.enumeration
    }

noncomputable def facts_1 : Contract.SealFacts catalog_1 where
  units := { entries := [{ position := 0, within := by decide +kernel, item := (Reg.Support.LegacyAgenda.bridge.toTheoremUnit D5.S3.ConceptDynamics.Aggregation.AgendaPower.agenda_power), correct := by rfl }]
             complete := rfl }

noncomputable def catalog_2 : Contract.SealCatalog := {
      arenaName := `Reg.Support.LegacyCausalCoordinates.icObjectArena
      catalogId := `Reg.Support.LegacyCausalCoordinates.icObjectArena
      arena := (_root_.Reg.Support.LegacyCausalCoordinates.icObjectArena)
      size := 1
      units := ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.Reg.Support.LegacyCausalCoordinates.icObjectArena)).stateDecidableEq (Reg.Support.LegacyCausalFinite.localActual)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.intervention_strictly_weaker_than_counterfactual) }]
      nondegenerate := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[1]'(by decide))).catalog.nondegenerate
      bundleNonempty := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[1]'(by decide))).catalog.bundleNonempty
      stateCard := 16
      stateCardEq := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[1]'(by decide))).catalog.stateCardEq
      full := 0
      fullEq := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[1]'(by decide))).catalog.fullEq
      rows := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[1]'(by decide))).catalog.rows
      collisions := #[]
      conclusion := .irredundant (by
        cases h : ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[1]'(by decide))).catalog.conclusion with
        | irredundant proof => exact proof
        | redundant _ => contradiction)
      enumeration := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[1]'(by decide))).catalog.enumeration
    }

noncomputable def facts_2 : Contract.SealFacts catalog_2 where
  units := { entries := [{ position := 0, within := by decide +kernel, item := (Reg.Support.LegacyCausalFinite.local_bridge.toTheoremUnit
           D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.intervention_strictly_weaker_than_counterfactual), correct := by rfl }]
             complete := rfl }

noncomputable def catalog_3 : Contract.SealCatalog := {
      arenaName := `Reg.Support.LegacyContextReplacement.objectArena
      catalogId := `Reg.Support.LegacyContextReplacement.objectArena
      arena := (_root_.Reg.Support.LegacyContextReplacement.objectArena)
      size := 1
      units := ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.Reg.Support.LegacyContextReplacement.objectArena)).stateDecidableEq (Reg.Support.LegacyContextReplacement.actual)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint.context_parameters_can_select_distinct_fixed_points) }]
      nondegenerate := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[2]'(by decide))).catalog.nondegenerate
      bundleNonempty := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[2]'(by decide))).catalog.bundleNonempty
      stateCard := 8
      stateCardEq := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[2]'(by decide))).catalog.stateCardEq
      full := 0
      fullEq := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[2]'(by decide))).catalog.fullEq
      rows := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[2]'(by decide))).catalog.rows
      collisions := #[]
      conclusion := .irredundant (by
        cases h : ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[2]'(by decide))).catalog.conclusion with
        | irredundant proof => exact proof
        | redundant _ => contradiction)
      enumeration := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[2]'(by decide))).catalog.enumeration
    }

noncomputable def facts_3 : Contract.SealFacts catalog_3 where
  units := { entries := [{ position := 0, within := by decide +kernel, item := (Reg.Support.LegacyContextReplacement.bridge.toTheoremUnit
           D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint.context_parameters_can_select_distinct_fixed_points), correct := by rfl }]
             complete := rfl }

noncomputable def catalog_4 : Contract.SealCatalog := {
      arenaName := `Reg.Support.LegacyGluing.arena
      catalogId := `Reg.Support.LegacyGluing.arena
      arena := (_root_.Reg.Support.LegacyGluing.arena).toArena
      size := 1
      units := ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.Reg.Support.LegacyGluing.arena).toArena).stateDecidableEq (Reg.Support.LegacyGluing.actual)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.Gluing.LocalLawGluingObstruction.compatible_local_laws_can_lack_global_state) }]
      nondegenerate := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[3]'(by decide))).catalog.nondegenerate
      bundleNonempty := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[3]'(by decide))).catalog.bundleNonempty
      stateCard := 8
      stateCardEq := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[3]'(by decide))).catalog.stateCardEq
      full := 8
      fullEq := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[3]'(by decide))).catalog.fullEq
      rows := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[3]'(by decide))).catalog.rows
      collisions := #[]
      conclusion := .irredundant (by
        cases h : ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[3]'(by decide))).catalog.conclusion with
        | irredundant proof => exact proof
        | redundant _ => contradiction)
      enumeration := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[3]'(by decide))).catalog.enumeration
    }

noncomputable def facts_4 : Contract.SealFacts catalog_4 where
  units := { entries := [{ position := 0, within := by decide +kernel, item := (Reg.Support.LegacyGluing.bridge.toTheoremUnit
           D5.S3.ConceptDynamics.Gluing.LocalLawGluingObstruction.compatible_local_laws_can_lack_global_state), correct := by rfl }]
             complete := rfl }

noncomputable def catalog_5 : Contract.SealCatalog := {
      arenaName := `Reg.Support.LegacyResidue.arena
      catalogId := `Reg.Support.LegacyResidue.arena
      arena := (_root_.Reg.Support.LegacyResidue.arena).toArena
      size := 1
      units := ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.Reg.Support.LegacyResidue.arena).toArena).stateDecidableEq (Reg.Support.LegacyResidue.actual)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification.two_step_adaptive_residue_identification) }]
      nondegenerate := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[4]'(by decide))).catalog.nondegenerate
      bundleNonempty := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[4]'(by decide))).catalog.bundleNonempty
      stateCard := 4
      stateCardEq := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[4]'(by decide))).catalog.stateCardEq
      full := 0
      fullEq := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[4]'(by decide))).catalog.fullEq
      rows := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[4]'(by decide))).catalog.rows
      collisions := #[]
      conclusion := .irredundant (by
        cases h : ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[4]'(by decide))).catalog.conclusion with
        | irredundant proof => exact proof
        | redundant _ => contradiction)
      enumeration := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[4]'(by decide))).catalog.enumeration
    }

noncomputable def facts_5 : Contract.SealFacts catalog_5 where
  units := { entries := [{ position := 0, within := by decide +kernel, item := (Reg.Support.LegacyResidue.bridge.toTheoremUnit
           D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification.two_step_adaptive_residue_identification), correct := by rfl }]
             complete := rfl }

noncomputable def catalog_6 : Contract.SealCatalog := {
      arenaName := `Reg.Support.LegacyStaticDesign.arena
      catalogId := `Reg.Support.LegacyStaticDesign.arena
      arena := (_root_.Reg.Support.LegacyStaticDesign.arena).toArena
      size := 1
      units := ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.Reg.Support.LegacyStaticDesign.arena).toArena).stateDecidableEq (Reg.Support.LegacyStaticDesign.actual)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign.static_exact_design) }]
      nondegenerate := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[5]'(by decide))).catalog.nondegenerate
      bundleNonempty := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[5]'(by decide))).catalog.bundleNonempty
      stateCard := 3
      stateCardEq := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[5]'(by decide))).catalog.stateCardEq
      full := 0
      fullEq := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[5]'(by decide))).catalog.fullEq
      rows := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[5]'(by decide))).catalog.rows
      collisions := #[]
      conclusion := .irredundant (by
        cases h : ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[5]'(by decide))).catalog.conclusion with
        | irredundant proof => exact proof
        | redundant _ => contradiction)
      enumeration := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[5]'(by decide))).catalog.enumeration
    }

noncomputable def facts_6 : Contract.SealFacts catalog_6 where
  units := { entries := [{ position := 0, within := by decide +kernel, item := (Reg.Support.LegacyStaticDesign.bridge.toTheoremUnit
           D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign.static_exact_design), correct := by rfl }]
             complete := rfl }

noncomputable def catalog_7 : Contract.SealCatalog := {
      arenaName := `D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena
      catalogId := `D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena
      arena := (_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena)
      size := 1
      units := ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena)).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationRealization)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.observation_strictly_weaker_than_intervention) }]
      nondegenerate := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[6]'(by decide))).catalog.nondegenerate
      bundleNonempty := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[6]'(by decide))).catalog.bundleNonempty
      stateCard := 32
      stateCardEq := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[6]'(by decide))).catalog.stateCardEq
      full := 24
      fullEq := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[6]'(by decide))).catalog.fullEq
      rows := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[6]'(by decide))).catalog.rows
      collisions := #[]
      conclusion := .irredundant (by
        cases h : ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[6]'(by decide))).catalog.conclusion with
        | irredundant proof => exact proof
        | redundant _ => contradiction)
      enumeration := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[6]'(by decide))).catalog.enumeration
    }

noncomputable def facts_7 : Contract.SealFacts catalog_7 where
  units := { entries := [{ position := 0, within := by decide +kernel, item := (D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservation_bridge.toTheoremUnit
           D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.observation_strictly_weaker_than_intervention), correct := by rfl }]
             complete := rfl }

noncomputable def catalog_8 : Contract.SealCatalog := {
      arenaName := `D5.S3.ConceptDynamics.InformationEscape.SystemUnit.arena
      catalogId := `D5.S3.ConceptDynamics.InformationEscape.SystemUnit.arena
      arena := (_root_.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.arena).toArena
      size := 1
      units := ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.arena).toArena).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscape.SystemUnit.systemRealization)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.engine_census_self_application) }]
      nondegenerate := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[7]'(by decide))).catalog.nondegenerate
      bundleNonempty := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[7]'(by decide))).catalog.bundleNonempty
      stateCard := 2
      stateCardEq := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[7]'(by decide))).catalog.stateCardEq
      full := 0
      fullEq := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[7]'(by decide))).catalog.fullEq
      rows := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[7]'(by decide))).catalog.rows
      collisions := #[]
      conclusion := .irredundant (by
        cases h : ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[7]'(by decide))).catalog.conclusion with
        | irredundant proof => exact proof
        | redundant _ => contradiction)
      enumeration := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[7]'(by decide))).catalog.enumeration
    }

noncomputable def facts_8 : Contract.SealFacts catalog_8 where
  units := { entries := [{ position := 0, within := by decide +kernel, item := (D5.S3.ConceptDynamics.InformationEscape.SystemUnit.system_self_application_realization.toTheoremUnit
           D5.S3.ConceptDynamics.InformationEscape.SystemUnit.engine_census_self_application), correct := by rfl }]
             complete := rfl }

noncomputable def catalog_9 : Contract.SealCatalog := {
      arenaName := `D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.commutingCompletionArena
      catalogId := `D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.commutingCompletionArena
      arena := (_root_.D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.commutingCompletionArena).toArena
      size := 1
      units := ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.commutingCompletionArena).toArena).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscapeRealizations.CommutingCompletionExchange.commutingCompletionRealization)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.commutativity_hypothesis_is_necessary) }]
      nondegenerate := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[8]'(by decide))).catalog.nondegenerate
      bundleNonempty := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[8]'(by decide))).catalog.bundleNonempty
      stateCard := 4
      stateCardEq := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[8]'(by decide))).catalog.stateCardEq
      full := 0
      fullEq := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[8]'(by decide))).catalog.fullEq
      rows := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[8]'(by decide))).catalog.rows
      collisions := #[]
      conclusion := .irredundant (by
        cases h : ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[8]'(by decide))).catalog.conclusion with
        | irredundant proof => exact proof
        | redundant _ => contradiction)
      enumeration := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[8]'(by decide))).catalog.enumeration
    }

noncomputable def facts_9 : Contract.SealFacts catalog_9 where
  units := { entries := [{ position := 0, within := by decide +kernel, item := (D5.S3.ConceptDynamics.InformationEscapeRealizations.CommutingCompletionExchange.commutativity_hypothesis_is_necessary_realization.toTheoremUnit
           D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.commutativity_hypothesis_is_necessary), correct := by rfl }]
             complete := rfl }

noncomputable def catalog_10 : Contract.SealCatalog := {
      arenaName := `D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena
      catalogId := `D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena
      arena := (_root_.D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena).toArena
      size := 1
      units := ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena).toArena).stateDecidableEq (D5.S3.ConceptDynamics.InformationEscapeRealizations.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseRealization)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.end_state_omits_preempting_cause) }]
      nondegenerate := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[9]'(by decide))).catalog.nondegenerate
      bundleNonempty := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[9]'(by decide))).catalog.bundleNonempty
      stateCard := 9
      stateCardEq := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[9]'(by decide))).catalog.stateCardEq
      full := 12
      fullEq := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[9]'(by decide))).catalog.fullEq
      rows := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[9]'(by decide))).catalog.rows
      collisions := #[]
      conclusion := .irredundant (by
        cases h : ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[9]'(by decide))).catalog.conclusion with
        | irredundant proof => exact proof
        | redundant _ => contradiction)
      enumeration := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[9]'(by decide))).catalog.enumeration
    }

noncomputable def facts_10 : Contract.SealFacts catalog_10 where
  units := { entries := [{ position := 0, within := by decide +kernel, item := (D5.S3.ConceptDynamics.InformationEscapeRealizations.EndStateOmitsPreemptingCause.end_state_omits_preempting_cause_realization.toTheoremUnit
           D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.end_state_omits_preempting_cause), correct := by rfl }]
             complete := rfl }

noncomputable def catalog_11 : Contract.SealCatalog := {
      arenaName := `D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.spectrumArena
      catalogId := `D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.spectrumArena
      arena := (_root_.D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.spectrumArena).toArena
      size := 1
      units := ![{ primitives := (@_root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle _ _ ((_root_.D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.spectrumArena).toArena).stateDecidableEq (@D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates.cutRealization D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.SpectrumAtom (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) fun (atom : D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.SpectrumAtom) => Reg.Support.LegacySpectrum.indexReadout atom)), Statement := _, proof := (@_root_.D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.spectrum_atom_index_bijective) }]
      nondegenerate := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[10]'(by decide))).catalog.nondegenerate
      bundleNonempty := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[10]'(by decide))).catalog.bundleNonempty
      stateCard := 5
      stateCardEq := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[10]'(by decide))).catalog.stateCardEq
      full := 0
      fullEq := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[10]'(by decide))).catalog.fullEq
      rows := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[10]'(by decide))).catalog.rows
      collisions := #[]
      conclusion := .irredundant (by
        cases h : ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[10]'(by decide))).catalog.conclusion with
        | irredundant proof => exact proof
        | redundant _ => contradiction)
      enumeration := ((_root_.Reg.Catalogs.InformationRoot.SealedCatalog.seal.catalogs[10]'(by decide))).catalog.enumeration
    }

noncomputable def facts_11 : Contract.SealFacts catalog_11 where
  units := { entries := [{ position := 0, within := by decide +kernel, item := (Reg.Support.LegacySpectrum.bridge.toTheoremUnit
           D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.spectrum_atom_index_bijective), correct := by rfl }]
             complete := rfl }

def rootCatalog : Contract.RootCatalog := { data := {
  rootId := `Reg.Catalogs.SharedInformationRoot.SealedCatalog,
  expected := #[{ statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.engine_census_self_application), theoremName := `D5.S3.ConceptDynamics.InformationEscape.SystemUnit.engine_census_self_application, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.SystemUnit.arena, statementIdentity := some "sha256:a3a2c21de13a5366dbb0d8ab39bc747e95b22c7cbeecb7ef39d86092b4c70ab0", registrationModuleName := `Reg.D5.S3.ConceptDynamics.InformationEscape.SystemUnit },
    { statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.commutativity_hypothesis_is_necessary), theoremName := `D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.commutativity_hypothesis_is_necessary, objectArenaName := `D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.commutingCompletionArena, statementIdentity := some "sha256:1aed443dafdf76d41d4cca3a5a8bbf76e5a0f33e4a90453061b57fc3f432fb0a", registrationModuleName := `Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.InformationRoot },
    { statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.end_state_omits_preempting_cause), theoremName := `D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.end_state_omits_preempting_cause, objectArenaName := `D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena, statementIdentity := some "sha256:b93e6bd918cabb38e32a21f11542a80c47dcc6ba73bdeac72336a5c75648c24c", registrationModuleName := `Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.InformationRoot },
    { statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.Aggregation.AgendaPower.agenda_power), theoremName := `D5.S3.ConceptDynamics.Aggregation.AgendaPower.agenda_power, objectArenaName := `Reg.Support.LegacyAgenda.arena, statementIdentity := some "sha256:384a1edc32c16ec0b4045c373ce00d995b3fa571bb9cbf36960355b33a93cc00", registrationModuleName := `Reg.D5.S3.ConceptDynamics.Aggregation.AgendaPower.InformationRoot },
    { statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification.two_step_adaptive_residue_identification), theoremName := `D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification.two_step_adaptive_residue_identification, objectArenaName := `Reg.Support.LegacyResidue.arena, statementIdentity := some "sha256:6f8434c94b05962f830bd9c47522da114d168db8b17fa7825970bf48a600b9e6", registrationModuleName := `Reg.D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification.InformationRoot },
    { statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.spectrum_atom_index_bijective), theoremName := `D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.spectrum_atom_index_bijective, objectArenaName := `D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.spectrumArena, statementIdentity := some "sha256:970d0c4dbc3081113fb682ad75b2e6ee7f11e8330ded5624aa79599b799b76b3", registrationModuleName := `Reg.D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.InformationRoot },
    { statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint.context_parameters_can_select_distinct_fixed_points), theoremName := `D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint.context_parameters_can_select_distinct_fixed_points, objectArenaName := `Reg.Support.LegacyContextReplacement.objectArena, statementIdentity := some "sha256:778398ffe72817b135e29453ae9a3b796de14383670686abbf230840cb7ee515", registrationModuleName := `Reg.D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint.InformationRoot },
    { statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.intervention_strictly_weaker_than_counterfactual), theoremName := `D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.intervention_strictly_weaker_than_counterfactual, objectArenaName := `Reg.Support.LegacyCausalCoordinates.icObjectArena, statementIdentity := some "sha256:fd8c5bad3c9b38d167e59ff3889f6897c82fdd7070d8feaae13528062ac13140", registrationModuleName := `Reg.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.InformationRoot },
    { statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.Gluing.LocalLawGluingObstruction.compatible_local_laws_can_lack_global_state), theoremName := `D5.S3.ConceptDynamics.Gluing.LocalLawGluingObstruction.compatible_local_laws_can_lack_global_state, objectArenaName := `Reg.Support.LegacyGluing.arena, statementIdentity := some "sha256:95b576248df546ed3529c83c5c171a1ab2f6cff8fd9f78d7db83204dd4ecfb56", registrationModuleName := `Reg.D5.S3.ConceptDynamics.Gluing.LocalLawGluingObstruction.InformationRoot },
    { statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.observation_strictly_weaker_than_intervention), theoremName := `D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.observation_strictly_weaker_than_intervention, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena, statementIdentity := some "sha256:65c74f1a6b6342639e4c773a4de5bbcd925ebae300eebf640b0cab6f5e4b2984", registrationModuleName := `Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.InformationRoot },
    { statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign.static_exact_design), theoremName := `D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign.static_exact_design, objectArenaName := `Reg.Support.LegacyStaticDesign.arena, statementIdentity := some "sha256:408742a2c71557575944155350def43ed8f9f37ec3a19fe75f721e084dfe939a", registrationModuleName := `Reg.D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign.InformationRoot },
    { statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.intervention_strictly_weaker_than_counterfactual), theoremName := `D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.intervention_strictly_weaker_than_counterfactual, objectArenaName := `Reg.Support.LegacyCausalCoordinates.objectArena, statementIdentity := some "sha256:fd8c5bad3c9b38d167e59ff3889f6897c82fdd7070d8feaae13528062ac13140", registrationModuleName := `Reg.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.UnifiedCausalRegistration },
    { statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.observation_strictly_weaker_than_intervention), theoremName := `D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.observation_strictly_weaker_than_intervention, objectArenaName := `Reg.Support.LegacyCausalCoordinates.objectArena, statementIdentity := some "sha256:65c74f1a6b6342639e4c773a4de5bbcd925ebae300eebf640b0cab6f5e4b2984", registrationModuleName := `Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.UnifiedCausalRegistration }],
  source := #[{ statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.engine_census_self_application), theoremName := `D5.S3.ConceptDynamics.InformationEscape.SystemUnit.engine_census_self_application, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.SystemUnit.arena, statementIdentity := some "sha256:a3a2c21de13a5366dbb0d8ab39bc747e95b22c7cbeecb7ef39d86092b4c70ab0", registrationModuleName := `Reg.D5.S3.ConceptDynamics.InformationEscape.SystemUnit },
    { statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.commutativity_hypothesis_is_necessary), theoremName := `D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.commutativity_hypothesis_is_necessary, objectArenaName := `D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.commutingCompletionArena, statementIdentity := some "sha256:1aed443dafdf76d41d4cca3a5a8bbf76e5a0f33e4a90453061b57fc3f432fb0a", registrationModuleName := `Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.InformationRoot },
    { statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.end_state_omits_preempting_cause), theoremName := `D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.end_state_omits_preempting_cause, objectArenaName := `D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena, statementIdentity := some "sha256:b93e6bd918cabb38e32a21f11542a80c47dcc6ba73bdeac72336a5c75648c24c", registrationModuleName := `Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.InformationRoot },
    { statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.Aggregation.AgendaPower.agenda_power), theoremName := `D5.S3.ConceptDynamics.Aggregation.AgendaPower.agenda_power, objectArenaName := `Reg.Support.LegacyAgenda.arena, statementIdentity := some "sha256:384a1edc32c16ec0b4045c373ce00d995b3fa571bb9cbf36960355b33a93cc00", registrationModuleName := `Reg.D5.S3.ConceptDynamics.Aggregation.AgendaPower.InformationRoot },
    { statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification.two_step_adaptive_residue_identification), theoremName := `D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification.two_step_adaptive_residue_identification, objectArenaName := `Reg.Support.LegacyResidue.arena, statementIdentity := some "sha256:6f8434c94b05962f830bd9c47522da114d168db8b17fa7825970bf48a600b9e6", registrationModuleName := `Reg.D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification.InformationRoot },
    { statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.spectrum_atom_index_bijective), theoremName := `D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.spectrum_atom_index_bijective, objectArenaName := `D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.spectrumArena, statementIdentity := some "sha256:970d0c4dbc3081113fb682ad75b2e6ee7f11e8330ded5624aa79599b799b76b3", registrationModuleName := `Reg.D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.InformationRoot },
    { statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint.context_parameters_can_select_distinct_fixed_points), theoremName := `D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint.context_parameters_can_select_distinct_fixed_points, objectArenaName := `Reg.Support.LegacyContextReplacement.objectArena, statementIdentity := some "sha256:778398ffe72817b135e29453ae9a3b796de14383670686abbf230840cb7ee515", registrationModuleName := `Reg.D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint.InformationRoot },
    { statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.intervention_strictly_weaker_than_counterfactual), theoremName := `D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.intervention_strictly_weaker_than_counterfactual, objectArenaName := `Reg.Support.LegacyCausalCoordinates.icObjectArena, statementIdentity := some "sha256:fd8c5bad3c9b38d167e59ff3889f6897c82fdd7070d8feaae13528062ac13140", registrationModuleName := `Reg.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.InformationRoot },
    { statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.Gluing.LocalLawGluingObstruction.compatible_local_laws_can_lack_global_state), theoremName := `D5.S3.ConceptDynamics.Gluing.LocalLawGluingObstruction.compatible_local_laws_can_lack_global_state, objectArenaName := `Reg.Support.LegacyGluing.arena, statementIdentity := some "sha256:95b576248df546ed3529c83c5c171a1ab2f6cff8fd9f78d7db83204dd4ecfb56", registrationModuleName := `Reg.D5.S3.ConceptDynamics.Gluing.LocalLawGluingObstruction.InformationRoot },
    { statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.observation_strictly_weaker_than_intervention), theoremName := `D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.observation_strictly_weaker_than_intervention, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena, statementIdentity := some "sha256:65c74f1a6b6342639e4c773a4de5bbcd925ebae300eebf640b0cab6f5e4b2984", registrationModuleName := `Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.InformationRoot },
    { statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign.static_exact_design), theoremName := `D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign.static_exact_design, objectArenaName := `Reg.Support.LegacyStaticDesign.arena, statementIdentity := some "sha256:408742a2c71557575944155350def43ed8f9f37ec3a19fe75f721e084dfe939a", registrationModuleName := `Reg.D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign.InformationRoot },
    { statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.intervention_strictly_weaker_than_counterfactual), theoremName := `D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.intervention_strictly_weaker_than_counterfactual, objectArenaName := `Reg.Support.LegacyCausalCoordinates.objectArena, statementIdentity := some "sha256:fd8c5bad3c9b38d167e59ff3889f6897c82fdd7070d8feaae13528062ac13140", registrationModuleName := `Reg.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.UnifiedCausalRegistration },
    { statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.observation_strictly_weaker_than_intervention), theoremName := `D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.observation_strictly_weaker_than_intervention, objectArenaName := `Reg.Support.LegacyCausalCoordinates.objectArena, statementIdentity := some "sha256:65c74f1a6b6342639e4c773a4de5bbcd925ebae300eebf640b0cab6f5e4b2984", registrationModuleName := `Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.UnifiedCausalRegistration }],
  baseline := #[{ statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.engine_census_self_application), theoremName := `D5.S3.ConceptDynamics.InformationEscape.SystemUnit.engine_census_self_application, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.SystemUnit.arena, statementIdentity := some "sha256:a3a2c21de13a5366dbb0d8ab39bc747e95b22c7cbeecb7ef39d86092b4c70ab0", registrationModuleName := `Reg.D5.S3.ConceptDynamics.InformationEscape.SystemUnit },
    { statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.commutativity_hypothesis_is_necessary), theoremName := `D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.commutativity_hypothesis_is_necessary, objectArenaName := `D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.commutingCompletionArena, statementIdentity := some "sha256:1aed443dafdf76d41d4cca3a5a8bbf76e5a0f33e4a90453061b57fc3f432fb0a", registrationModuleName := `Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.InformationRoot },
    { statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.end_state_omits_preempting_cause), theoremName := `D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.end_state_omits_preempting_cause, objectArenaName := `D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena, statementIdentity := some "sha256:b93e6bd918cabb38e32a21f11542a80c47dcc6ba73bdeac72336a5c75648c24c", registrationModuleName := `Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.InformationRoot },
    { statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.Aggregation.AgendaPower.agenda_power), theoremName := `D5.S3.ConceptDynamics.Aggregation.AgendaPower.agenda_power, objectArenaName := `Reg.Support.LegacyAgenda.arena, statementIdentity := some "sha256:384a1edc32c16ec0b4045c373ce00d995b3fa571bb9cbf36960355b33a93cc00", registrationModuleName := `Reg.D5.S3.ConceptDynamics.Aggregation.AgendaPower.InformationRoot },
    { statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification.two_step_adaptive_residue_identification), theoremName := `D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification.two_step_adaptive_residue_identification, objectArenaName := `Reg.Support.LegacyResidue.arena, statementIdentity := some "sha256:6f8434c94b05962f830bd9c47522da114d168db8b17fa7825970bf48a600b9e6", registrationModuleName := `Reg.D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification.InformationRoot },
    { statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.spectrum_atom_index_bijective), theoremName := `D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.spectrum_atom_index_bijective, objectArenaName := `D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.spectrumArena, statementIdentity := some "sha256:970d0c4dbc3081113fb682ad75b2e6ee7f11e8330ded5624aa79599b799b76b3", registrationModuleName := `Reg.D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.InformationRoot },
    { statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint.context_parameters_can_select_distinct_fixed_points), theoremName := `D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint.context_parameters_can_select_distinct_fixed_points, objectArenaName := `Reg.Support.LegacyContextReplacement.objectArena, statementIdentity := some "sha256:778398ffe72817b135e29453ae9a3b796de14383670686abbf230840cb7ee515", registrationModuleName := `Reg.D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint.InformationRoot },
    { statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.intervention_strictly_weaker_than_counterfactual), theoremName := `D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.intervention_strictly_weaker_than_counterfactual, objectArenaName := `Reg.Support.LegacyCausalCoordinates.icObjectArena, statementIdentity := some "sha256:fd8c5bad3c9b38d167e59ff3889f6897c82fdd7070d8feaae13528062ac13140", registrationModuleName := `Reg.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.InformationRoot },
    { statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.Gluing.LocalLawGluingObstruction.compatible_local_laws_can_lack_global_state), theoremName := `D5.S3.ConceptDynamics.Gluing.LocalLawGluingObstruction.compatible_local_laws_can_lack_global_state, objectArenaName := `Reg.Support.LegacyGluing.arena, statementIdentity := some "sha256:95b576248df546ed3529c83c5c171a1ab2f6cff8fd9f78d7db83204dd4ecfb56", registrationModuleName := `Reg.D5.S3.ConceptDynamics.Gluing.LocalLawGluingObstruction.InformationRoot },
    { statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.observation_strictly_weaker_than_intervention), theoremName := `D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.observation_strictly_weaker_than_intervention, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena, statementIdentity := some "sha256:65c74f1a6b6342639e4c773a4de5bbcd925ebae300eebf640b0cab6f5e4b2984", registrationModuleName := `Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.InformationRoot },
    { statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign.static_exact_design), theoremName := `D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign.static_exact_design, objectArenaName := `Reg.Support.LegacyStaticDesign.arena, statementIdentity := some "sha256:408742a2c71557575944155350def43ed8f9f37ec3a19fe75f721e084dfe939a", registrationModuleName := `Reg.D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign.InformationRoot }],
  companionPrefix := some `Reg.Catalogs.SharedInformationRoot } }

noncomputable def view_0 : Contract.SealCatalogView := { catalog := catalog_0, facts := facts_0 }

noncomputable def view_1 : Contract.SealCatalogView := { catalog := catalog_1, facts := facts_1 }

noncomputable def view_2 : Contract.SealCatalogView := { catalog := catalog_2, facts := facts_2 }

noncomputable def view_3 : Contract.SealCatalogView := { catalog := catalog_3, facts := facts_3 }

noncomputable def view_4 : Contract.SealCatalogView := { catalog := catalog_4, facts := facts_4 }

noncomputable def view_5 : Contract.SealCatalogView := { catalog := catalog_5, facts := facts_5 }

noncomputable def view_6 : Contract.SealCatalogView := { catalog := catalog_6, facts := facts_6 }

noncomputable def view_7 : Contract.SealCatalogView := { catalog := catalog_7, facts := facts_7 }

noncomputable def view_8 : Contract.SealCatalogView := { catalog := catalog_8, facts := facts_8 }

noncomputable def view_9 : Contract.SealCatalogView := { catalog := catalog_9, facts := facts_9 }

noncomputable def view_10 : Contract.SealCatalogView := { catalog := catalog_10, facts := facts_10 }

noncomputable def view_11 : Contract.SealCatalogView := { catalog := catalog_11, facts := facts_11 }

noncomputable def «seal» : Contract.Seal := {
  rootId := `Reg.Catalogs.SharedInformationRoot.SealedCatalog
  catalogs := #[
    view_0,
    view_1,
    view_2,
    view_3,
    view_4,
    view_5,
    view_6,
    view_7,
    view_8,
    view_9,
    view_10,
    view_11
  ]
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxHeartbeats, value := .nat 2000000 }, { name := `maxRecDepth, value := .nat 100000 }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }

end Reg.Catalogs.SharedInformationRoot.SealedCatalog
