import Mathlib.Data.Fin.VecNotation
import LeanInformationAuditInterface.Contract.Catalog
import D5.S3.ConceptDynamics.CIRPT.PrimitiveKernel
import D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope
import D5.S3.ConceptDynamics.InformationEscape.ExactRate
import D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas
import Reg.Catalogs.InformationRoot.SealData.Data2
import Reg.Support.LegacySpectrum

namespace Reg.Catalogs.InformationRoot.SealedCatalog
open LeanInformationAudit

noncomputable def facts_10 : Contract.SealFacts catalog_10 where
  units := { entries := [{ position := 0, within := by decide +kernel, item := (Reg.Support.LegacySpectrum.bridge.toTheoremUnit
           D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.spectrum_atom_index_bijective), correct := by rfl }]
             complete := rfl }
  rows := [{
      position := 0
      within := by decide +kernel
      row := {
        unique := 20
        uniqueEq := ((catalog_10.rows (⟨0, by decide +kernel⟩ : Fin catalog_10.size)).uniqueEq).trans (by rfl)
        without := 20
        withoutEq := ((catalog_10.rows (⟨0, by decide +kernel⟩ : Fin catalog_10.size)).withoutEq).trans (by rfl)
        roleBins := ![0, 0, 0, 0, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0]
        roleEq := by intro bucket; exact ((catalog_10.rows (⟨0, by decide +kernel⟩ : Fin catalog_10.size)).roleEq bucket).trans (congrFun (by rfl : (catalog_10.rows (⟨0, by decide +kernel⟩ : Fin catalog_10.size)).roleBins = ![0, 0, 0, 0, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0]) bucket)
        roleTotal := by decide +kernel
        conclusion := .positive (by decide +kernel) (by
          apply (D5.S3.ConceptDynamics.InformationEscape.Catalog.lowersEscape_iff_uniqueCaptureCount_pos _ _ catalog_10.nondegenerate).mpr
          rw [(catalog_10.rows (⟨0, by decide +kernel⟩ : Fin catalog_10.size)).uniqueEq]
          decide +kernel) }
      correct := by rfl
      bins := { entries := [{ position := 0, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 1, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 2, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 3, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 4, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 5, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 6, within := by decide +kernel, item := 0, correct := by decide +kernel },
                  { position := 7, within := by decide +kernel, item := 20, correct := by decide +kernel },
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
                D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.spectrumArena.State
                (@D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates.cutSignature
                  D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.SpectrumAtom
                  (Fin (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                  (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))))
              (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
                D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.spectrumArena.State
                (@D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates.cutSignature
                  D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.SpectrumAtom
                  (Fin (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                  (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))))
              PUnit.unit), axis := D5.S3.ConceptDynamics.CIRPT.PrimitiveAxis.cut, correct := by decide +kernel }]
                nodup := by
                  change ([(@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.spectrumArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates.cutSignature
              D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.SpectrumAtom
              (Fin (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.spectrumArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates.cutSignature
              D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.SpectrumAtom
              (Fin (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))))
          PUnit.unit)] : List (Sum
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.spectrumArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates.cutSignature
              D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.SpectrumAtom
              (Fin (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.spectrumArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates.cutSignature
              D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.SpectrumAtom
              (Fin (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))))).Nodup
                  letI : DecidableEq (Sum _ _) := (by change DecidableEq ((catalog_10.units (⟨0, by decide +kernel⟩ : Fin catalog_10.size)).primitives.Index); exact (catalog_10.units (⟨0, by decide +kernel⟩ : Fin catalog_10.size)).primitives.indexDecidableEq); letI : Fintype (Sum _ _) := (by change Fintype ((catalog_10.units (⟨0, by decide +kernel⟩ : Fin catalog_10.size)).primitives.Index); exact (catalog_10.units (⟨0, by decide +kernel⟩ : Fin catalog_10.size)).primitives.indexFintype)
                  apply of_decide_eq_true; decide +kernel
                complete := by
                  change ∀ i : (Sum
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.spectrumArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates.cutSignature
              D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.SpectrumAtom
              (Fin (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.spectrumArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates.cutSignature
              D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.SpectrumAtom
              (Fin (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))))), i ∈ [(@Sum.inl
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index
            D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.spectrumArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates.cutSignature
              D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.SpectrumAtom
              (Fin (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))))
          (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.AnchorIndex
            D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.spectrumArena.State
            (@D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates.cutSignature
              D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.SpectrumAtom
              (Fin (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))))
          PUnit.unit)]
                  letI : DecidableEq (Sum _ _) := (by change DecidableEq ((catalog_10.units (⟨0, by decide +kernel⟩ : Fin catalog_10.size)).primitives.Index); exact (catalog_10.units (⟨0, by decide +kernel⟩ : Fin catalog_10.size)).primitives.indexDecidableEq); letI : Fintype (Sum _ _) := (by change Fintype ((catalog_10.units (⟨0, by decide +kernel⟩ : Fin catalog_10.size)).primitives.Index); exact (catalog_10.units (⟨0, by decide +kernel⟩ : Fin catalog_10.size)).primitives.indexFintype)
                  apply of_decide_eq_true; decide +kernel }
      partition := { rows := [{ item := (D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.SpectrumAtom.t1), classId := 0 },
                       { item := (D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.SpectrumAtom.t2), classId := 1 },
                       { item := (D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.SpectrumAtom.t3), classId := 2 },
                       { item := (D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.SpectrumAtom.t4), classId := 3 },
                       { item := (D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.SpectrumAtom.t5), classId := 4 }]
                     nodup := by
                       letI := catalog_10.arena.stateDecidableEq; letI := catalog_10.arena.stateFintype
                       change ([(D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.SpectrumAtom.t1), (D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.SpectrumAtom.t2), (D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.SpectrumAtom.t3), (D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.SpectrumAtom.t4), (D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.SpectrumAtom.t5)] : List (D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.SpectrumAtom)).Nodup
                       apply of_decide_eq_true; decide +kernel
                     complete := by
                       letI := catalog_10.arena.stateDecidableEq; letI := catalog_10.arena.stateFintype
                       change ∀ x : (D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.SpectrumAtom), x ∈ [(D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.SpectrumAtom.t1), (D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.SpectrumAtom.t2), (D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.SpectrumAtom.t3), (D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.SpectrumAtom.t4), (D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.SpectrumAtom.t5)]
                       apply of_decide_eq_true; decide +kernel
                     classes := by letI := catalog_10.arena.stateDecidableEq; letI := catalog_10.arena.stateFintype; apply of_decide_eq_true; decide +kernel }
      stateOrder := by rfl }]
  complete := rfl

end Reg.Catalogs.InformationRoot.SealedCatalog
