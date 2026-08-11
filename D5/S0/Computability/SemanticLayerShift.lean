/- GID: D5/S0/Computability/SemanticLayerShift
   generality: G
   mirror-B: D5/B/S0/Computability/SemanticLayerShift
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A traceable semantic entry shifts losslessly to an open entry at the next layer. -/

import D5.S0.History.ResidualLedger
import Mathlib.Logic.Equiv.Basic

/- Provenance: the source atom supplies the typed layer transition. Pinned
   Mathlib supplies the status transposition and subtype restriction
   (`Equiv.swap`, `Equiv.subtypeEquiv`) and the final bijectivity theorem
   (`Equiv.bijective`). -/

namespace D5.S0.Computability.SemanticLayerShift

open D5.S0.History.ResidualLedger

/-- Entries whose current-layer readout has a semantic type mismatch. -/
abbrev SemanticEntry (Source Detector NextAction : Type*) :=
  {entry : ResidualLedgerEntry Source Detector NextAction //
    entry.status = .semantic}

/-- Entries reopened for certification at the next layer. -/
abbrev OpenEntry (Source Detector NextAction : Type*) :=
  {entry : ResidualLedgerEntry Source Detector NextAction //
    entry.status = .open_}

/-- Exchange the current-layer semantic status with the next-layer open
status, leaving closed and tail entries fixed. -/
def residualStatusShift : Equiv.Perm ResidualStatus :=
  Equiv.swap .semantic .open_

/-- Apply lossless component translations and the semantic-to-open status
change to a residual-ledger entry. -/
def residualEntryShiftEquiv
    {Source₀ Source₁ Detector₀ Detector₁ NextAction₀ NextAction₁ : Type*}
    (source : Source₀ ≃ Source₁) (detector : Detector₀ ≃ Detector₁)
    (nextAction : NextAction₀ ≃ NextAction₁) :
    ResidualLedgerEntry Source₀ Detector₀ NextAction₀ ≃
      ResidualLedgerEntry Source₁ Detector₁ NextAction₁ :=
  (residualLedgerEquivComponents Source₀ Detector₀ NextAction₀).trans
    ((source.prodCongr
      (detector.prodCongr (residualStatusShift.prodCongr nextAction))).trans
        (residualLedgerEquivComponents Source₁ Detector₁ NextAction₁).symm)

/-- A traceable layer shift is an equivalence from semantic entries at the
current layer to open entries at the next layer. The component equivalences
preserve source provenance while translating the detector and future budget. -/
def semanticLayerShiftEquiv
    {Source₀ Source₁ Detector₀ Detector₁ NextAction₀ NextAction₁ : Type*}
    (source : Source₀ ≃ Source₁) (detector : Detector₀ ≃ Detector₁)
    (nextAction : NextAction₀ ≃ NextAction₁) :
    SemanticEntry Source₀ Detector₀ NextAction₀ ≃
      OpenEntry Source₁ Detector₁ NextAction₁ :=
  (residualEntryShiftEquiv source detector nextAction).subtypeEquiv fun entry => by
    cases entry with
    | mk sourceValue detectorValue status nextActionValue =>
        cases status <;>
          simp [residualEntryShiftEquiv, residualStatusShift,
            residualLedgerEquivComponents, Equiv.swap_apply_def]

/-- The typed semantic-to-open layer shift loses no ledger entry and creates
no duplicate: it is both injective and surjective. -/
theorem semantic_layer_shift_bijective
    {Source₀ Source₁ Detector₀ Detector₁ NextAction₀ NextAction₁ : Type*}
    (source : Source₀ ≃ Source₁) (detector : Detector₀ ≃ Detector₁)
    (nextAction : NextAction₀ ≃ NextAction₁) :
    Function.Bijective (semanticLayerShiftEquiv source detector nextAction) :=
  (semanticLayerShiftEquiv source detector nextAction).bijective

end D5.S0.Computability.SemanticLayerShift
