/- GID: D5/S0/History/ResidualLedger
   generality: G
   mirror-B: D5/B/S0/History/ResidualLedger
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Residual ledger entries are losslessly equivalent to their four typed components. -/

import D5.S0.History.ResidualLedger.Native
import OmegaMath.Data.Product
import OmegaMathlib.Logic.Function.Defs

/-! The typed components and lossless encodings of a residual-ledger entry. -/

namespace D5.S0.History.ResidualLedger

/-- The four entry fields in the strict product representation. -/
abbrev StrictResidualLedgerComponents (Source Detector NextAction : Type*) :=
  Omega.Product Source (Omega.Product Detector (Omega.Product ResidualStatus NextAction))

/-- Read the four fields in order. -/
noncomputable def encodeResidualLedgerComponents {Source Detector NextAction : Type*}
    (entry : ResidualLedgerEntry Source Detector NextAction) :
    StrictResidualLedgerComponents Source Detector NextAction :=
  Omega.Product.ofValues entry.source (Omega.Product.ofValues entry.detector
    (Omega.Product.ofValues entry.status entry.nextAction))

private noncomputable def decodeResidualLedgerComponents {Source Detector NextAction : Type*}
    (parts : StrictResidualLedgerComponents Source Detector NextAction) :
    ResidualLedgerEntry Source Detector NextAction where
  source := parts.fst
  detector := parts.snd.fst
  status := parts.snd.snd.fst
  nextAction := parts.snd.snd.snd

/-- The four-component representation of a residual-ledger record is lossless. -/
theorem residual_ledger_components_bijective (Source Detector NextAction : Type*) :
    OmegaMathlib.Function.Bijective (encodeResidualLedgerComponents
      (Source := Source) (Detector := Detector) (NextAction := NextAction)) :=
  Omega.And.intro
    (Omega.Function.LeftInverse.injective (g := decodeResidualLedgerComponents)
      (fun _ => Omega.rfl))
    (Omega.Function.RightInverse.surjective (g := decodeResidualLedgerComponents)
      (fun _ => Omega.rfl))

end D5.S0.History.ResidualLedger
