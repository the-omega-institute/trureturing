import CFMPGenericCapDisk1307Transient
import CFMPLiteralCornerFibers1347Transient
import Mathlib.SetTheory.Cardinal.Finite

set_option autoImplicit false
noncomputable section
namespace D5.S3.Geometry.Gluing.LiteralCapDiskCandidate
open D5.S3.Geometry.Gluing.LiteralSixPairingCandidate (literalPairing localNoEdgeReversal)
open D5.S3.Geometry.Gluing.LiteralCornerFibersCandidate
  (OriginalCorner lowerFiberEquiv upperFiberEquiv)
open D5.S3.Geometry.Gluing.RawFaceCapSliceCandidate (label)
open D5.S3.Geometry.Gluing.RawFaceOccurrenceCandidate (OrderedEnd)
open D5.S3.Geometry.Gluing.RawFaceCycleCandidate (chooseOrientation)
open D5.S3.Geometry.Gluing.RawFaceCapDiskCandidate (capStrictImage actualCapDiskChart)
open D5.S3.Geometry.Gluing.ActualLinkAffineFan (OpenDisk)

-- Temporary exact applications; no canonical finite-instance retention.
theorem lower_card : Nat.card
    {c : OriginalCorner // label literalPairing c = label literalPairing (0,0)} = 18 := by
  simpa only [Nat.card_prod, Nat.card_fin] using Nat.card_congr lowerFiberEquiv

theorem upper_card : Nat.card
    {c : OriginalCorner // label literalPairing c = label literalPairing (0,3)} = 6 := by
  simpa only [Nat.card_fin] using Nat.card_congr upperFiberEquiv

variable [TopologicalSpace (Fin 6)] [DiscreteTopology (Fin 6)]

def actualLiteralCapDiskChart (d0 : OrderedEnd (Fin 6)) :
    ↥(capStrictImage literalPairing d0) ≃ₜ OpenDisk :=
  actualCapDiskChart literalPairing (chooseOrientation literalPairing) d0
    (localNoEdgeReversal d0)
end D5.S3.Geometry.Gluing.LiteralCapDiskCandidate

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  for name in [``D5.S3.Geometry.Gluing.LiteralCapDiskCandidate.lower_card,
      ``D5.S3.Geometry.Gluing.LiteralCapDiskCandidate.upper_card,
      ``D5.S3.Geometry.Gluing.LiteralCapDiskCandidate.actualLiteralCapDiskChart] do
    unless (env.checked.get.find? name).isSome do
      Lean.throwError m!"CFMP1366 literal cap application target absent: {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        Lean.throwError m!"CFMP1366 disallowed axiom {ax}"
    Lean.logInfo m!"CFMP1366 CHECKED {name} axioms={axioms}"
