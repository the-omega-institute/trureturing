import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.InverseLimit.SignedSuccessorCoordinates

/-! The complete source telescope of the coordinate constructor is retained.
The proof-carrying Result output has no selected raw readout/state occurrence
in this registration attempt; no validated four-slot binding is asserted. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set

namespace Reg.D5.S3.Topology.InverseLimit.SignedSuccessorCoordinates

open _root_.D5.S3.Topology.InverseLimit.SignedProperLimit
open _root_.D5.S3.Topology.InverseLimit.SignedSuccessorCoordinates

structure SourceInputs where
  a : Ordinal.{0}
  history : Prefix (Order.succ a)
  Y : Set (history.Space ⟨a, Order.lt_succ a⟩)
  Z : Set (history.Space ⟨a, Order.lt_succ a⟩)
  closedY : IsClosed Y
  closedZ : IsClosed Z
  cover : Y ∪ Z = univ

def conclusion (P : SourceInputs) : Prop := Nonempty (Result P.history P.Y P.Z)

abbrev sourceScope := type_of% (@exists_successor_coordinates)

/-- No source binder or closed-cover condition is discarded. -/
theorem source_bridge : sourceScope ↔ ∀ P : SourceInputs, conclusion P := by
  constructor
  · intro h P
    exact h P.history P.Y P.Z P.closedY P.closedZ P.cover
  · intro h a H Y Z hY hZ hcover
    exact h ⟨a, H, Y, Z, hY, hZ, hcover⟩

/-- This is source reconstruction evidence, without a registration verdict. -/
theorem actual_positive : ∀ P : SourceInputs, conclusion P :=
  source_bridge.mp @exists_successor_coordinates

end Reg.D5.S3.Topology.InverseLimit.SignedSuccessorCoordinates
