import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.Measures.SignedDelayedSuccessor

/-! The complete born-data and old-law telescope is preserved verbatim by the
source type and its proof application. This is not a four-slot registration.
Issue 21750 records the missing full realization bridge, lawful enrolled
readout and whole-family variation, sensitivity and observational dependence. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Topology.Measures.SignedDelayedSuccessor

open _root_.D5.S3.Topology.Measures.SignedDelayedSuccessor

universe u v w z

abbrev successorScope := type_of% (@exists_delayed_successor.{u, v, w, z})

theorem successor_source : successorScope.{u, v, w, z} :=
  @exists_delayed_successor.{u, v, w, z}

end Reg.D5.S3.Topology.Measures.SignedDelayedSuccessor
