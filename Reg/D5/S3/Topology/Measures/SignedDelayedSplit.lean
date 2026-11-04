import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.Measures.SignedDelayedSplit

/-! Exact unabridged source telescopes for delayed selection and signed splitting.
These source applications do not supply four-slot variation or sensitivity. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Topology.Measures.SignedDelayedSplit

open _root_.D5.S3.Topology.Measures.SignedDelayedSplit

universe u v w z

abbrev poolScope := type_of% (@exists_delayed_fibre_pools.{u, v, z})
abbrev planScope := type_of% (@exists_delayed_pool_plan.{u, v, z})
abbrev internalScope := type_of% (@exists_internal_delayed_split.{u, v, w, z})
abbrev splitScope := type_of% (@exists_parity_ordered_split.{u, v, w, z})

theorem pools_source : poolScope.{u, v, z} := @exists_delayed_fibre_pools.{u, v, z}
theorem plan_source : planScope.{u, v, z} := @exists_delayed_pool_plan.{u, v, z}
theorem internal_source : internalScope.{u, v, w, z} := @exists_internal_delayed_split.{u, v, w, z}
theorem split_source : splitScope.{u, v, w, z} := @exists_parity_ordered_split.{u, v, w, z}

end Reg.D5.S3.Topology.Measures.SignedDelayedSplit
