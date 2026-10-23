import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.Measures.SignedSplitSuccessor

/-!
# Original signed successor component scopes

These bindings retain the original arbitrary real signed-measure telescopes,
including empty finite coordinate/exclusion families, arbitrary filters,
finite row types and the literal closed split. They supply actual-positive
source bindings only. A typed dependent-family realization bridge, lawful
enrolled-template readout, whole-family variation and sensitivity, and actual
observational dependence remain absent. No four-slot registration or
`declared_validated` status is asserted by these bindings.
-/

namespace Reg.D5.S3.Topology.Measures.SignedSplitSuccessor

open _root_.D5.S3.Topology.Measures.SignedSplitSuccessor

universe u v w z

theorem finite_marginal_actual :
    type_of% (@eventually_uniform_finite_marginal.{u,v,w,z}) :=
  @eventually_uniform_finite_marginal.{u,v,w,z}

theorem auxiliary_index_actual : type_of% (@exists_auxiliary_index.{u,v,w}) :=
  @exists_auxiliary_index.{u,v,w}

theorem target_index_actual : type_of% (@exists_target_index.{u,v,w}) :=
  @exists_target_index.{u,v,w}

theorem target_piece_actual : type_of% (@exists_signed_target_piece.{u,v}) :=
  @exists_signed_target_piece.{u,v}

theorem finite_exclusion_actual : type_of% (@exists_target_after_finite_exclusion.{u,v,w}) :=
  @exists_target_after_finite_exclusion.{u,v,w}

theorem closed_split_actual : type_of% (@exists_closed_split_of_ordered_exclusion.{u,v}) :=
  @exists_closed_split_of_ordered_exclusion.{u,v}

end Reg.D5.S3.Topology.Measures.SignedSplitSuccessor
