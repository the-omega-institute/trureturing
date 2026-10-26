import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.InverseLimit.SignedOrdinalSuccessor

/-! Exact source reconstruction is attempted for each new public theorem.
No lawful enrolled readout or whole-family variation and sensitivity proof
has been supplied for these dependent proof-carrying output records. This is
not a four-slot registration; the unfinished audit belongs to issue 21750. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Topology.InverseLimit.SignedOrdinalSuccessor

open _root_.D5.S3.Topology.InverseLimit.SignedOrdinalSuccessor

abbrev preparationScope := type_of% (@exists_prepared)
abbrev codesScope := type_of% (@exists_codes)
abbrev projectionScope := type_of% (@projection_onto)
abbrev oldFScope := type_of% (@Prepared.old_f)
abbrev oldEScope := type_of% (@Prepared.old_e)
abbrev massScope := type_of% (@Prepared.mass)
abbrev nullScope := type_of% (@Prepared.null)
abbrev ordinaryScope := type_of% (@exists_ordinary)

abbrev successorScope := type_of% (@exists_successor)
abbrev readbackScope := type_of% (@Result.birth_readback)
abbrev retentionScope := type_of% (@Result.arrival_retains)
abbrev literalFScope := type_of% (@Result.literal_f)
abbrev literalEScope := type_of% (@Result.literal_e)
abbrev transportScope := type_of% (@Result.quantitative_transport)
abbrev quantitativeScope := type_of% (@Result.quantitative_g)

theorem preparation_source : preparationScope := @exists_prepared
theorem codes_source : codesScope := @exists_codes
theorem projection_source : projectionScope := @projection_onto
theorem old_f_source : oldFScope := @Prepared.old_f
theorem old_e_source : oldEScope := @Prepared.old_e
theorem mass_source : massScope := @Prepared.mass
theorem null_source : nullScope := @Prepared.null
theorem ordinary_source : ordinaryScope := @exists_ordinary

theorem successor_source : successorScope := @exists_successor
theorem readback_source : readbackScope := @Result.birth_readback
theorem retention_source : retentionScope := @Result.arrival_retains
theorem literal_f_source : literalFScope := @Result.literal_f
theorem literal_e_source : literalEScope := @Result.literal_e
theorem transport_source : transportScope := @Result.quantitative_transport
theorem quantitative_source : quantitativeScope := @Result.quantitative_g

end Reg.D5.S3.Topology.InverseLimit.SignedOrdinalSuccessor
