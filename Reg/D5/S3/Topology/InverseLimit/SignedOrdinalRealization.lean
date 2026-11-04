import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.InverseLimit.SignedOrdinalRealization

/-! Exact source reconstruction is checked. Four-slot realization, lawful
readout and whole-family variation/sensitivity remain unfinished under issue
21750. No declared_validated registration is claimed. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Topology.InverseLimit.SignedOrdinalRealization
open _root_.D5.S3.Topology.InverseLimit.SignedOrdinalRealization

abbrev properLaws_scope := type_of% (@properLaws)
theorem properLaws_source : properLaws_scope := @properLaws
abbrev slice_carrier_scope := type_of% (@slice_carrier)
theorem slice_carrier_source : slice_carrier_scope := @slice_carrier
abbrev carrier_read_scope := type_of% (@carrier_read)
theorem carrier_read_source : carrier_read_scope := @carrier_read
abbrev top_read_scope := type_of% (@top_read)
theorem top_read_source : top_read_scope := @top_read
abbrev initial_carrier_scope := type_of% (@initial_carrier)
theorem initial_carrier_source : initial_carrier_scope := @initial_carrier
abbrev wholeBirth_read_scope := type_of% (@wholeBirth_read)
theorem wholeBirth_read_source : wholeBirth_read_scope := @wholeBirth_read
abbrev whole_measure_scope := type_of% (@whole_measure)
theorem whole_measure_source : whole_measure_scope := @whole_measure
abbrev slice_nu_scope := type_of% (@slice_nu)
theorem slice_nu_source : slice_nu_scope := @slice_nu
abbrev slice_J_scope := type_of% (@slice_J)
theorem slice_J_source : slice_J_scope := @slice_J
abbrev successor_carrier_scope := type_of% (@successor_carrier)
theorem successor_carrier_source : successor_carrier_scope := @successor_carrier
abbrev projection_factor_scope := type_of% (@projection_factor)
theorem projection_factor_source : projection_factor_scope := @projection_factor
abbrev initial_onto_scope := type_of% (@initial_onto)
theorem initial_onto_source : initial_onto_scope := @initial_onto
abbrev slice_N_scope := type_of% (@slice_N)
theorem slice_N_source : slice_N_scope := @slice_N
abbrev reservoir_incoming_scope := type_of% (@reservoir_incoming)
theorem reservoir_incoming_source : reservoir_incoming_scope := @reservoir_incoming
abbrev launch_scope := type_of% (@launch)
theorem launch_source : launch_scope := @launch

end Reg.D5.S3.Topology.InverseLimit.SignedOrdinalRealization
