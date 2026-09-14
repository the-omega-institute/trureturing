import LeanInformationAudit.Tests.Occurrence.JointImport.Shared

open LeanInformationAudit.Tests.Occurrence.JointImport

register_information_theorem shared in arena
  primitives readout.toPrimitiveBundle realization bridge

expect_information_occurrence shared in arena
  from "LeanInformationAudit.Tests.Occurrence.JointImport.First"

#seal_information_theory

-- Source-level companion references must resolve in their own sealing module.
#check shared.__information_unit
#check shared.__lowers_escape
#check shared.__escape_enriched
#check arena.__information_catalog
#check arena.__catalog_irredundant
