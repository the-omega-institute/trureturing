import D5.S3.ConceptDynamics.InformationEscape.InformationRoot
import Reg.Support.InformationRootContract
import LeanInformationAudit.SealCommand

open Lean LeanInformationAudit

run_cmd RootCatalogs.declare Reg.Support.InformationRootContract.contract

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
-- The production root seals eleven finite catalogs under the existing limit.
#seal_information_theory
