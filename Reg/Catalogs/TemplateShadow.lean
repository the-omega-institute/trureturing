import D5.S3.ConceptDynamics.InformationEscape.TemplateShadow
import Reg.Support.TemplateShadowContract
import LeanInformationAudit.SealCommand

open Lean LeanInformationAudit

run_cmd RootCatalogs.declare Reg.Support.TemplateShadowContract.contract

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
-- Seal the existing finite catalogs under the production seal limit.
#seal_information_theory
