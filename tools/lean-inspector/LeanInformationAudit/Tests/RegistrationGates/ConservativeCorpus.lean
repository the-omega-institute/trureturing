import D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations
import D5.S3.ConceptDynamics.InformationEscape.GuardedEqualityRegistrations
import D5.S3.ConceptDynamics.InformationEscape.IffRegistrations
import D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations
import D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations
import D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations
import D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations
import D5.S3.ConceptDynamics.InformationEscape.TemplateShadow

import D5.S3.ConceptDynamics.InformationEscape.InformationRoot
import D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers
import D5.S3.ConceptDynamics.InformationEscapeRealizations.UnifiedCausalRegistration
import LeanInformationAudit.Tests.RegistrationGates.InventoryAssertions

open Lean LeanInformationAudit

-- Historical undeclared registrations remain rewrite inventory. This asserts
-- every occurrence and BindingRecord, without claiming provenance admission.
run_meta do
  let env := (← getEnv).setExporting false
  let modules : Array (Name × Nat) := #[
    (`D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations, 2),
    (`D5.S3.ConceptDynamics.InformationEscape.GuardedEqualityRegistrations, 2),
    (`D5.S3.ConceptDynamics.InformationEscape.IffRegistrations, 2),
    (`D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations, 3),
    (`D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations, 2),
    (`D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations, 2),
    (`D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations, 2),
    (`D5.S3.ConceptDynamics.InformationEscape.TemplateShadow, 10),
    (`D5.S3.ConceptDynamics.InformationEscape.InformationRoot, 11),
    (`D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers, 7),
    (`D5.S3.ConceptDynamics.InformationEscapeRealizations.UnifiedCausalRegistration, 2)]
  for (owner, expected) in modules do
    discard <| Tests.assertUndeclaredInventory env owner expected
