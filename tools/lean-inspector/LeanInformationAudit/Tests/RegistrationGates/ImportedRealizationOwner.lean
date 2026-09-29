import LeanInformationAudit.Tests.Occurrence.RootCatalog.Designated
import LeanInformationAudit.Tests.Occurrence.RootCatalog.Ownership

open Lean LeanInformationAudit
open LeanInformationAudit.Tests.Occurrence.RootCatalog
open LeanInformationAudit.Tests.Occurrence.RootCatalog.Ownership

-- One generated inline realization and two imported pure realization bridges.
-- The eleven production events run these same assertions in FrozenRoots.
run_meta do
  checkImportedOwners baselineRoot 1
  checkImportedOwners causalContributor 2
  let events := TemplateBinding.inventory (← getEnv)
  let baseline := events.find? (·.key.registrationModule == baselineRoot)
  let causal := events.find? (·.key.registrationModule == causalContributor)
  let (some baseline, some causal) := (baseline, causal)
    | throwError "fixture ownership: missing native contributor"
  -- Present units from the other imported contributor still have the wrong owner.
  rejectsOwner { baseline with unitName := causal.unitName }
  rejectsOwner { causal with unitName := baseline.unitName }
  logInfo "fixture cross-contributor units rejected"
