import LeanInformationAuditInterface.Contract.Core
import LeanInformationAuditInterface.Contract.Implementation
import LeanInformationAuditInterface.Contract.Registration
import LeanInformationAuditInterface.Contract.Catalog

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let mut structures : Nat := 0
  let mut fields : Nat := 0
  for index in [:env.header.moduleNames.size] do
    let owner := env.header.moduleNames[index]!
    unless (`LeanInformationAuditInterface.Contract).isPrefixOf owner do continue
    for name in env.header.moduleData[index]!.constNames do
      unless (env.getModuleIdxFor? name).map (·.toNat) == some index do continue
      let some info := getStructureInfo? env name | continue
      structures := structures + 1
      for field in info.fieldNames do
        fields := fields + 1
        if let some defaultName := getEffectiveDefaultFnForField? env name field then
          logInfo m!"contract_default_function:{defaultName}"
          throwError "[FAIL] contract_field_default:{name}.{field}"
  unless structures != 0 && fields != 0 do throwError "contract_defaults_check_empty"
  logInfo m!"[PASS] contract_no_field_defaults structures={structures} fields={fields}"
