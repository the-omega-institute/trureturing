import LeanInformationAudit.Registry
import LeanInformationAudit.Contract.Discovery

namespace LeanInformationAudit.Contract.RootStructure
open Lean

/-- The loaded Reg source tree fixes obligations before candidate discovery.
Unmoved legacy files are ordinary under this rule; their typed-entry migration
state is measured separately rather than inferred from legacy catalog commands. -/
def required (env : Environment) : IO (Array Requirement) :=
  requiredFor (env.header.moduleNames.push env.header.mainModule |>.filter ((`Reg).isPrefixOf ·))
    fun owner => Repository.source (owner.toString.replace "." "/" ++ ".lean")

end LeanInformationAudit.Contract.RootStructure

namespace LeanInformationAudit.Contract.Discovery
open Lean Meta

/-- Compilation-time callers pass their compiler inventory to the same discovery
computation used by standalone artifact readers. -/
def discoverWithStructure (requirements : Array RootStructure.Requirement)
    (moduleNames : Array Name)
    (sourceOf : Name → IO System.FilePath := moduleSource) : MetaM Snapshot := do
  let original ← getEnv
  let compiled := original.setExporting false
  let context : CompiledExpressions.Context := {
    find := compiled.find?
    heartbeatStart := ← getInitHeartbeats
    heartbeatLimit := ← getMaxHeartbeats }
  let constantsOf (owner : Name) : IO (Array ConstantInfo) := do
    if owner == compiled.header.mainModule then
      return compiled.constants.map₂.toList.toArray.map Prod.snd
    let some idx := compiled.getModuleIdx? owner
      | throw <| IO.userError s!"contract.discovery:module_missing:{owner}"
    return compiled.header.moduleData[idx.toNat]!.constants
  let mut closures : NameMap (Array Name) := {}
  for owner in moduleNames do
    for definition in ← IO.ofExcept <| auditConstants owner (← constantsOf owner) do
      let head := definition.info.type.getAppFn.constName!
      if head == ``Contract.Registration || head == ``Contract.Seal then
        closures := closures.insert definition.info.name (← collectAxioms definition.info.name)
  discoverCompiled requirements moduleNames context constantsOf
    (fun name => match closures.find? name with
      | some axioms => pure axioms
      | none => throw <| IO.userError s!"contract.discovery:axioms_missing:{name}") sourceOf

/-- Production constructs obligations from the Reg source-tree path rule before
discovery. Isolated tests can supply requirements from their own source tree;
no decoded contract entry determines its module kind. -/
def discover (moduleNames : Array Name)
    (sourceOf : Name → IO System.FilePath := moduleSource) : MetaM Snapshot := do
  let env ← getEnv
  let requirements ← RootStructure.required env
  for owner in env.header.moduleNames.push env.header.mainModule do
    if (`Reg).isPrefixOf owner && !moduleNames.contains owner then
      throwError "contract.root_structure:required_module_missing:{owner}"
  discoverWithStructure requirements moduleNames sourceOf

end LeanInformationAudit.Contract.Discovery
