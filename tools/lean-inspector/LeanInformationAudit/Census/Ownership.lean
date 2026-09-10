import Lean

namespace LeanInformationAudit.CensusOwnership

open Lean

/-- Realized reserved theorems can occur in several modules. The first-import
index is provenance for lookup, not a unique ownership authority. -/
def moduleContainsTheorem (data : ModuleData) (info : ConstantInfo) : Bool :=
  info.isTheorem && data.constNames.contains info.name &&
    data.constants.any (fun localInfo => localInfo.name == info.name && localInfo.isTheorem &&
      localInfo.type == info.type && localInfo.levelParams == info.levelParams)

def recordedModuleContainsTheorem (env : Environment) (scope : Array Name)
    (owner declaration : Name) : IO Bool := do
  unless scope.contains owner do return false
  let some info := env.find? declaration | return false
  if owner == env.header.mainModule then
    return moduleContainsTheorem (<- mkModuleData env) info
  let some index := env.getModuleIdx? owner | return false
  return moduleContainsTheorem env.header.moduleData[index.toNat]! info

/-- Presence determines the scope diagnostic; declaration binding checks type and levels separately. -/
def nameInScope (env : Environment) (scope : Array Name) (declaration : Name) : IO Bool := do
  if let some index := env.getModuleIdxFor? declaration then
    if scope.contains env.header.moduleNames[index.toNat]! &&
        env.header.moduleData[index.toNat]!.constNames.contains declaration then return true
  for owner in scope do
    if owner == env.header.mainModule then
      if (<- mkModuleData env).constNames.contains declaration then return true
    else if let some index := env.getModuleIdx? owner then
      if env.header.moduleData[index.toNat]!.constNames.contains declaration then return true
  return false

/-- A theorem may have several valid module occurrences within a selected root. -/
def theoremInScope (env : Environment) (scope : Array Name) (declaration : Name) : IO Bool := do
  let first := (env.getModuleIdxFor? declaration).map (env.header.moduleNames[·.toNat]!)
    |>.getD env.header.mainModule
  if <- recordedModuleContainsTheorem env scope first declaration then return true
  for owner in scope do
    if owner != first && (<- recordedModuleContainsTheorem env scope owner declaration) then return true
  return false

end LeanInformationAudit.CensusOwnership
