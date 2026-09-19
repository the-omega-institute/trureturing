/- Copyright (c) 2026 The Omega Institute. Released under Apache 2.0. -/
module
prelude
public import Lean.EnvExtension
public section
namespace Lean

/- Filled only by the content-addressed compiler recipe before compilation. -/
def compilerOriginHash : String := "@COMPILER_ORIGIN_HASH@"

abbrev CompilerGeneratedCompanionDriver := Environment → Array Name

/- The compiler recipe keeps provenance in private producer-owned extensions in
   each generator module.  This shared value is only the read-only record and
   exact matcher used by those query functions; it is not a write authority. -/
structure CompilerProducedTheorem where
  owner : Name
  theoremValue : TheoremVal
  deriving Inhabited

def CompilerProducedTheorem.matches (record : CompilerProducedTheorem) (env : Environment) : Bool :=
  let expected := record.theoremValue
  let owner := match env.getModuleIdxFor? expected.name with
    | some index => env.header.moduleNames[index.toNat]!
    | none => env.header.mainModule
  owner == record.owner && match env.find? expected.name with
    | some (.thmInfo actual) => actual.levelParams == expected.levelParams &&
        actual.type == expected.type && actual.value == expected.value
    | _ => false

def compilerProducedNames (records : Array CompilerProducedTheorem) (env : Environment) : Array Name :=
  records.filterMap fun record =>
    if record.matches env then some record.theoremValue.name else none

end Lean
