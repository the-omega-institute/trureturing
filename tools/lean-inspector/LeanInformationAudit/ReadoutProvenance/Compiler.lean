import LeanInformationAudit.ReadoutProvenance
import Lean.Meta
import Lean.Util.Trace

/-!
Compilation callers supply their existing lexical and declaration tables to the
compiled provenance calculator. Environment extensions hold immutable snapshots
so compiler `withEnv` scopes isolate caches and observations. Reports use the
calculator directly and do not import this adapter.
-/

namespace LeanInformationAudit.RegistrationGates
open Lean

initialize registerTraceClass `InformationProvenance.check

private initialize compilerSession : EnvExtension ProvenanceSession ←
  registerEnvExtension (pure {})
private initialize compilerModuleClasses : EnvExtension (Option (Std.HashMap Name Bool)) ←
  registerEnvExtension (pure none)

namespace Compiler

def view (env : Environment) : CompiledView := {
  find? := env.find?
  getProjectionFnInfo? := fun name => (env.getProjectionFnInfo? name).map fun info =>
    { ctorName := info.ctorName, numParams := info.numParams, i := info.i, fromClass := info.fromClass }
  isClass := Lean.isClass env
  isInstance := Meta.isInstanceCore env
  ownerOf := fun name => (env.getModuleIdxFor? name).map fun index =>
    env.header.modules[index.toNat]!.module
  mainModule := env.header.mainModule
  protectedModules := (compilerModuleClasses.getState env).getD {}
  constantsIdentity := unsafe ptrAddrUnsafe env.constants
  isExporting := env.isExporting }

private def prepareView : CoreM CompiledView := do
  let env ← getEnv
  if (compilerModuleClasses.getState env).isNone then
    let names := env.header.modules.map (·.module)
    let mut data : Std.HashMap Name ModuleData := {}
    for index in [:names.size] do
      if let some item := env.header.moduleData[index]? then
        data := data.insert names[index]! item
    let classes := compiledModuleClasses names (data[·]?)
    modifyEnv fun env => compilerModuleClasses.setState env (some classes)
  return view (← getEnv)

/-- Run one shared calculator query, publishing only immutable session data
and compiler diagnostics. The calculator receives no compiler monad action. -/
def runQuery (action : QueryM α) (locals : LocalContext := {}) : CoreM α := do
  let view ← prepareView
  let session ← IO.mkRef (compilerSession.getState (← getEnv))
  let messages ← IO.mkRef (#[] : Array String)
  let options ← getOptions
  let heartbeatStart ← IO.getNumHeartbeats
  let context : QueryContext := {
    view, session, locals, options, heartbeatStart,
    heartbeatLimit := provenanceDefEqHeartbeats,
    trace := fun message => messages.modify (·.push message) }
  let result : Except IO.Error α ← (try
    pure (.ok (← action.run context))
    catch error => pure (.error error) : IO (Except IO.Error α))
  let snapshot ← session.get
  modifyEnv fun env => compilerSession.setState env snapshot
  for message in (← messages.get) do trace[InformationProvenance.check] "{message}"
  match result with
  | .ok value => return value
  | .error error => throwError "{error}"

def runWalk (action : WalkM α) : StateRefT WalkState Meta.MetaM α := do
  let locals ← getLCtx
  let (value, state) ← runQuery (action.run (← get)) locals
  set state
  return value

end Compiler

def readoutClosureCurrent (theoremName : Name) (readout : Expr) :
    CoreM (Bool × Option (Array String)) :=
  Compiler.runQuery (Compiled.readoutClosureCurrent theoremName readout)

def readoutClosure (env : Environment) (theoremName : Name) (readout : Expr) :
    CoreM (Bool × Option (Array String)) :=
  withEnv env (readoutClosureCurrent theoremName readout)

def provenanceErrorCurrent (root catalog theoremName realization : Name) : CoreM (Option String) :=
  Compiler.runQuery (Compiled.provenanceErrorCurrent root catalog theoremName realization)

def provenanceError (env : Environment) (root catalog theoremName realization : Name) :
    CoreM (Option String) :=
  withEnv env (provenanceErrorCurrent root catalog theoremName realization)

def providerArgumentsCurrent (theoremName : Name) (arguments : Array Expr)
    (availableWork : Nat) : CoreM (Except String (Array Name × Nat)) :=
  Compiler.runQuery (Compiled.providerArgumentsCurrent theoremName arguments availableWork)

def argumentIdentityState (theoremName : Name) (available : Nat) : Meta.MetaM WalkState := do
  Compiler.runQuery (Compiled.argumentIdentityState theoremName available) (← getLCtx)

def argumentIdentityNode (env : Environment) (expression : Expr)
    (deferStatementApart : Bool := false) : StateRefT WalkState Meta.MetaM Unit :=
  Compiler.runWalk (Compiled.argumentIdentityNode (Compiler.view env) expression deferStatementApart)

def templateTypesCurrent (theoremName : Name) (types : Array (Expr × Array Expr))
    (availableWork : Nat) : CoreM (Except String Nat) :=
  Compiler.runQuery (Compiled.templateTypesCurrent theoremName types availableWork)

def observedWholeReadoutCalls : CoreM Nat :=
  return (compilerSession.getState (← getEnv)).wholeReadoutCalls

def getProvenanceCounters : CoreM ProvenanceCounters :=
  return (compilerSession.getState (← getEnv)).counters

def withStatementAliasMemo (action : Meta.MetaM α) : Meta.MetaM α := do
  let previous := (compilerSession.getState (← getEnv)).aliasMemo
  modifyEnv fun env => compilerSession.modifyState env fun state =>
    { state with aliasMemo := (true, none) }
  try action
  finally modifyEnv fun env => compilerSession.modifyState env fun state =>
    { state with aliasMemo := previous }

end LeanInformationAudit.RegistrationGates
