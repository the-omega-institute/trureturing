import OmegaChecks.ModuleSurface

open Lean Lean.Meta

namespace OmegaChecks.FieldMethods

/-- Follow the same type heads (including reducible aliases) as Lean's dot elaborator. -/
private partial def matchesReceiver (domain : Expr) (base : Name) : MetaM Bool :=
  withReducibleAndInstances do
    if domain.cleanupAnnotations.isAppOf base then return true
    let type ← whnfCore domain
    if type.isAppOf base then return true
    if let some body ← unfoldDefinition? type then matchesReceiver body base else return false

/-- A consumer may introduce a method as either a declaration or an export alias.
The official receiver's type has lost the Omega prefix, so its corresponding field
must resolve to the same translated declaration when the defining module is imported. -/
def check (strict official : Environment) (owner : Name) (rename : Name → Name) : IO Unit := do
  let some src := strict.getModuleIdx? owner | throw <| IO.userError s!"missing strict module {owner}"
  let some dst := official.getModuleIdx? owner | throw <| IO.userError s!"missing official module {owner}"
  let localAliases := aliasExtension.getModuleEntries official dst
  let entries := (strict.header.moduleData[src]!.constNames.map fun n => (n, n)) ++
    aliasExtension.getModuleEntries strict src
  let verify : MetaM Unit := do
    for (name, target) in entries do
      if name.getRoot != `Omega || name.isInternalOrNum || name.hasMacroScopes || isPrivateName name then continue
      let base := name.getPrefix
      if rename base == base then continue
      let info ← getConstInfo target
      let hasReceiver ← forallTelescopeReducing info.type fun xs _ =>
        xs.anyM fun x => do matchesReceiver (← inferType x) base
      unless hasReceiver do continue
      let field := name.replacePrefix base (rename base)
      let expected := rename target
      let resolve := fun env n => (ResolveName.resolveGlobalName env {} .anonymous [] n).filter (·.2.isEmpty)
      unless resolve strict name == [(target, [])] && resolve official field == [(expected, [])] do
        throwError "field resolution mismatch for {name} in {owner}: expected {field} to resolve to {expected}"
      if field != expected && !localAliases.contains (field, expected) then
        let closure ← ModuleSurface.publicClosure official owner
        unless closure.any (fun moduleName => (official.getModuleIdx? moduleName).any fun i =>
          (aliasExtension.getModuleEntries official i).contains (field, expected)) do
          throwError "missing public field export {field} for {expected} when importing {owner}"
  verify.run' |>.toIO' {fileName := "<project extension methods>", fileMap := default} {env := strict}

end OmegaChecks.FieldMethods
