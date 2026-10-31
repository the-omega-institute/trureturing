import LeanInformationAuditRegAnalysis.SearchReduction.Lookup
import Batteries.Tactic.OpenPrivate

/-! A cache carries ordinary declarations checked by the Lean kernel.
They can be replayed directly or exported as an ordinary compiled dependency
module, without copying the source environment or its extension states. -/
namespace LeanInformationAudit.SearchReduction
open Lean Meta
open private Lean.Environment.setCheckedSync from Lean.Environment

private structure DependencyState where
  seen : NameSet := {}
  visiting : NameSet := {}
  declarations : Array Declaration := #[]

private partial def captureDependency (source base : Environment) (target n : Name) :
    StateT DependencyState (Except String) Unit := do
  if n == target then throw s!"search.target_in_cache_dependency:{n}"
  if (base.toKernelEnv.find? n).isSome || (← get).seen.contains n then return
  if (← get).visiting.contains n then throw s!"search.cache_dependency_cycle:{n}"
  let some info := (source.setExporting false).find? n
    | throw s!"search.missing_cache_dependency:{n}"
  modify fun s => {s with visiting := s.visiting.insert n}
  let declaration ← match info with
    | .inductInfo value => do
      if value.numNested != 0 then throw s!"search.cache_nested_inductive:{n}"
      let group := value.all
      modify fun s => {s with seen := group.foldl (·.insert ·) s.seen}
      let mut types := []
      for owner in group do
        let some (.inductInfo member) := (source.setExporting false).find? owner
          | throw s!"search.cache_inductive_missing:{owner}"
        let mut ctors := []
        for c in member.ctors do
          let some ctor := (source.setExporting false).find? c
            | throw s!"search.cache_constructor_missing:{c}"
          modify fun s => {s with seen := s.seen.insert c}
          for dep in ctor.type.getUsedConstants do captureDependency source base target dep
          ctors := ctors ++ [{name := c, type := ctor.type : Constructor}]
        for dep in member.type.getUsedConstants do captureDependency source base target dep
        types := types ++ [{name := owner, type := member.type, ctors : InductiveType}]
      pure (some (Declaration.inductDecl value.levelParams value.numParams types false))
    | .ctorInfo value =>
      captureDependency source base target value.induct
      pure none
    | .recInfo value =>
      for owner in value.all do captureDependency source base target owner
      pure none
    | .axiomInfo _ => throw s!"search.cache_new_axiom_forbidden:{n}"
    | .quotInfo _ => throw s!"search.cache_quotient_primitive_missing:{n}"
    | _ => do
      for dep in info.getUsedConstantsAsSet do captureDependency source base target dep
      match info with
      | .defnInfo value => pure (some (.defnDecl value))
      | .thmInfo value => pure (some (.thmDecl value))
      | .opaqueInfo value => pure (some (.opaqueDecl value))
      | _ => throw s!"search.cache_unsupported_dependency:{n}"
  modify fun s => {s with
    seen := s.seen.insert n
    visiting := s.visiting.erase n
    declarations := (declaration.map (s.declarations.push ·)).getD s.declarations}

def captureCacheDependencies (source base : Environment) (target : Name)
    (roots : Array Name) : Except String (Array Declaration) := do
  let (_, state) ← (roots.forM (captureDependency source base target)).run {}
  return state.declarations

/-- Cached dependency bodies have the same status as certificates: every
declaration crosses the kernel in this run, with no added axioms. -/
def replayCacheDependencies (declarations : Array Declaration) : MetaM Unit := do
  -- Imported private auxiliaries can share a user name with a public
  -- declaration. The elaborator's async name trie rejects that pair, although
  -- the kernel distinguishes their full names. Replay synchronously in the
  -- kernel map, then expose that checked map to certificate publication.
  let mut checked := (← getEnv).toKernelEnv
  for declaration in declarations do
    if declaration.getNames.all (fun n => (checked.find? n).isSome) then continue
    if let .axiomDecl _ := declaration then throwError "search.cache_new_axiom_forbidden"
    checked ← ofExceptKernelException <|
      checked.addDeclCore 0 0 declaration (cancelTk? := none)
  modifyEnv (·.setCheckedSync checked)
  emitLookupRecord s!"PROBE_CACHE_KERNEL_DEPENDENCIES count={declarations.size}"

end LeanInformationAudit.SearchReduction
