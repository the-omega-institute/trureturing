import Lean.Environment

namespace LeanInformationAudit.CompiledMetadata
open Lean

/-- Pinned compiler payload layouts, read directly from ModuleData.entries.
No extension is registered, initialized or replayed by this reader. -/
structure Projection where
  ctorName : Name
  numParams : Nat
  i : Nat
  fromClass : Bool
  deriving Inhabited, BEq

private structure ClassEntry where
  name : Name
  outParams : Array Nat
  outLevelParams : Array Nat

private inductive AttributeKind where
  | global | local | scoped

private structure InstanceEntry where
  keys : Array Unit
  val : Expr
  priority : Nat
  globalName? : Option Name
  synthOrder : Array Nat
  attrKind : AttributeKind

private inductive ScopedEntry (α : Type) where
  | global (value : α)
  | scoped (namespaceName : Name) (value : α)

inductive Reducibility where
  | reducible | semireducible | irreducible | implicitReducible | instanceReducible
  deriving Inhabited, BEq

/-- Declaration semantics needed by provenance and template dependency gates.
These maps index compiler metadata; they confer no proof-checking authority. -/
structure Store where
  projections : NameMap Projection := {}
  classes : NameSet := {}
  instances : NameSet := {}
  implementedBy : NameMap Name := {}
  externs : NameSet := {}
  reducibility : NameMap Reducibility := {}
  recursive : NameSet := {}
  axioms : NameMap (Array Name) := {}

private def globalValue? : ScopedEntry α → Option α
  | .global value => some value
  | .scoped .. => none

private def axiomExtensionName : Name :=
  (`_private.Lean.Util.CollectAxioms).num 0 ++ `Lean.exportedAxiomsExt

/-- The compiler exports axiom closures of public declarations as data. -/
unsafe def exportedAxioms? (data : ModuleData) (name : Name) : Option (Array Name) := do
  let (_, entries) ← data.entries.find? (fun entry =>
    entry.1 == axiomExtensionName)
  for entry in entries do
    let (constant, axioms) : Name × Array Name := unsafeCast entry
    if constant == name then return axioms
  none

/-- Interpret the pinned payload types of the exact extension names. Other
extensions are outside the declaration-semantic input of these gates. -/
unsafe def readModule (state : Store) (data : ModuleData) : Store := Id.run do
  let mut state := state
  for (kind, entries) in data.entries do
    if kind == axiomExtensionName then
      for entry in entries do
        let (name, axioms) : Name × Array Name := unsafeCast entry
        state := { state with axioms := state.axioms.insert name axioms }
    else if kind == `Lean.projectionFnInfoExt then
      for entry in entries do
        let (name, projection) : Name × Projection := unsafeCast entry
        state := { state with projections := state.projections.insert name projection }
    else if kind == `recExt then
      for entry in entries do
        let name : Name := unsafeCast entry
        state := { state with recursive := state.recursive.insert name }
    else if kind == `Lean.classExtension then
      for entry in entries do
        let entry : ClassEntry := unsafeCast entry
        state := { state with classes := state.classes.insert entry.name }
    else if kind == `Lean.Meta.instanceExtension then
      for entry in entries do
        let entry : ScopedEntry InstanceEntry := unsafeCast entry
        if let some value := globalValue? entry then
          if let some name := value.globalName? then
            state := { state with instances := state.instances.insert name }
    else if kind == `Lean.Compiler.implementedByAttr then
      for entry in entries do
        let (name, implementation) : Name × Name := unsafeCast entry
        state := { state with implementedBy := state.implementedBy.insert name implementation }
    else if kind == `Lean.externAttr then
      for entry in entries do
        let entry : Name × EnvExtensionEntry := unsafeCast entry
        state := { state with externs := state.externs.insert entry.1 }
    else if kind == `reducibilityCore then
      for entry in entries do
        let (name, status) : Name × Reducibility := unsafeCast entry
        state := { state with reducibility := state.reducibility.insert name status }
    else if kind == `reducibilityExtra then
      for entry in entries do
        let entry : ScopedEntry (Name × Reducibility) := unsafeCast entry
        if let some (name, status) := globalValue? entry then
          state := { state with reducibility := state.reducibility.insert name status }
  return state

end LeanInformationAudit.CompiledMetadata
