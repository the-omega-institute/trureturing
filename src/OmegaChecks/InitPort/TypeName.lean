module
public import Lean
import all Init.Dynamic
import all Lean.Environment
import all Lean.OriginalConstKind
import Lean.Compiler.IR.CompilerM
import OmegaChecks.InitPort.Translation

open Lean

namespace OmegaChecks.InitPort.TypeName

private def package : Type u → {T : Type // T = Name} :=
  opaqueId (fun _ => ⟨Name, rfl⟩)

private def family (α : Type u) : NonemptyType :=
  ⟨(package α).1, ⟨cast (package α).2.symm Name.anonymous⟩⟩

private structure Model (α : Type u) where
  data : (family α).type

private def make (α : Type u) (name : Name) : Model α :=
  ⟨cast (package α).2.symm name⟩

private def decode (α : Type u) (self : Model α) : Name :=
  cast (package α).2 self.data

private theorem inverseCast {T U : Type} (h : T = U) (v : U) : cast h (cast h.symm v) = v := by
  cases h
  rfl

private theorem roundTrip (α : Type u) (n : Name) : decode α (make α n) = n :=
  inverseCast (package α).2 n

public def reader := mkPrivateNameCore `Init.Dynamic `TypeName.typeNameImpl

/-- Both conversions are unsafe in the pinned interface. In particular only trusted code
may assert which declaration name represents an arbitrary type. -/
public def unsafeConversion (name : Name) := name == `TypeName.mk || name == reader

public def isUnsafeConversion (ci : ConstantInfo) (strict : Bool) : Bool := Id.run do
  let rename := if strict then InitKernelPort.portName else id
  let .defnInfo d := ci | return false
  let [u] := d.levelParams | return false
  let mk := d.name == rename `TypeName.mk
  unless (mk || d.name == rename reader) && d.safety == .unsafe && d.all == [d.name] do return false
  let tag := mkApp (mkConst (rename `TypeName) [.param u]) (.bvar 0)
  let name := mkConst (rename `Lean.Name)
  let expected := Expr.forallE `α (.sort (.succ (.param u)))
    (if mk then .forallE `typeName name (tag.liftLooseBVars 0 1) .default
     else .forallE `inst tag name .instImplicit) .default
  return d.type.eqv expected

/-- Replay the total logical terms separately before installing the official unsafe flags. -/
public def replay (base : Kernel.Environment) (constants : Std.HashMap Name ConstantInfo) : IO Kernel.Environment := do
  let mut installed := base
  for n in [`TypeName.mk, reader] do
    let some ci := constants[InitKernelPort.portName n]? | continue
    unless isUnsafeConversion ci true do throw <| IO.userError s!"incorrect type name conversion {n}"
    let .defnInfo d := ci | throw <| IO.userError s!"missing type name definition {n}"
    unless (installed.addDeclCore 0 1000 (.defnDecl {d with safety := .safe}) none).isOk do
      throw <| IO.userError s!"invalid logical type name conversion {n}"
    let .ok next := installed.addDeclCore 0 1000 (.defnDecl d) none
      | throw <| IO.userError s!"invalid unsafe type name interface {n}"
    installed := next
  return installed

private def replaceModel (n : Name) : Name :=
  if n == ``family then `TypeNameData
  else if n == ``Model then `TypeName
  else if n == ``Model.mk then mkPrivateNameCore `Init.Dynamic `TypeName.mk'
  else if n == ``Model.data then mkPrivateNameCore `Init.Dynamic `TypeName.data
  else n

public structure Templates where
  family : Expr
  make : Expr
  decode : Expr

public def templates (env : Environment) : IO Templates := do
  let body (n : Name) := do
    let some (.defnInfo ci) := env.find? n | throw <| IO.userError s!"missing type name template {n}"
    let unfoldHelper := fun n => n == ``package || (isPrivateName n && n.toString.contains "_proof_" &&
      (privateToUserName n).getRoot == `OmegaChecks)
    let e ← (Meta.deltaExpand ci.value unfoldHelper (allowOpaque := true)).toIO'
      {fileName := "<type name carrier>", fileMap := default} {env}
    return e.replace fun
      | .const n us => some (.const (replaceModel n) us)
      | .proj n idx arg => if n == ``Model then some (.proj `TypeName idx arg) else none
      | _ => none
  return ⟨← body ``family, ← body ``make, ← body ``decode⟩

public def identityIR (env : Environment) (n : Name) : Bool := Id.run do
  let some (.fdecl _ args .tobject (.inc kept 1 true false (.ret (.var returned))) _) :=
    IR.findEnvDecl env n | return false
  let #[_, name] := args | return false
  return kept == name.x && returned == name.x

private def nativeType (rename : Name → Name) (e : Expr) : Expr :=
  e.replace fun
    | .const n us => if [`TypeName, `Lean.Name].contains n then some (.const (rename n) us) else none
    | _ => none

private def copyStage (source env : Environment) (ext : Compiler.LCNF.DeclExt .pure)
    (n : Name) (rename : Name → Name) : IO Environment := do
  let some d := Compiler.LCNF.getDeclCore? source ext n | throw <| IO.userError s!"missing {ext.name}/{n}"
  let #[index, payload] := d.params | throw <| IO.userError s!"wrong type name arity {n}"
  let type := nativeType rename
  let value ← match d.value with
    | .code (.return x) =>
      unless x == payload.fvarId do throw <| IO.userError s!"incorrect identity {n}"
      pure d.value
    | .code (.let binding (.return x)) =>
      unless x == binding.fvarId do throw <| IO.userError s!"incorrect type name return {n}"
      let rhs ← match binding.value with
        | .const ctor us args =>
          unless n == `TypeName.mk && ctor == mkPrivateNameCore `Init.Dynamic `TypeName.mk' &&
              args == #[.type (.fvar index.fvarId), .fvar payload.fvarId] do
            throw <| IO.userError "incorrect name constructor"
          pure (.const (rename ctor) us args)
        | .proj family 0 arg _ =>
          unless n == reader && family == `TypeName && arg == payload.fvarId do
            throw <| IO.userError "incorrect name projection"
          pure (.proj (rename family) 0 arg)
        | _ => throw <| IO.userError s!"unexpected type name operation {n}"
      pure (.code (.let {binding with type := type binding.type, value := rhs} (.return x)))
    | _ => throw <| IO.userError s!"unexpected type name code {n}"
  return ext.addEntry env { d with
    name := rename n
    type := type d.type
    params := d.params.map (fun p => {p with type := type p.type})
    value }

/-- The two pinned runtime functions only retain and return their borrowed name argument. -/
public def nativeEntries (source monolith : Environment) (owner : Name) (rename : Name → Name)
    (available : Name → Bool) : IO Environment := do
  let mut kenv := monolith.toKernelEnv
  let privateReader := rename reader
  for n in [rename `TypeName.mk, rename `TypeName.typeName, privateReader] do
    kenv := { kenv with const2ModIdx := kenv.const2ModIdx.erase n }
  let mut env := (Environment.ofKernelEnv kenv).setMainModule owner
  for n in [`TypeName.mk, reader] do
    unless available n do continue
    let some (.fdecl _ args ty body info) := IR.findEnvDecl source n | throw <| IO.userError s!"missing native {n}"
    let some sig := Compiler.LCNF.getSigCore? source Compiler.LCNF.impureSigExt n
      | throw <| IO.userError s!"missing signature {n}"
    unless identityIR source n && info.sorryDep?.isNone do throw <| IO.userError s!"invalid identity function {n}"
    let target := rename n
    env := Lean.privateConstKindsExt.insert env target .defn
    env := Compiler.LCNF.setDeclPublic env target
    env := Compiler.LCNF.impureSigExt.addEntry env {sig with name := target}
    env ← copyStage source env Compiler.LCNF.baseExt n rename
    env ← copyStage source env Compiler.LCNF.monoExt n rename
    env := IR.declMapExt.addEntry env (.fdecl target args ty body info)
  if available reader && available `TypeName.typeName then
    env ← IO.ofExcept <| Compiler.setImplementedBy env (rename `TypeName.typeName) (rename reader)
  return env

/-- Hidden executable definitions and the public getter are still available to the compiler. -/
public def publicCompilerEntries (env : Environment) : IO (Array (Name × Array EnvExtensionEntry)) := do
  let data ← mkModuleData env .private
  return data.entries.filter (fun e => (e.1 == Compiler.implementedByAttr.ext.name ||
    e.1 == Lean.privateConstKindsExt.name) && !e.2.isEmpty)

public def check (strict publicStrict env : Environment) (n : Name) (candidate : Expr) : IO Unit := do
  let model ← templates env
  let expected := if n == `TypeNameData then model.family else if n == reader then model.decode else model.make
  let some official := env.find? n | throw <| IO.userError s!"missing {n}"
  unless env.getModuleIdxFor? n == env.getModuleIdx? `Init.Dynamic &&
      (n == `TypeNameData || n == `TypeName.mk || n == reader) &&
      candidate.equal (expected.instantiateLevelParams [`u] (official.levelParams.map Level.param)) do
    throw <| IO.userError s!"incorrect indexed name model for {n}"
  unless [`TypeName.mk, reader, `Lean.opaqueId].all (identityIR env) &&
      Compiler.getImplementedBy? env `TypeName.typeName == some reader do
    throw <| IO.userError "type name constructor or accessor changed its runtime representation"
  let some (.opaqueInfo pinned) := env.find? `TypeNameData | throw <| IO.userError "missing opaque name carrier"
  let concrete : MetaM Unit := do
    let .ok _ := Kernel.check env {} (mkConst ``roundTrip (official.levelParams.map Level.param))
      | throwError "ill-typed name round trip"
    let erased := model.family.replace fun
      | .const `Lean.opaqueId us => do
        let some (.opaqueInfo ident) := env.find? `Lean.opaqueId | none
        some (ident.value.instantiateLevelParams ident.levelParams us)
      | _ => none
    unless Kernel.isDefEqGuarded env {} (erased.instantiateLevelParams [`u] (pinned.levelParams.map Level.param))
        pinned.value do throwError "type name payload differs from the native Name carrier"
  concrete.run' |>.toIO' {fileName := "<type name representation>", fileMap := default} {env}
  let some visible := publicStrict.find? `Omega.TypeNameData | throw <| IO.userError "missing public name family"
  unless visible.isAxiom && getReducibilityStatusCore strict `Omega.TypeNameData == .irreducible do
    throw <| IO.userError "type name carrier is exposed"
  let strictReader := mkPrivateNameCore `OmegaInit.Dynamic `Omega.TypeName.typeNameImpl
  if n == `TypeName.mk then
    unless (publicStrict.find? `Omega.TypeName.mk).any (·.isUnsafe) &&
        getOriginalConstKind? publicStrict `Omega.TypeName.mk == some .defn do
      throw <| IO.userError "the public type name constructor has no executable definition"
  if strict.contains strictReader && strict.contains `Omega.TypeName.typeName then
    unless Compiler.getImplementedBy? publicStrict `Omega.TypeName.typeName == some strictReader do
      throw <| IO.userError "the public type name accessor has no implementation"
  let familyType (α : Name) := mkApp (mkConst `Omega.NonemptyType.type [.zero]) (mkApp (mkConst `Omega.TypeNameData [.zero]) (mkConst α))
  let x := familyType `Bool
  let y := familyType `Nat
  for t in #[x,y,mkConst `Omega.Lean.Name] do
    unless (Kernel.check strict {} t).isOk do throw <| IO.userError s!"invalid name carrier probe {t}"
  if Kernel.isDefEqGuarded strict {} x y || Kernel.isDefEqGuarded strict {} x (mkConst `Omega.Lean.Name) then
    throw <| IO.userError "the private payload type or its index is exposed"

end OmegaChecks.InitPort.TypeName
