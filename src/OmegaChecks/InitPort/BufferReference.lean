module
public import Lean
public import OmegaChecks.InitPort.Translation
import all Init.System.IO

open Lean
namespace OmegaChecks.InitPort.BufferReference

private opaque read (_ : @& ST.Ref IO.RealWorld IO.FS.Stream.Buffer) : BaseIO IO.FS.Stream.Buffer :=
  ST.pure {}

public def owner := `Init.System.IO
public def operations := [`ST.Prim.Ref.get, `ST.Prim.Ref.modify, `ST.Prim.Ref.modifyGet]
public def consumers := [`IO.FS.Stream.ofBuffer, `IO.FS.withIsolatedStreams]
public def support (n : Name) := mkPrivateNameCore owner (.str `IO.FS.Stream.Buffer n.getString!)
public def strictName (n : Name) := InitKernelPort.portName (support n)

private def pinned (name : Name) := mkApp2 (mkConst name) (mkConst `IO.RealWorld) (mkConst `IO.FS.Stream.Buffer)

private def specialize (e : Expr) := e.replace fun t => do
  let n ← operations.find? (fun n => (pinned n).equal t)
  return mkConst (support n)

/-- Interpret each hidden buffer operation at the identical instantiation of the official primitive. -/
public def restore (e : Expr) := e.replace fun t => do
  let n ← operations.find? (fun n => t.isConstOf (support n))
  return pinned n

public def consumerBody (src : Environment) (d : DefinitionVal) : IO Expr := do
  let wrappers := [`ST.Ref.get, `ST.Ref.modify, `ST.Ref.modifyGet]
  let expanded ← (Meta.deltaExpand d.value (wrappers.contains ·)).toIO'
    {fileName := "<buffer operations>", fileMap := default} {env := src}
  let body := specialize expanded
  unless (body.getUsedConstants.any fun k => operations.any (fun op => k == support op)) &&
      !body.getUsedConstants.any operations.contains && Kernel.isDefEqGuarded src {} (restore body) d.value do
    throw <| IO.userError s!"unexpected buffer specialization at {d.name}"
  return body

/-- The read fallback inhabits the concrete buffer type. The update definitions retain the
pinned kernel computations and specialize their otherwise polymorphic reference reads. -/
public def models (src templates : Environment) : IO (Array ConstantInfo) := do
  let some (.opaqueInfo original) := src.find? `ST.Prim.Ref.get | throw <| IO.userError "missing pinned reference read"
  unless !original.isUnsafe && operations.all (fun n => src.getModuleIdxFor? n == src.getModuleIdx? `Init.System.ST &&
      !src.contains (support n)) do throw <| IO.userError "unexpected reference operation identity"
  let some (.opaqueInfo r) := templates.find? ``read | throw <| IO.userError "missing buffer read model"
  let mut results := #[ConstantInfo.opaqueInfo {r with name := support operations.head!, all := [support operations.head!]}]
  for op in operations do
    let term := pinned op
    let .ok type := Kernel.check src {} term | throw <| IO.userError s!"invalid buffer operation {op}"
    if op == `ST.Prim.Ref.get then
      unless !r.isUnsafe && Kernel.isDefEqGuarded src {} r.type type &&
          getExternNameFor src `c op == some "lean_st_ref_get" do throw <| IO.userError "different buffer read type or primitive"
      continue
    let some (.defnInfo official) := src.find? op | throw <| IO.userError s!"missing buffer update {op}"
    let expanded := official.value.beta #[mkConst `IO.RealWorld, mkConst `IO.FS.Stream.Buffer]
    let body := specialize expanded
    unless !body.getUsedConstants.any operations.contains && Kernel.isDefEqGuarded src {} (restore body) term &&
        Compiler.getImplementedBy? src op == some (op.appendAfter "Unsafe") do throw <| IO.userError s!"different atomic update {op}"
    let name := support op
    results := results.push (.defnInfo {official with name, type, value := body, all := [name]})
  return results

end OmegaChecks.InitPort.BufferReference
