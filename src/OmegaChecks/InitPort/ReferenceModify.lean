module
public import Lean
public import OmegaChecks.InitPort.Translation
import all Init.System.ST

open Lean
namespace OmegaChecks.InitPort.ReferenceModify

/-- The option lets the logical read be inhabited for every payload type. Native reads
always produce the value stored in the cell. -/
private opaque read? {σ α : Type} (_ : @& ST.Ref σ α) : ST σ (Option α) := ST.pure none

private def modify {σ α : Type} (r : ST.Ref σ α) (f : α → α) : ST σ Unit := fun world =>
  let out := read? r world
  Option.casesOn (motive := fun _ => ST.Out σ Unit) out.val
    ⟨(), out.state⟩ (fun a => ST.Prim.Ref.set r (f a) out.state)

private def wrapRead {σ α : Type} (r : ST.Ref σ α) : ST σ (Option α) := fun world =>
  let out := ST.Prim.Ref.get r world
  ⟨some out.val, out.state⟩

private unsafe def atomic {σ α : Type} (r : ST.Ref σ α) (f : α → α) : ST σ Unit := do
  let v ← ST.Prim.Ref.take r
  ST.Prim.Ref.put r (f v)

public def owner := `Init.System.ST
public def consumer := `ST.Prim.Ref.modify
public def support := mkPrivateNameCore owner `ST.Prim.Ref.readForModify

public def implementation := `ST.Prim.Ref.modifyUnsafe

public def checkImplementation (src : Environment) (native : DefinitionVal) (body : Expr) : IO Unit := do
  let some (.defnInfo original) := src.find? consumer | throw <| IO.userError "missing atomic reference update"
  unless native.name == implementation && native.safety == .unsafe && original.safety == .safe &&
      src.getModuleIdxFor? native.name == src.getModuleIdx? owner && src.getModuleIdxFor? consumer == src.getModuleIdx? owner &&
      Compiler.getImplementedBy? src consumer == some native.name && body == mkConst consumer &&
      Kernel.isDefEqGuarded src {} original.type native.type do
    throw <| IO.userError "unexpected implementation of the pinned atomic update"

public def model (src templates : Environment) : IO ConstantInfo := do
  let some (.opaqueInfo r) := templates.find? ``read? | throw <| IO.userError "missing optional read template"
  let some (.defnInfo impl) := src.find? `ST.Prim.Ref.modifyUnsafe | throw <| IO.userError "missing atomic update"
  let some (.defnInfo expected) := templates.find? ``atomic | throw <| IO.userError "missing atomic update specification"
  unless impl.safety == .unsafe && Kernel.isDefEqGuarded src {} impl.value expected.value &&
      src.getModuleIdxFor? `ST.Prim.Ref.get == src.getModuleIdx? owner &&
      getExternNameFor src `c `ST.Prim.Ref.get == some "lean_st_ref_get" &&
      Compiler.getImplementedBy? src consumer == some `ST.Prim.Ref.modifyUnsafe && !src.contains support do
    throw <| IO.userError "unexpected pinned read or update primitive"
  return .opaqueInfo {r with name := support, all := [support]}

public def restore (templates : Environment) (e : Expr) : IO Expr := do
  let some (.defnInfo official) := templates.find? ``wrapRead | throw <| IO.userError "missing pinned update read"
  return e.replace fun t => if t.isConstOf support then some official.value else none

/-- Expanding the private read as an official read followed by `some` makes the
optional branch reduce to the pinned read, callback and write. -/
public def body (src templates : Environment) (d : DefinitionVal) : IO Expr := do
  let some (.defnInfo candidate) := templates.find? ``modify | throw <| IO.userError "missing reference update template"
  let e := candidate.value.replace fun t => if t.isConstOf ``read? then some (mkConst support) else none
  unless d.name == consumer && d.levelParams == candidate.levelParams &&
      Kernel.isDefEqGuarded src {} candidate.type d.type && Kernel.isDefEqGuarded src {} (← restore templates e) d.value do
    throw <| IO.userError "reference update does not implement the pinned read and write"
  return e

end OmegaChecks.InitPort.ReferenceModify
