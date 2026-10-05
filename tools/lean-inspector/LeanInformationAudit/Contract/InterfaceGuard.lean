import LeanInformationAudit.Contract.SourceAudit

namespace LeanInformationAudit.Contract.InterfaceGuard
open Lean

/-- Fixed companion families emitted by the pinned Lean compiler. Constructor
and projection names come from kernel/structure metadata, not source spelling.
An unrecognized compiler product fails closed alongside authored constants. -/
def family (env : Environment) (type : Name) : Except String NameSet := do
  let some (.inductInfo info) := env.find? type
    | throw s!"contract.interface:compiled_type_missing:{type}"
  let mut allowed : NameSet := ({} : NameSet).insert type
  for suffix in #[`rec, `recOn, `casesOn, `noConfusion, `noConfusionType,
      `ctorIdx, `ctorElim, `ctorElimType, `_sizeOf_1, `_sizeOf_inst] do
    allowed := allowed.insert (type ++ suffix)
  for ctor in info.ctors do
    allowed := allowed.insert ctor
    for suffix in #[`inj, `injEq, `noConfusion, `elim, `sizeOf_spec, `_flat_ctor] do
      allowed := allowed.insert (ctor ++ suffix)
  if isStructure env type then
    for projection in getStructureFields env type do
      allowed := allowed.insert (type ++ projection)
  return allowed

/-- Check compiler-owned contract types and their dependency products. -/
def audit (env : Environment) (owner : Name) : Except String Unit := do
  let some idx := env.getModuleIdx? owner
    | throw s!"contract.interface:module_missing:{owner}"
  let names := env.header.moduleData[idx.toNat]!.constNames
  let mut allowed : NameSet := {}
  for name in names do
    match env.find? name with
    | some (.inductInfo _) =>
      for entry in (← family env name).toArray do allowed := allowed.insert entry
    | some (.defnInfo info) =>
      if info.type.getForallBody.isSort then
        let mut pending := #[name]
        while !pending.isEmpty do
          let next := pending.back!
          pending := pending.pop
          if allowed.contains next then continue
          allowed := allowed.insert next
          if let some dependency := env.find? next then
            let used := dependency.type.getUsedConstants ++
              ((dependency.value? (allowOpaque := true)).map Expr.getUsedConstants |>.getD #[])
            pending := pending ++ used.filter names.contains
    | _ => pure ()
  for name in names do
    let compilerEquation := match name with
      | .str parent suffix => allowed.contains parent && isReservedName env name &&
          (suffix == "eq_def" || (suffix.startsWith "eq_" && (suffix.drop 3).toString.toNat?.isSome))
      | _ => false
    unless allowed.contains name || compilerEquation do
      throw s!"contract.interface:compiled_non_type:{owner}:{name}"

end LeanInformationAudit.Contract.InterfaceGuard
