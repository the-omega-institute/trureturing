module

public import OmegaChecks.InitPort.Translation
import all OmegaChecks.InitPort.ReferencePut

open Lean
namespace OmegaChecks.InitPort.PointerHash

public def name := `ShareCommon.Object.ptrHash

/-- The official abbreviation converts the existing object observation to UInt64. -/
public def isOriginal (ci : ConstantInfo) (strict : Bool) : Bool := Id.run do
  let .defnInfo d := ci | return false
  let rename := if strict then InitKernelPort.portName else id
  unless d.name == rename name && d.safety == .unsafe && d.all == [d.name] &&
      d.levelParams.isEmpty && (d.hints matches .abbrev) do return false
  let obj := mkConst `ShareCommon.Object
  let ty := Expr.forallE `a obj (mkConst `UInt64) .default
  let body := Expr.lam `a obj (mkApp (mkConst `USize.toUInt64)
    (mkApp2 (mkConst `ptrAddrUnsafe [0]) obj (.bvar 0))) .default
  let tr := InitKernelPort.translate rename
  return ReferencePut.sameTerm d.type (tr ty) && ReferencePut.sameTerm d.value (tr body)

/-- Check the public reduction policy and the borrowing convention of each emitted entry.
The strict UInt64 is represented by its Nat-backed Fin field. -/
public def checkABI (env : Environment) (strict : Bool) : Bool := Id.run do
  let target := if strict then InitKernelPort.portName name else name
  let some (.fdecl _ args result ..) := IR.findEnvDecl env target | return false
  return getReducibilityStatusCore env target == .reducible &&
    args.map (fun p => (p.ty, p.borrow)) == #[(IR.IRType.tobject, true)] &&
    result == (if strict then IR.IRType.tobject else .uint64)

end OmegaChecks.InitPort.PointerHash
