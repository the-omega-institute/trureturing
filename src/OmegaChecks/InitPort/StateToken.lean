module
public import Lean
public import OmegaChecks.InitPort.Alternatives.StateToken
import all OmegaChecks.InitPort.Alternatives.StateToken
import Lean.Compiler.IR.CompilerM

open Lean

namespace OmegaChecks.InitPort.StateToken

/-- The concrete representative in the pinned private implementation. -/
private def representative (_ : Type) : NonemptyType.{0} := ⟨PUnit, ⟨PUnit.unit⟩⟩
private def nativeToken {σ : Type} (_ : σ) : PUnit.{1} := PUnit.unit

/-- Unpack the implementation of the existing opaque identity only while checking
the concrete native representation. The published token type retains the region index. -/
private def erased (env : Environment) (value : Expr) : MetaM Expr := do
  let some (.opaqueInfo ident) := env.find? `Lean.opaqueId | throwError "missing opaque identity"
  return value.replace fun
    | .const `Lean.opaqueId levels => some (ident.value.instantiateLevelParams ident.levelParams levels)
    | _ => none

/-- Even with every reducible body available, the private package keeps regions distinct
and hides the concrete unit carrier. Ordinary imports additionally seal the family. -/
public def checkAbstraction (env : Environment) : IO Unit := do
  let token (region : Name) := mkApp (mkConst `Omega.Void) (mkConst region)
  let a := token `Bool
  let b := token `Nat
  let unit := mkConst `PUnit [.succ .zero]
  for type in #[a, b, unit] do
    unless (Kernel.check env {} type).isOk do throw <| IO.userError "ill-typed state region check"
  if Kernel.isDefEqGuarded env {} a b || Kernel.isDefEqGuarded env {} a unit then
    throw <| IO.userError "state token regions or their private representation are exposed"

public def check (env : Environment) (native : OpaqueVal) (candidate : Expr) : IO Unit := do
  let family := native.name == `Void.nonemptyType
  let owner := env.getModuleIdx? `Init.System.ST
  let some (.opaqueInfo carrier) := env.find? `Void.nonemptyType | throw <| IO.userError "missing state token carrier"
  unless (family || native.name == `Void.mk) && owner.isSome && !native.isUnsafe &&
      [native.name, carrier.name, `Void, `Void.mk].all (fun n => env.getModuleIdxFor? n == owner) &&
      Kernel.isDefEqGuarded env {} carrier.value (mkConst ``representative) &&
      getExternNameFor env `c `Void.mk == some "lean_void_mk" do
    throw <| IO.userError "state token representation differs from the pinned implementation"
  let header ← IO.FS.readFile ((← findSysroot) / "include" / "lean" / "lean.h")
  unless header.contains "static inline lean_obj_res lean_void_mk(lean_obj_arg a) {\n    lean_dec(a);\n    return lean_box(0);\n}" do
    throw <| IO.userError "native token no longer returns the zero scalar"
  let some (.fdecl _ params .tobject (.inc kept 1 true false (.ret (.var returned))) _) :=
      IR.findEnvDecl env `Lean.opaqueId | throw <| IO.userError "unexpected opaque identity IR"
  let #[_, arg] := params | throw <| IO.userError "unexpected identity arguments"
  unless kept == arg.x && returned == arg.x do throw <| IO.userError "opaque function changes its argument"
  let model := if family then ``Alternatives.Void.nonemptyType else ``Alternatives.Void.mk
  unless Kernel.isDefEqGuarded env {} candidate (mkConst model) do
    throw <| IO.userError "state token differs from the common indexed package"
  let verify : MetaM Unit := do
    let simplified ← erased env candidate
    let target := if family then ``representative else ``nativeToken
    unless Kernel.isDefEqGuarded env {} simplified (mkConst target) do throwError "incorrect native representative"
    if !family then
      let interface ← Meta.deltaExpand native.type (· == `Void)
      let concrete := interface.replace fun
        | .const `Void.nonemptyType _ => some (mkConst ``Alternatives.Void.nonemptyType)
        | _ => none
      let .ok actual := Kernel.check env {} candidate | throwError "ill-typed state token"
      unless Kernel.isDefEqGuarded env {} actual concrete do throwError "state token belongs to another region"
  verify.run' |>.toIO' {fileName := "<region-indexed state token>", fileMap := default} {env}

end OmegaChecks.InitPort.StateToken
