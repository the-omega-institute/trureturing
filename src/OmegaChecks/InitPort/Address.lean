module
public import Lean

open Lean

namespace OmegaChecks.InitPort.Address

/-- Check the pinned implementation and the continuation's result for every possible
machine address. The primitive's runtime address is never interpreted by the kernel. -/
public def check (env : Environment) (native : DefinitionVal) (candidate : Expr) : IO Unit := do
  let some (.defnInfo reference) := env.find? `withPtrAddr
    | throw <| IO.userError "missing safe address reference"
  let levels := native.levelParams.map Level.param
  let owner := env.getModuleIdx? `Init.Util
  unless native.name == `withPtrAddrUnsafe && native.safety == .unsafe && reference.safety == .safe &&
      owner.isSome && [native.name, reference.name, `ptrAddrUnsafe].all (fun n => env.getModuleIdxFor? n == owner) &&
      Compiler.getImplementedBy? env reference.name == some native.name &&
      reference.levelParams.length == native.levelParams.length &&
      (reference.type.instantiateLevelParams reference.levelParams levels).equal native.type &&
      candidate.equal (.const reference.name levels) do
    throw <| IO.userError "invalid address implementation or safe reference"
  let refBody := reference.value.instantiateLevelParams reference.levelParams levels
  let certify : MetaM Unit := Meta.forallTelescope native.type fun args _ => do
    let #[α, _, a, k, h] := args | throwError "unexpected pointer continuation inputs"
    let actual := native.value.beta args
    let .app continuation address := actual | throwError "unexpected native address result"
    unless continuation == k && address.isAppOfArity `ptrAddrUnsafe 2 &&
        address.getAppArgs == #[α, a] do throwError "unexpected native address computation"
    let .app f representative := refBody.beta args | throwError "unexpected safe address result"
    unless f == k do throwError "unexpected safe address continuation"
    Meta.withLocalDeclD `address (mkConst `USize) fun w => do
      let target ← Meta.mkEq (mkApp k w) (mkAppN candidate args)
      let proof := mkApp2 h w representative
      let closed ← Meta.mkLambdaFVars (args.push w) proof
      let statement ← Meta.mkForallFVars (args.push w) target
      let .ok inferred := Kernel.check env {} closed | throwError "invalid address independence proof"
      unless Kernel.isDefEqGuarded env {} inferred statement do
        throwError "address independence proof has the wrong result"
  certify.run' |>.toIO' {fileName := "<address-independent continuation>", fileMap := default} {env}

end OmegaChecks.InitPort.Address
