module
public import OmegaChecks.InitPort.Translation
import all OmegaChecks.InitPort.ReferencePut

open Lean

namespace OmegaChecks.InitPort.Address

public def name := `withPtrAddrUnsafe

/-- Match the entire dependent signature and the pinned transparent callback application. -/
public def isOriginal (ci : ConstantInfo) (strict : Bool) : Bool := Id.run do
  let .defnInfo d := ci | return false
  let rename := if strict then InitKernelPort.portName else id
  let [u, v] := d.levelParams.map Level.param | return false
  unless d.name == rename name && d.all == [d.name] && d.safety == .unsafe do return false
  let arg := ReferencePut.forallArg .default
  let implicitArg := ReferencePut.forallArg .implicit
  let word := mkConst `USize
  let eq := mkApp3 (mkConst `Eq [v.succ]) (.bvar 4) (mkApp (.bvar 2) (.bvar 1)) (mkApp (.bvar 2) (.bvar 0))
  let law := arg word (arg word eq)
  let callback := arg word (.bvar 2)
  let type := implicitArg (.sort u.succ) (implicitArg (.sort v.succ) (arg (.bvar 1) (arg callback (arg law (.bvar 3)))))
  let body := mkApp (.bvar 1) (mkApp2 (mkConst `ptrAddrUnsafe [u]) (.bvar 4) (.bvar 2))
  let tr := InitKernelPort.translate rename
  return ReferencePut.sameTerm d.type (tr type) && ReferencePut.sameTerm d.value (tr (ReferencePut.lambdaBody body type))

public def hasBorrowedABI (env : Environment) (strict : Bool) : Bool := Id.run do
  let target := if strict then InitKernelPort.portName name else name
  let some (.fdecl _ args .tobject ..) := IR.findEnvDecl env target | return false
  return args.map (fun p => (p.ty, p.borrow)) ==
    #[(IR.IRType.erased, false), (.erased, false), (.tobject, true), (.tobject, false), (.erased, false)]

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
