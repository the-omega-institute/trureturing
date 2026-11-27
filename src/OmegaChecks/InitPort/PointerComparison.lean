module

public import OmegaChecks.InitPort.Translation
import all OmegaChecks.InitPort.ReferencePut

open Lean
namespace OmegaChecks.InitPort.PointerComparison

public def names := [`ptrEq, `withPtrEqUnsafe]

public def hasBorrowedABI (env : Environment) (name : Name) (strict : Bool) : Bool := Id.run do
  unless names.contains name do return false
  let target := if strict then InitKernelPort.portName name else name
  let some (.fdecl _ args .uint8 ..) := IR.findEnvDecl env target | return false
  let values := #[(IR.IRType.erased, false), (.tobject, true), (.tobject, true)]
  let expected := if name == `ptrEq then values else values ++ #[(.object, false), (.erased, false)]
  return args.map (fun p => (p.ty, p.borrow)) == expected

private def argument (n : Name) (ty body : Expr) := Expr.forallE n ty body .default

private def lambdaBody (type body : Expr) : Expr := match type with
  | .forallE n t b bi => .lam n t.consumeMData (lambdaBody b body) bi
  | _ => body

/-- The pinned transparent terms use word equality and the guarded callback on Unit. -/
public def isOriginal (ci : ConstantInfo) (strict : Bool) : Bool := Id.run do
  let .defnInfo d := ci | return false
  let [u] := d.levelParams | return false
  let name := if strict then InitKernelPort.originalName d.name else d.name
  unless names.contains name && d.safety == .unsafe && d.all == [d.name] do return false
  let level := Level.param u
  let bl := mkConst `Bool
  let yes := mkConst `Bool.true
  let word := mkConst `USize
  let unit := mkConst `Unit
  let unitValue := mkConst `Unit.unit
  let (result, body) := if name == `ptrEq then
    let beq := mkApp2 (mkConst `instBEqOfDecidableEq [0]) word (mkConst `instDecidableEqUSize)
    let addr := mkApp (mkConst `ptrAddrUnsafe [level]) (.bvar 2)
    (bl, mkApp4 (mkConst `BEq.beq [0]) word beq (mkApp addr (.bvar 1)) (mkApp addr (.bvar 0)))
  else
    let equal := mkApp3 (mkConst `Eq [.succ level]) (.bvar 3) (.bvar 2) (.bvar 1)
    let eqTrue (x : Expr) := mkApp3 (mkConst `Eq [1]) bl x yes
    let law := argument .anonymous equal (eqTrue (mkApp (.bvar 1) unitValue))
    let callbacks := argument `k (argument .anonymous unit bl) (argument `h law bl)
    let test := mkApp3 (mkConst `ptrEq [level]) (.bvar 4) (.bvar 3) (.bvar 2)
    let decide := mkApp2 (mkConst `instDecidableEqBool) test yes
    (callbacks, mkApp5 (mkConst `ite [1]) bl (eqTrue test) decide yes (mkApp (.bvar 1) unitValue))
  let ty := Expr.forallE `α (.sort (.succ level)) (argument `a (.bvar 0)
    (argument `b (.bvar 1) result)) .implicit
  let tr := InitKernelPort.translate (if strict then InitKernelPort.portName else id)
  return ReferencePut.sameTerm d.type (tr ty) && ReferencePut.sameTerm d.value (tr (lambdaBody ty body))

/-- Independently typecheck the dependency chain under safe copies and install only the unsafe originals. -/
public def replay (checked installed : Kernel.Environment) (constants : Std.HashMap Name ConstantInfo) :
    IO Kernel.Environment := do
  let mut safe := checked
  let mut actual := installed
  let add (env : Kernel.Environment) (d : DefinitionVal) := do
    match env.addDeclCore 0 1000 (.defnDecl d) none with
    | .ok next => pure next
    | .error e => throw <| IO.userError s!"kernel rejected {d.name}: {← e.toMessageData {} |>.toString}"
  for name in names do
    let some ci := constants[InitKernelPort.portName name]? | continue
    unless isOriginal ci true do throw <| IO.userError s!"invalid transparent pointer comparison {name}"
    let .defnInfo d := ci | throw <| IO.userError s!"expected definition {name}"
    safe ← add safe {d with safety := .safe}
    actual ← add actual d
  return actual

end OmegaChecks.InitPort.PointerComparison
