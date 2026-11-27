module
public import Lean
public import OmegaChecks.InitPort.ReferenceModify
import all Init.Data.Random

open Lean
namespace OmegaChecks.InitPort.RandomState

private opaque global (_ : Unit) : IO.Ref StdGen :=
  ⟨((ST.Prim.mkRef (σ := Unit) () (Void.mk ())).val).ref, ⟨mkStdGen 0⟩⟩

private def initRef : IO (IO.Ref StdGen) := do
  let seed := UInt64.toNat (ByteArray.toUInt64LE! (← IO.getRandomBytes 8))
  IO.mkRef (mkStdGen seed)

private def draw (read : IO.Ref StdGen → BaseIO (Option StdGen)) (lo hi : Nat) : BaseIO Nat := do
  let gen ← read IO.stdGenRef
  let pair := randNat (gen.getD (mkStdGen 0)) lo hi
  IO.stdGenRef.set pair.2
  pure pair.1

public def owner := `Init.Data.Random
public def refName := `IO.stdGenRef
public def support := mkPrivateNameCore owner `IO.stdGenRef.acquire

public def model (src templates : Environment) : IO ConstantInfo := do
  let some (.opaqueInfo accessor) := templates.find? ``global | throw <| IO.userError "missing generator accessor"
  let some initializer := getRegularInitFnNameFor? src refName | throw <| IO.userError "missing standard generator initializer"
  let some (.defnInfo init) := src.find? initializer | throw <| IO.userError "missing pinned initializer body"
  let some (.defnInfo expected) := templates.find? ``initRef | throw <| IO.userError "missing initializer specification"
  unless !src.contains support && src.getModuleIdxFor? refName == src.getModuleIdx? owner &&
      src.getModuleIdxFor? initializer == src.getModuleIdx? owner && Kernel.isDefEqGuarded src {} init.value expected.value do
    throw <| IO.userError "unexpected standard generator initialization"
  let value := accessor.value.replace fun sub => do
    let n ← sub.constName?
    let .thmInfo proof ← templates.find? n | none
    guard (templates.getModuleIdxFor? n == templates.getModuleIdxFor? accessor.name)
    return proof.value
  return .opaqueInfo {accessor with name := support, value, all := [support]}

public def refBody := mkApp (mkConst support) (mkConst `Unit.unit)

public def drawBody (src templates : Environment) (d : DefinitionVal) : IO Expr := do
  let some (.defnInfo template) := templates.find? ``draw | throw <| IO.userError "missing standard generator draw template"
  let read := mkApp2 (mkConst ReferenceModify.support) (mkConst `IO.RealWorld) (mkConst `StdGen)
  let e := template.value.beta #[read]
  unless d.name == `IO.rand && Kernel.isDefEqGuarded src {} (← ReferenceModify.restore templates e) d.value do
    throw <| IO.userError "random draw differs from the pinned read, generation and update"
  return e

end OmegaChecks.InitPort.RandomState
