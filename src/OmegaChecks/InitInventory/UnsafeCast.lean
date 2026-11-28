module
public import Lean
import OmegaChecks.InitPort.StrictReplay
import OmegaChecks.InitInventory.StateFactory

open Lean
namespace OmegaChecks.InitInventory.UnsafeCast

/-- Inspect the pinned weak-head reduction on its closed True-to-False input. Abstracting
its equality operand yields a safe contradiction from precisely the demanded equality. -/
public def reductionAxiom (env : Environment) : IO Name := do
  let helper := `unsafeCast._proof_1
  let error (part : String) := IO.userError s!"unexpected unsafeCast {part}"
  let owner := env.getModuleIdx? `Init.Prelude
  unless owner.isSome && [`unsafeCast, helper, `lcProof].all (env.getModuleIdxFor? · == owner) &&
      (env.find? `unsafeCast).any (fun c => c.isUnsafe && (c matches .defnInfo _)) &&
      (env.find? `lcProof).any (fun c => c.isUnsafe && c.isAxiom) do throw <| error "owner or declaration kind"
  let call := mkApp3 (mkConst `unsafeCast [0, 0]) (mkConst `True) (mkConst `False) (mkConst `True.intro)
  let .ok (.proj `PLift 0 lifted) := Kernel.whnf env {} call | throw <| error "result projection"
  unless lifted.isAppOfArity `ULift.down 2 do throw <| error "universe projection"
  let transport := lifted.appArg!
  unless transport.isAppOfArity `cast 4 do throw <| error "transport"
  let #[_, _, evidence, _] := transport.getAppArgs | throw <| error "transport arguments"
  unless evidence.equal (mkApp2 (mkConst helper [0, 0]) (mkConst `True) (mkConst `False)) do throw <| error "specialized equality helper"
  let .ok proof := Kernel.whnf env {} evidence | throw <| error "helper reduction"
  unless proof.isAppOfArity `lcProof 1 do throw <| error "helper axiom"
  let equality := proof.appArg!
  let some aux := env.find? helper | throw <| error "evidence declaration"
  let actual := (aux.type.instantiateLevelParams aux.levelParams [0, 0]).bindingBody!.instantiate1 (mkConst `True)
  let actual := actual.bindingBody!.instantiate1 (mkConst `False)
  unless Kernel.isDefEqGuarded env {} actual equality do throw <| error "specialized equality"
  let h := mkFVar ⟨`h⟩
  let body := (Expr.proj `PLift 0 lifted).replace fun e => if e.equal evidence then some h else none
  let witness := Expr.lam `h equality (body.abstract #[h]) .default
  let statement := Expr.forallE `h equality (mkConst `False) .default
  let .ok inferred := Kernel.check env {} witness | throw <| error "safe witness term"
  unless Kernel.isDefEqGuarded env {} inferred statement do throw <| error "safe witness type"
  discard <| OmegaChecks.InitPort.replayStrict env.toKernelEnv (witness.getUsedConstants ++ statement.getUsedConstants)
  return proof.getAppFn.constName!

/-- Inspect the exposed factory reader and match its actual transport operand to the
zero-axiom diagonal refutation. The factory writer is absent from that operand. -/
public def factoryReductionAxiom (env witnesses : Environment) : IO Name := do
  let reader := `ShareCommon.StateFactory.get
  let error (part : String) := IO.userError s!"unexpected pinned {reader} {part}"
  let some (.defnInfo d) := env.find? reader | throw <| error "definition"
  unless d.safety == .unsafe && d.value.isAppOfArity `unsafeCast 2 &&
      env.getModuleIdxFor? reader == env.getModuleIdx? `Init.ShareCommon do throw <| error "cast body"
  let .ok (.proj `PLift 0 lifted) := Kernel.whnf env {} (mkApp d.value (mkFVar ⟨`factory⟩))
    | throw <| error "result projection"
  unless lifted.isAppOfArity `ULift.down 2 do throw <| error "universe projection"
  let transport := lifted.appArg!
  unless transport.isAppOfArity `cast 4 do throw <| error "transport"
  let evidence := transport.getAppArgs[2]!
  unless evidence.isAppOfArity `unsafeCast._proof_1 2 do throw <| error "equality helper"
  let .ok proof := Kernel.whnf env {} evidence | throw <| error "equality operand"
  let some witness := witnesses.find? ``OmegaChecks.InitBoundaries.FactoryCarriers.noGetCast | throw <| error "witness"
  unless proof.isAppOfArity `lcProof 1 && witness.type.isForall &&
      Kernel.isDefEqGuarded env {} witness.type.bindingDomain! proof.appArg! &&
      witness.type.bindingBody!.isConstOf `False do throw <| error "carrier refutation"
  return `lcProof

end OmegaChecks.InitInventory.UnsafeCast
