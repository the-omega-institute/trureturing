module
public import Lean
public import OmegaChecks.InitPort.Translation
import all Init.Control.StateRef
import all Init.Internal.Order.Basic

open Lean
namespace OmegaChecks.InitPort.StateRunner

private opaque read {ω σ : Type} (initial : σ) (_ : @& ST.Ref ω σ) : ST ω σ :=
  ST.pure initial

private def run {ω σ : Type} {m : Type → Type} [Monad m] [MonadLiftT (ST ω) m] {α : Type}
    (x : StateRefT' ω σ m α) (s : σ) : m (α × σ) := do
  let r ← ST.mkRef s
  let a ← x r
  let s ← liftM (read s r)
  pure (a, s)

private def first {ω σ : Type} {m : Type → Type} [Monad m] [MonadLiftT (ST ω) m] {α : Type}
    (x : StateRefT' ω σ m α) (s : σ) : m α := do
  let pair ← x.run s
  pure pair.1

open _root_.Lean.Order in
private theorem monotoneRun.{u} {γ : Sort u} {m : Type → Type} {ω σ α : Type}
    [PartialOrder γ] [Monad m] [MonadLiftT (ST ω) m] [∀ t, PartialOrder (m t)] [MonoBind m]
    (f : γ → StateRefT' ω σ m α) (ordered : ∀ x y, x ⊑ y → ∀ r, f x r ⊑ f y r) (s : σ) :
    monotone (fun x => run (f x) s) := by
  intro x y xy
  apply MonoBind.bind_mono_right
  intro r
  exact MonoBind.bind_mono_left (ordered x y xy r)

public def monotonicity := `Lean.Order.monotone_stateRefT'Run

public def owner := `Init.Control.StateRef
public def support := mkPrivateNameCore owner `StateRefT'.readWithInitial
public def consumers := [`StateRefT'.run, `StateRefT'.run']

private def renameRead (e : Expr) := e.replace fun t =>
  if t.isConstOf ``read then some (mkConst support) else none

/-- A returning read may use the supplied initial value to inhabit its logical result.
The public computation still calls the same reference primitive with the actual cell. -/
public def restore (e : Expr) := e.replace fun t => do
  guard (t.isAppOfArity support 3)
  let args := t.getAppArgs
  return mkApp2 (mkConst `ST.Prim.Ref.get) args[0]! args[1]!

/-- The monotonicity proof uses the same read as the checked implementation of the runner. -/
public def monotonicityProof (src templates : Environment) (expected : TheoremVal) (type : Expr) : IO Expr := do
  let some (.thmInfo th) := templates.find? ``monotoneRun | throw <| IO.userError "missing state runner monotonicity proof"
  let levels := expected.levelParams.map Level.param
  let external (e : Expr) := (renameRead (e.instantiateLevelParams th.levelParams levels)).replace fun node =>
    if node.isConstOf ``run then some (mkConst `StateRefT'.run) else none
  unless expected.name == monotonicity && th.levelParams.length == expected.levelParams.length &&
      Kernel.isDefEqGuarded src {} type expected.type && Kernel.isDefEqGuarded src {} (external th.type) type do
    throw <| IO.userError "state runner monotonicity differs from its pinned interface"
  return external th.value

public def model (src templates : Environment) : IO ConstantInfo := do
  let some (.opaqueInfo r) := templates.find? ``read | throw <| IO.userError "missing state runner read template"
  let some (.opaqueInfo get) := src.find? `ST.Prim.Ref.get | throw <| IO.userError "missing pinned reference read"
  unless !get.isUnsafe && src.getModuleIdxFor? get.name == src.getModuleIdx? `Init.System.ST &&
      getExternNameFor src `c get.name == some "lean_st_ref_get" && !src.contains support do
    throw <| IO.userError "unexpected state runner reference primitive"
  return .opaqueInfo {r with name := support, all := [support]}

public def body (src templates : Environment) (d : DefinitionVal) : IO Expr := do
  let template := if d.name == `StateRefT'.run then ``run else ``first
  let some (.defnInfo candidate) := templates.find? template | throw <| IO.userError "missing state runner template"
  let e := renameRead candidate.value
  unless consumers.contains d.name && d.levelParams == candidate.levelParams &&
      Kernel.isDefEqGuarded src {} candidate.type d.type && Kernel.isDefEqGuarded src {} (restore e) d.value do
    throw <| IO.userError "state runner differs from its pinned allocation, action and read"
  return e

end OmegaChecks.InitPort.StateRunner
