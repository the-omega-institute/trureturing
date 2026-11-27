module
public import Lean
public import Init.Data.Iterators.Consumers.Monadic.Loop
import all Init.Data.Iterators.Consumers.Monadic.Loop
import all Init.WFExtrinsicFix

open Lean Std Std.Iterators

namespace OmegaChecks.InitPort.LawfulLoop

@[expose] public def reference {α : Type w} {m : Type w → Type w'} {β : Type w} [Iterator α m β]
    {n : Type x → Type x'} [Monad n] (lift : ∀ γ δ, (γ → n δ) → m γ → n δ) (γ : Type x)
    (Pl : β → γ → ForInStep γ → Prop) (_wf : IteratorLoop.WellFounded α m Pl)
    (it : IterM (α := α) m β) (init : γ)
    (f : (b : β) → it.IsPlausibleIndirectOutput b → (c : γ) → n (Subtype (Pl b c))) : n γ :=
  IteratorLoop.defaultImplementation.forIn lift γ Pl it init f

@[expose] public def implementation.{w,w',x,x'} : type_of% @reference.{w,w',x,x'} :=
  fun {_ _ _} _ {_} _ lift γ Pl wf it init f =>
    IterM.DefaultConsumers.forIn'.wf lift γ Pl wf it init _ (fun _ => id) f

private theorem agreeOn {m : Type w → Type w'} {α : Type w} {β : Type w}
    [Iterator α m β]
    {n : Type x → Type x'} [Monad n]
    {lift : ∀ γ δ, (γ → n δ) → m γ → n δ} {γ : Type x}
    (Pl : β → γ → ForInStep γ → Prop)
    (wf : IteratorLoop.WellFounded α m Pl)
    {it : IterM (α := α) m β} {init : γ}
    {P : β → Prop} {hP : ∀ b, it.IsPlausibleIndirectOutput b → P b}
    (f : (b : β) → P b → (c : γ) → n (Subtype (Pl b c))) :
    IterM.DefaultConsumers.forIn' lift γ Pl it init P hP f =
      IterM.DefaultConsumers.forIn'.wf lift γ Pl wf it init P hP f := by
  haveI : Nonempty γ := ⟨init⟩
  rw [IterM.DefaultConsumers.forIn', WellFounded.extrinsicFix₃_eq_fix]; rotate_left
  · apply InvImage.wf
    exact wf
  · fun_induction IterM.DefaultConsumers.forIn'.wf lift γ Pl wf it init P hP f
    rename_i ihy ihs
    rw [WellFounded.fix_eq]
    congr 1; ext step
    cases step.inflate using PlausibleIterStep.casesOn
    · apply congrArg (Bind.bind (f _ _ _)); funext forInStep
      match forInStep with
      | ⟨.yield c, h⟩ => simp (discharger := assumption) [ihy]
      | ⟨.done c, h⟩ => simp
    · simp (discharger := assumption) [ihs]
    · simp

/-- The field supplies termination for this callback. Congruence of bind works for every monad. -/
public theorem agreement.{w,w',x,x'} : @reference.{w,w',x,x'} = @implementation.{w,w',x,x'} := by
  funext α m β iter n monad lift γ Pl wf it init f
  exact agreeOn Pl wf f

public def owner := `Init.Data.Iterators.Consumers.Monadic.Loop
public def helper := mkPrivateNameCore owner `Std.IterM.DefaultConsumers.forInWithWF
public def strictHelper := mkPrivateNameCore (owner.replacePrefix `Init `OmegaInit)
  `Omega.Std.IterM.DefaultConsumers.forInWithWF

/-- A finite iterator supplies termination for every callback, so the entire default
instance is represented by its checked well-founded projection. -/
public def specializeFiniteDefault? (sub : Expr) : MetaM (Option Expr) := do
  unless sub.getAppFn.isConstOf ``IteratorLoop.defaultImplementation do return none
  let #[β, α, m, n, monad, iter] := sub.getAppArgs | return none
  let constraint ← Meta.mkAppOptM ``Finite #[α, m, β, iter]
  let some fin ← Meta.synthInstance? constraint | return none
  let constructor := mkAppN (mkConst ``IteratorLoop.mk sub.getAppFn.constLevels!) #[α, m, β, iter, n]
  let .forallE _ field _ _ ← Meta.whnf (← Meta.inferType constructor) | return none
  Meta.forallBoundedTelescope field (some 6) fun xs _ => do
    let #[lift, γ, pl, it, init, f] := xs | return none
    let wf ← Meta.mkAppOptM ``IteratorLoop.wellFounded_of_finite #[m, α, β, γ, iter, fin, pl]
    let call ← Meta.mkAppOptM helper #[α, m, β, iter, n, monad, lift, γ, pl, wf, it, init, f]
    return some (mkApp constructor (← Meta.mkLambdaFVars xs call))

/-- The source alias unfolds to the original projection. Only calls carrying the exact local
termination witness can be expressed through it. -/
public def specialize? (sub : Expr) : MetaM (Option Expr) := do
  if sub.getAppFn.isConstOf ``IteratorLoop.defaultImplementation then return ← specializeFiniteDefault? sub
  unless sub.getAppFn.isConstOf ``IteratorLoop.forIn do return none
  let #[α, m, β, iter, n, loop, lift, γ, pl, it, init, f] := sub.getAppArgs | return none
  unless loop.getAppFn.isConstOf ``IteratorLoop.defaultImplementation do return none
  let #[_, _, _, _, monad, _] := loop.getAppArgs | return none
  let expected ← Meta.mkAppOptM ``IteratorLoop.WellFounded #[α, m, β, iter, γ, pl]
  let some wf ← (← getLCtx).getFVars.findSomeM? (fun var => do
    let t ← Meta.inferType var
    return if t.getAppFn.isConstOf ``IteratorLoop.WellFounded && (← Meta.isDefEq t expected) then some var else none)
    | return none
  return some (← Meta.mkAppOptM helper #[α, m, β, iter, n, monad, lift, γ, pl, wf, it, init, f])

/-- Only the reference environment receives this transparent alias of the pinned projection. -/
public def addReference (source templates : Environment) : IO Environment := do
  unless source.contains ``IteratorLoop.defaultImplementation do return source
  let some (.defnInfo ref) := templates.find? ``reference | throw <| IO.userError "missing loop reference"
  let decl := Declaration.defnDecl {ref with name := helper, all := [helper]}
  match source.addDeclCore 0 1000 decl none with
  | .ok out => return out
  | .error e => throw <| IO.userError (← e.toMessageData {} |>.toString)

/-- In the isolated module the same private helper computes the terminating loop. Its
complete function is compared with the two sides of the checked universal equality. -/
public def check (strict standard : Environment) (translateTerm : Expr → Expr) : IO (Array Name) := do
  let some (.defnInfo actual) := strict.find? strictHelper | throw <| IO.userError "missing strict well-founded loop"
  let some (.defnInfo ref) := standard.find? ``reference | throw <| IO.userError "missing loop reference"
  let some (.thmInfo proof) := standard.find? ``agreement | throw <| IO.userError "missing loop equality"
  let levels := actual.levelParams.map Level.param
  let mappedType := translateTerm actual.type
  let body := translateTerm actual.value
  let refTerm := mkConst ref.name levels
  let .ok (.sort u) := Kernel.check standard {} mappedType | throw <| IO.userError "invalid loop type"
  let equation := mkApp3 (mkConst `Eq [u]) mappedType refTerm body
  unless actual.safety == .safe && actual.all == [strictHelper] && levels.length == ref.levelParams.length &&
      proof.levelParams.length == levels.length &&
      strict.getModuleIdxFor? strictHelper == strict.getModuleIdx? (owner.replacePrefix `Init `OmegaInit) &&
      Kernel.isDefEqGuarded standard {} mappedType (ref.type.instantiateLevelParams ref.levelParams levels) &&
      Kernel.isDefEqGuarded standard {} equation (proof.type.instantiateLevelParams proof.levelParams levels) do
    throw <| IO.userError "well-founded loop does not implement the certified function"
  let axs ← (collectAxioms proof.name : CoreM _).toIO' {fileName := "<well-founded loop>", fileMap := default} {env := standard}
  unless axs.all (#[`propext, `Classical.choice, `Quot.sound].contains ·) do
    throw <| IO.userError "unexpected assumption in the loop correspondence"
  return actual.type.getUsedConstants ++ actual.value.getUsedConstants

end OmegaChecks.InitPort.LawfulLoop
