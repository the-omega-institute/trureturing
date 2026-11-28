module
public import OmegaChecks.InitPort.RangeFix
public import Init.Data.Iterators.Consumers.Monadic.Loop
import all Init.Data.Iterators.Consumers.Monadic.Loop
import all Init.WFExtrinsicFix

open Lean Std Std.Iterators

namespace OmegaChecks.InitPort.LawfulLoop

@[expose] public def reference.{w,w',x,x'} : type_of% @IterM.DefaultConsumers.forIn'.wf.{w,w',x,x'} :=
  fun {_ _ _} _ {_} _ lift γ pl _ it init P hp f =>
    IterM.DefaultConsumers.forIn' lift γ pl it init P hp f

@[expose] public def implementation.{w,w',x,x'} : type_of% @reference.{w,w',x,x'} :=
  @IterM.DefaultConsumers.forIn'.wf

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
  funext m α β iter n monad lift γ Pl wf it init P hp f
  exact agreeOn Pl wf f

public def owner := `Init.Data.Iterators.Consumers.Monadic.Loop
public def helper := mkPrivateNameCore owner `Std.IterM.DefaultConsumers.forInWithWF
public structure Rule where
  owner : Name
  helper : Name
  trigger : Name
  reference : Name
  implementation : Name
  agreement : Name

public def rules : List Rule := [
  ⟨owner, helper, ``IteratorLoop.defaultImplementation, ``reference, ``implementation, ``agreement⟩,
  ⟨RangeFix.owner, RangeFix.helper, ``Rxc.Iterator.instIteratorLoop.loop, ``RangeFix.reference,
    ``RangeFix.implementation, ``RangeFix.agreement⟩]

private def project (α m β iter n monad lift γ pl wf it init f : Expr) : MetaM Expr := do
  let predicate ← Meta.mkAppOptM ``IterM.IsPlausibleIndirectOutput #[α, β, m, iter, it]
  let witness ← Meta.mkAppOptM ``IteratorLoop.defaultImplementation._proof_1 #[β, α, m, iter, it]
  Meta.mkAppOptM helper #[m, α, β, iter, n, monad, lift, γ, pl, wf, it, init, predicate, witness, f]

private def termination? (α m β iter γ pl : Expr) : MetaM (Option Expr) := do
  let expected ← Meta.mkAppOptM ``IteratorLoop.WellFounded #[α, m, β, iter, γ, pl]
  if let some wf ← (← getLCtx).getFVars.findSomeM? (fun var => do
    let t ← Meta.inferType var
    return if t.getAppFn.isConstOf ``IteratorLoop.WellFounded && (← Meta.isDefEq t expected) then some var else none) then
    return some wf
  let constraint ← Meta.mkAppOptM ``Finite #[α, m, β, iter]
  let some fin ← Meta.synthInstance? constraint | return none
  return some (← Meta.mkAppOptM ``IteratorLoop.wellFounded_of_finite #[m, α, β, γ, iter, fin, pl])

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
    let call ← project α m β iter n monad lift γ pl wf it init f
    return some (mkApp constructor (← Meta.mkLambdaFVars xs call))

/-- The source alias unfolds to the original projection. Only calls carrying the exact local
termination witness can be expressed through it. -/
public def specialize? (sub : Expr) : MetaM (Option Expr) := do
  if sub.getAppFn.isConstOf ``IteratorLoop.defaultImplementation then return ← specializeFiniteDefault? sub
  if sub.getAppFn.isConstOf ``IterM.DefaultConsumers.forIn' then
    let #[m, α, β, iter, n, monad, lift, γ, pl, it, init, p, hp, f] := sub.getAppArgs | return none
    let some wf ← termination? α m β iter γ pl | return none
    return some (← Meta.mkAppOptM helper #[m, α, β, iter, n, monad, lift, γ, pl, wf, it, init, p, hp, f])
  unless sub.getAppFn.isConstOf ``IteratorLoop.forIn do return none
  let #[α, m, β, iter, n, loop, lift, γ, pl, it, init, f] := sub.getAppArgs | return none
  unless loop.getAppFn.isConstOf ``IteratorLoop.defaultImplementation do return none
  let #[_, _, _, _, monad, _] := loop.getAppArgs | return none
  let some wf ← termination? α m β iter γ pl | return none
  return some (← project α m β iter n monad lift γ pl wf it init f)

/-- The reference environment uses transparent aliases of the pinned operations. -/
public def addReferences (source templates : Environment) : IO Environment := do
  let mut env := source
  for rule in rules do
    unless source.contains rule.trigger do continue
    let some (.defnInfo ref) := templates.find? rule.reference | throw <| IO.userError s!"missing {rule.reference}"
    let decl := Declaration.defnDecl {ref with name := rule.helper, all := [rule.helper]}
    match env.addDeclCore 0 1000 decl none with
    | .ok out => env := out
    | .error e => throw <| IO.userError (← e.toMessageData {} |>.toString)
  return env

end OmegaChecks.InitPort.LawfulLoop
