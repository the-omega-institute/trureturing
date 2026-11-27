module
public import Lean
import all OmegaChecks.InitInventory.TransformerLaws
import all Init.Data.Iterators.Basic
import all Init.Data.Iterators.Combinators.Monadic.FilterMap
import all Init.Data.Iterators.Lemmas.Combinators.Monadic.FilterMap

/-! Monadically mapping the output of a reader exposes which of two equal readers is used. -/

public section
open Std Std.Iterators
namespace OmegaChecks.InitBoundaries.IteratorStepLift
open TransformerLaws.MapAfterBind
universe u v

private theorem cancelFamilyCasts (s : {q : Type u → Type u // q = id}) :
    (fun (A : Type u) (a : A) =>
      cast (congrFun s.property A) (cast ((congrFun s.property A).symm) a)) =
      (fun (A : Type u) (a : A) => a) := by
  rcases s with ⟨q, h⟩
  cases h
  rfl

private theorem allCancel : (fun (A : Type u) (a : A) => Shrink.inflate (Shrink.deflate a)) =
    (fun (A : Type u) (a : A) => a) :=
  cancelFamilyCasts (Std.Internal.idOpaque (α := Type u))

/- Use congruence for the entire cancellation function so it can also be rewritten under a binder. -/
open Lean Meta Elab Term in
local elab "cancelShrinks% " h:term : term => do
  let proof ← elabTerm h none
  let type ← inferType proof
  let some sub := type.find? (fun x => x.getAppFn.isConstOf ``Shrink.inflate &&
    x.getAppArgs.back?.any (fun (y : Expr) => y.getAppFn.isConstOf ``Shrink.deflate)) | throwError "no casts"
  let .const _ us := sub.getAppFn | throwError "unexpected cast"
  let eq := Lean.mkConst ``allCancel us
  let some (_, lhs, _) := (← inferType eq).eq? | throwError "no cancellation"
  withLocalDeclD `normalize (← inferType lhs) fun nf => do
    let body := type.replace fun x => do
      guard (x.getAppFn.isConstOf ``Shrink.inflate)
      let #[ty, wrapped] := x.getAppArgs | none
      guard (wrapped.getAppFn.isConstOf ``Shrink.deflate)
      let #[_, value] := wrapped.getAppArgs | none
      return mkApp2 nf ty value
    let ctx ← mkLambdaFVars #[nf] body
    let rewrite ← mkAppM ``congrArg #[ctx, eq]
    mkAppM ``Eq.mp #[rewrite, proof]

@[instance_reducible] private def reading (T : Type u) : Iterator (ULift.{u} Unit) (ReaderM T) T where
  IsPlausibleStep _ _ := True
  step it t := .deflate ⟨.yield it t, trivial⟩

@[instance_reducible] private def attachment (T : Type u) : MonadAttach (Paired T) where
  CanReturn _ _ := True
  attach p := ⟨(fun t => ⟨p.val.1 t, trivial⟩, fun t => ⟨p.val.2 t, trivial⟩),
    congrArg (fun h t => (⟨h t, trivial⟩ : { _x // True })) p.property⟩

private theorem fromStep (rule : (type_of% @Std.IterM.step_mapWithPostcondition.{u,u,u}) ∨
    (type_of% @Std.IterM.step_mapM.{u,u,u}))
    {T : Type u} {f g : T → T} (agree : ∀ x, f x = g x) : f = g := by
  letI := reading T
  letI := monad T
  letI := lawful T
  letI : MonadLiftT (ReaderM T) (Paired T) := ⟨fun r => diagonal r⟩
  let it : IterM (α := ULift.{u} Unit) (ReaderM T) T := ⟨⟨()⟩⟩
  letI := attachment T
  let action (t : T) : Paired T T :=
    ⟨(fun _ => f t, fun _ => g t), congrArg (fun y (_ : T) => y) (agree t)⟩
  -- Mapping the action copies its first reader. Binding the action in the official right side
  -- retains its second reader, which returns the other representative at each input.
  let k (t : T) := PostconditionT.attachLift (action t)
  have eq : type_of% (Std.IterM.step_mapWithPostcondition (it := it) (f := k)) := by
    cases rule with
    | inl law => exact law (it := it) (f := k)
    | inr law => exact law (it := it) (f := action)
  let observed (s : Paired T _) := fun t : T =>
    match ((s.val.2 t : Shrink _).inflate : (it.mapWithPostcondition k).Step).val with
    | .yield _ b => b
    | .skip _ => t
    | .done => t
  have out := congrArg observed eq
  dsimp +zetaDelta [observed, IterM.step, Types.Map.instIterator._aux_3, Types.Map.instIterator,
    Types.FilterMap.instIterator, Iterator.step, it, reading, monadLift, liftM, Id.run, PostconditionT.map,
    diagonal, k, attachment, action, PostconditionT.attachLift, MonadAttach.attach, Functor.map,
    Bind.bind, Pure.pure, bindPair, monad, bind, pure, IterM.mapWithPostcondition,
    IterM.InternalCombinators.map, IterM.InternalCombinators.filterMap, IterM.filterMapWithPostcondition] at out
  have stage₁ := cancelShrinks% out
  dsimp at stage₁
  have stage₂ := cancelShrinks% stage₁
  exact stage₂
private theorem rawMap (law : type_of% @Std.IterM.step_mapWithPostcondition.{max 1 u v,max 1 u v,max 1 u v}) :
    type_of% @funext.{u,v} := funextFromEndomorphisms (fromStep (Or.inl law))

private theorem rawMapM (law : type_of% @Std.IterM.step_mapM.{max 1 u v,max 1 u v,max 1 u v}) :
    type_of% @funext.{u,v} := funextFromEndomorphisms (fromStep (Or.inr law))

/-- These transports use the equality stored in the pinned shrinking representation. -/
private def pack {A : Type u} (a : A) : Shrink A :=
  cast (congrFun (Std.Internal.idOpaque (α := Type u)).property.symm A) a
private def unpack {A : Type u} (a : Shrink A) : A :=
  cast (congrFun (Std.Internal.idOpaque (α := Type u)).property A) a

/- Expand the pinned step bodies and replace their simplifier-generated transport proofs.
The resulting interface and proof are checked for definitional equality in the source kernel. -/
open Lean Meta Elab Term in
local elab "cleanStep% " h:term : term => withExporting (isExporting := false) do
  let exp ← instantiateMVars (← elabTerm h none)
  let expr ← deltaExpand exp (fun n =>
    n == ``rawMapM || n == ``rawMap || (``fromStep).isPrefixOf n ||
    n == ``allCancel || n == ``reading || (``Std.Iterators.Types.Map.instIterator).isPrefixOf n) true
  let clean := expr.replace fun
    | .const n us =>
      if n == ``Shrink.inflate then some (Lean.mkConst ``unpack us)
      else if n == ``Shrink.deflate then some (Lean.mkConst ``pack us)
      else none
    | _ => none
  let env ← getEnv
  unless Kernel.isDefEqGuarded env {} exp clean do throwError "rewritten expression differs from its source"
  return clean

public theorem funextOfMap.{u',v'} : cleanStep% (type_of% (private_decl% @rawMap.{u',v'})) :=
  cleanStep% (private_decl% @rawMap.{u',v'})
public theorem funextOfMapM.{u',v'} : cleanStep% (type_of% (private_decl% @rawMapM.{u',v'})) :=
  cleanStep% (private_decl% @rawMapM.{u',v'})
open Lean in
run_cmd
  let env ← getEnv
  for (raw, witness) in [(``rawMap, ``funextOfMap), (``rawMapM, ``funextOfMapM)] do
    let before ← getConstInfo raw
    let after ← getConstInfo witness
    let levels := before.levelParams.map Level.param
    unless Kernel.isDefEqGuarded env {} before.type (after.type.instantiateLevelParams after.levelParams levels) &&
        (← collectAxioms witness).isEmpty do
      throwError "invalid map-step reduction {witness}"

end OmegaChecks.InitBoundaries.IteratorStepLift
