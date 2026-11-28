module
public import Lean
public import OmegaChecks.InitInventory.Extensionality
import all Init.Data.Iterators.Basic
import all Init.Data.Iterators.Combinators.Monadic.FilterMap
import all Init.Data.Iterators.Lemmas.Combinators.Monadic.FilterMap
import all Init.Data.Iterators.Lemmas.Combinators.FilterMap

/-! Monadic mapping and filtering can expose which of two equal continuations is used. -/

public section
open Std Std.Iterators
namespace OmegaChecks.InitBoundaries.IteratorStepLift
universe u v

/-- For a pure source iterator, the map step only needs the map-before-bind law in
the target monad. The outer iterator step is eliminated before using this law. -/
theorem pureMapOfBindMapLeft (fusion : type_of% @bind_map_left.{u,v}) :
    type_of% @Std.Iter.step_mapWithPostcondition.{u,v} := by
  intro α β γ inst it n f mon law
  letI : MonadLift Id n := ⟨pure⟩
  refine (Std.Iter.step_filterMapWithPostcondition (m := Id) (it := it)
    (f := fun b => PostconditionT.map some (f b))).trans ?_
  generalize it.step = s
  cases s using PlausibleIterStep.casesOn <;> try rfl
  simp only [PostconditionT.operation_map, fusion, bind_pure_comp]
  rfl

/-- Attaching the result gives the same sufficient law for an effectful map. -/
theorem pureMapMOfBindMapLeft (fusion : type_of% @bind_map_left.{u,v}) :
    type_of% @Std.Iter.step_mapM.{u,v} := by
  intro α β γ inst it n f mon att law
  exact pureMapOfBindMapLeft fusion (it := it) (f := fun a => PostconditionT.attachLift (f a))

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

/-- Two provably equal continuations can return an observation immediately, at any result type. -/
private abbrev Branch (T A : Type u) := T → (A → T) → T
private abbrev PairedBranch (T A : Type u) := {p : Branch T A × Branch T A // p.1 = p.2}
private def twin {T A : Type u} (r : Branch T A) : PairedBranch T A := ⟨(r, r), rfl⟩

private theorem twinExists {T A : Type u} (p : PairedBranch T A) : ∃ r, p = twin r := by
  rcases p with ⟨⟨r, s⟩, h⟩
  cases h
  exact ⟨r, rfl⟩

@[instance_reducible] private def branchMonad (T : Type u) : Monad (PairedBranch T) where
  pure a := twin fun _ k => k a
  bind p g := ⟨(fun t k => p.val.1 t (fun a => (g a).val.2 t k),
    fun t k => p.val.2 t (fun a => (g a).val.2 t k)),
    congrArg (fun r t k => r t (fun a => (g a).val.2 t k)) p.property⟩
  map f p := twin fun t k => p.val.1 t (fun a => k (f a))

private theorem branchLawful (T : Type u) : letI := branchMonad T; LawfulMonad (PairedBranch T) := by
  letI := branchMonad T
  exact {
    map_const := rfl
    id_map := by intro _ x; obtain ⟨_, rfl⟩ := twinExists x; rfl
    comp_map := by intros; rfl
    pure_seq := by intros; rfl
    map_pure := by intros; rfl
    seq_pure := by intro _ _ x _; obtain ⟨_, rfl⟩ := twinExists x; rfl
    seqLeft_eq := by
      intro _ _ x y; obtain ⟨_, rfl⟩ := twinExists x; obtain ⟨_, rfl⟩ := twinExists y; rfl
    seqRight_eq := by
      intro _ _ x y; obtain ⟨_, rfl⟩ := twinExists x; obtain ⟨_, rfl⟩ := twinExists y; rfl
    seq_assoc := by
      intro _ _ _ x g h
      obtain ⟨_, rfl⟩ := twinExists x
      obtain ⟨_, rfl⟩ := twinExists g
      obtain ⟨_, rfl⟩ := twinExists h
      rfl
    bind_pure_comp := by intro _ _ _ x; obtain ⟨_, rfl⟩ := twinExists x; rfl
    bind_map := by intro _ _ _ x; obtain ⟨_, rfl⟩ := twinExists x; rfl
    pure_bind := by
      intro A B a k
      change twin (k a).val.2 = k a
      obtain ⟨r, hr⟩ := twinExists (k a)
      rw [hr]
      rfl
    bind_assoc := by intros; rfl
  }

@[instance_reducible] private def branchAttachment (T : Type u) : MonadAttach (PairedBranch T) where
  CanReturn _ _ := True
  attach {A} p := ⟨(fun t k => p.val.1 t (fun a => k ⟨a, trivial⟩),
    fun t k => p.val.2 t (fun a => k ⟨a, trivial⟩)),
    congrArg (fun (r : Branch T A) t (k : {_a : A // True} → T) => r t (fun a => k ⟨a, trivial⟩)) p.property⟩

/-- An aborted mapping can report an arbitrary value even when its declared return type is Boolean. -/
private theorem fromStep (rule : (type_of% @Std.IterM.step_mapWithPostcondition.{u,u,u}) ∨
    (type_of% @Std.IterM.step_mapM.{u,u,u}) ∨ (type_of% @Std.IterM.step_filterWithPostcondition.{u,u,u}) ∨
    (type_of% @Std.IterM.step_filterM.{u,u,u}))
    {T : Type u} {f g : T → T} (agree : ∀ t, f t = g t) : f = g := by
  letI := reading T
  letI := branchMonad T
  letI := branchLawful T
  letI := branchAttachment T
  letI : MonadLiftT (ReaderM T) (PairedBranch T) := ⟨fun r => twin (fun t k => k (r t))⟩
  let it : IterM (α := ULift.{u} Unit) (ReaderM T) T := ⟨⟨()⟩⟩
  let action (A : Type u) (t : T) : PairedBranch T A :=
    ⟨(fun _ _ => f t, fun _ _ => g t), congrArg (fun y (_ : T) (_ : A → T) => y) (agree t)⟩
  rcases rule with law | law | law | law
  all_goals
    first
    | have eq := law (it := it) (f := fun t => PostconditionT.attachLift (action T t))
    | have eq := law (it := it) (f := action T)
    | have eq := law (it := it) (f := fun t => PostconditionT.attachLift (action (ULift.{u} Bool) t))
    | have eq := law (it := it) (f := action (ULift.{u} Bool))
    have out := congrArg (fun s : PairedBranch T _ => fun t => s.val.2 t (fun _ => t)) eq
    dsimp +zetaDelta [IterM.step, IterM.mapM, IterM.mapWithPostcondition, IterM.filterM,
      IterM.filterWithPostcondition, Types.Map.instIterator._aux_3, Types.Map.instIterator,
      Types.FilterMap.instIterator, Iterator.step, it, reading, monadLift, liftM, PostconditionT.map,
      twin, branchAttachment, action, PostconditionT.attachLift, MonadAttach.attach, Functor.map,
      Bind.bind, Pure.pure, branchMonad, bind, pure, IterM.InternalCombinators.map,
      IterM.InternalCombinators.filterMap, IterM.filterMapWithPostcondition] at out
    exact cancelShrinks% out

private theorem rawMap (law : type_of% @Std.IterM.step_mapWithPostcondition.{max 1 u v,max 1 u v,max 1 u v}) :
    type_of% @funext.{u,v} := funextFromEndomorphisms (fromStep (Or.inl law))

private theorem rawMapM (law : type_of% @Std.IterM.step_mapM.{max 1 u v,max 1 u v,max 1 u v}) :
    type_of% @funext.{u,v} := funextFromEndomorphisms (fromStep (Or.inr (Or.inl law)))

private theorem rawFilter (law : type_of% @Std.IterM.step_filterWithPostcondition.{max 1 u v,max 1 u v,max 1 u v}) :
    type_of% @funext.{u,v} := funextFromEndomorphisms (fromStep (Or.inr (Or.inr (Or.inl law))))

private theorem rawFilterM (law : type_of% @Std.IterM.step_filterM.{max 1 u v,max 1 u v,max 1 u v}) :
    type_of% @funext.{u,v} := funextFromEndomorphisms (fromStep (Or.inr (Or.inr (Or.inr law))))

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
    [``rawMapM, ``rawMap, ``rawFilter, ``rawFilterM].contains n ||
    (``fromStep).isPrefixOf n ||
    (``Std.IterM.step_filterWithPostcondition).isPrefixOf n ||
    (``Std.Iterators.Types.FilterMap.instIterator).isPrefixOf n ||
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

public theorem funextOfFilter.{u',v'} : cleanStep% (type_of% (private_decl% @rawFilter.{u',v'})) :=
  cleanStep% (private_decl% @rawFilter.{u',v'})

public theorem funextOfFilterM.{u',v'} : cleanStep% (type_of% (private_decl% @rawFilterM.{u',v'})) :=
  cleanStep% (private_decl% @rawFilterM.{u',v'})


open Lean in
run_cmd
  let env ← getEnv
  for (raw, witness) in [(``rawMap, ``funextOfMap), (``rawMapM, ``funextOfMapM),
      (``rawFilter, ``funextOfFilter), (``rawFilterM, ``funextOfFilterM)] do
    let before ← getConstInfo raw
    let after ← getConstInfo witness
    let levels := before.levelParams.map Level.param
    unless Kernel.isDefEqGuarded env {} before.type (after.type.instantiateLevelParams after.levelParams levels) &&
        (← collectAxioms witness).isEmpty do
      throwError "invalid iterator step reduction {witness}"

end OmegaChecks.InitBoundaries.IteratorStepLift
