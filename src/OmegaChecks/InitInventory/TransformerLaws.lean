module
public import Lean
import all Init.Data.List.Scan.Basic
import all Init.Data.Option.Instances
public import Init.Control.Lawful.MonadLift.Instances
public import Init.Data.Option.Monadic
import Lean.Replay
import all Lean.Util.CollectAxioms
public import OmegaChecks.InitInventory.Extensionality

public section

open Lean
namespace OmegaChecks.InitBoundaries
universe u v w z

namespace SubsingletonState

/-- Pointwise equality for maps out of a subsingleton state. -/
def Extensionality : Prop := ∀ {σ α : Type u} [Subsingleton σ] {f g : σ → α},
  (∀ s, f s = g s) → f = g

private abbrev Graph {σ α : Type u} (f : σ → α) := (s : σ) × {y : α // y = f s}

private theorem graphSubsingleton {σ α : Type u} [Subsingleton σ] (f : σ → α) : Subsingleton (Graph f) :=
  ⟨fun ⟨s, y, hy⟩ ⟨t, z, hz⟩ => by
    cases Subsingleton.elim s t
    cases hy
    cases hz
    rfl⟩

theorem ofState (state : type_of% @instSubsingletonStateM.{u}) : Extensionality.{u} := by
  intro σ α _ f g h
  letI := graphSubsingleton f
  let left : StateM σ (Graph f) := fun s => (⟨s, f s, rfl⟩, s)
  let right : StateM σ (Graph f) := fun s => (⟨s, g s, (h s).symm⟩, s)
  exact congrArg (fun t : StateM σ (Graph f) => fun s => (t s).1.2.val)
    ((state (σ := σ) (α := Graph f)).elim left right)

theorem iffState : (type_of% @instSubsingletonStateM.{u}) ↔ Extensionality.{u} := by
  refine ⟨ofState, ?_⟩
  intro ext σ α _ _
  exact ⟨fun f g => ext fun s => Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _)⟩

end SubsingletonState

namespace TransformerLaws

/-- A pointwise identity can be applied in the error branch of both mapping and binding. -/
@[instance_reducible] private def exceptionMonad {ε : Type u} (reset : ε → ε) : Monad (fun α : Type u => Except ε α) where
  pure := Except.ok
  bind x k := match x with | .ok a => k a | .error e => .error (reset e)
  map f x := match x with | .ok a => .ok (f a) | .error e => .error (reset e)

private theorem lawful {ε : Type u} (reset : ε → ε) (fixed : ∀ e, reset e = e) :
    letI := exceptionMonad reset; LawfulMonad (fun α : Type u => Except ε α) := by
  letI := exceptionMonad reset
  exact {
    map_const := rfl
    id_map := by intro _ x; cases x <;> first | rfl | exact congrArg Except.error (fixed _) | exact congrArg Except.error (fixed _).symm
    comp_map := by intro _ _ _ g h x; cases x <;> first | rfl | exact congrArg Except.error (fixed _) | exact congrArg Except.error (fixed _).symm
    pure_seq := by intro _ _ f x; cases x <;> first | rfl | exact congrArg Except.error (fixed _) | exact congrArg Except.error (fixed _).symm
    map_pure := by intros; rfl
    seq_pure := by intro _ _ g x; cases g <;> first | rfl | exact congrArg Except.error (fixed _) | exact congrArg Except.error (fixed _).symm
    seqLeft_eq := by intro _ _ x y; cases x <;> cases y <;> first | rfl | exact congrArg Except.error (fixed _) | exact congrArg Except.error (fixed _).symm
    seqRight_eq := by intro _ _ x y; cases x <;> cases y <;> first | rfl | exact congrArg Except.error (fixed _) | exact congrArg Except.error (fixed _).symm
    seq_assoc := by intro _ _ _ x g h; cases x <;> cases g <;> cases h <;> first | rfl | exact congrArg Except.error (fixed _) | exact congrArg Except.error (fixed _).symm
    bind_pure_comp := by intro _ _ f x; cases x <;> first | rfl | exact congrArg Except.error (fixed _) | exact congrArg Except.error (fixed _).symm
    bind_map := by intro _ _ f x; cases f <;> cases x <;> first | rfl | exact congrArg Except.error (fixed _) | exact congrArg Except.error (fixed _).symm
    pure_bind := by intros; rfl
    bind_assoc := by intro _ _ _ x f g; cases x <;> first | rfl | exact congrArg Except.error (fixed _)
  }

private def Graph {T : Type u} (f : T → T) := (x : T) × {y : T // f x = y}
private def resetGraph {T : Type u} (f : T → T) (p : Graph f) : Graph f := ⟨p.1, f p.1, rfl⟩
private theorem resetGraph_eq {T : Type u} (f : T → T) (p : Graph f) : resetGraph f p = p := by
  rcases p with ⟨x,y,hy⟩
  cases hy
  rfl

private abbrev ErrorM {T : Type u} (f : T → T) (α : Type u) := Except (Graph f) α

private theorem readerIdentity {T : Type u} {f g : T → T} (agree : ∀ x, f x = g x)
    (identityLaw : letI := exceptionMonad (resetGraph f); LawfulFunctor (ReaderT T (ErrorM f))) :
    f = g := by
  letI := exceptionMonad (resetGraph f)
  letI : LawfulFunctor (ReaderT T (ErrorM f)) := identityLaw
  let input : ReaderT T (ErrorM f) PUnit := fun t => .error ⟨t, g t, agree t⟩
  let output (a : ReaderT T (ErrorM f) PUnit) (t : T) :=
    match a t with | .error s => s.2.val | .ok _ => t
  exact congrArg output (id_map input)

private theorem viaFunctor (law : type_of% @ReaderT.instLawfulFunctor.{u,u})
    {T : Type u} {f g : T → T} (agree : ∀ x, f x = g x) : f = g := by
  letI := exceptionMonad (resetGraph f)
  letI : LawfulMonad (ErrorM f) := lawful (resetGraph f) (resetGraph_eq f)
  exact readerIdentity agree ((law (ρ := T) (m := ErrorM f)))

private theorem viaApplicative (law : type_of% @ReaderT.instLawfulApplicative.{u,u})
    {T : Type u} {f g : T → T} (agree : ∀ x, f x = g x) : f = g := by
  letI := exceptionMonad (resetGraph f)
  letI : LawfulMonad (ErrorM f) := lawful (resetGraph f) (resetGraph_eq f)
  exact readerIdentity agree ((law (ρ := T) (m := ErrorM f)).toLawfulFunctor)

private theorem viaMonad (law : type_of% @ReaderT.instLawfulMonad.{u,u})
    {T : Type u} {f g : T → T} (agree : ∀ x, f x = g x) : f = g := by
  letI := exceptionMonad (resetGraph f)
  letI : LawfulMonad (ErrorM f) := lawful (resetGraph f) (resetGraph_eq f)
  exact readerIdentity agree ((law (ρ := T) (m := ErrorM f)).toLawfulApplicative.toLawfulFunctor)

private theorem viaState (law : type_of% @StateT.instLawfulMonad.{u,u})
    {T : Type u} {f g : T → T} (agree : ∀ x, f x = g x) : f = g := by
  letI := exceptionMonad (resetGraph f)
  letI : LawfulMonad (ErrorM f) := lawful (resetGraph f) (resetGraph_eq f)
  letI : LawfulFunctor (StateT T (ErrorM f)) := (law (σ := T) (m := ErrorM f)).toLawfulApplicative.toLawfulFunctor
  let input : StateT T (ErrorM f) PUnit := fun t => .error ⟨t, g t, agree t⟩
  let output (a : StateT T (ErrorM f) PUnit) (t : T) :=
    match a t with | .error s => s.2.val | .ok _ => t
  exact congrArg output (id_map input)

public theorem fromReaderTFunctor
    (law : type_of% @ReaderT.instLawfulFunctor.{max 1 u v, max 1 u v}) : type_of% @funext.{u,v} :=
  funextFromEndomorphisms (viaFunctor law)

public theorem fromReaderTApplicative
    (law : type_of% @ReaderT.instLawfulApplicative.{max 1 u v, max 1 u v}) : type_of% @funext.{u,v} :=
  funextFromEndomorphisms (viaApplicative law)

public theorem fromReaderTMonad
    (law : type_of% @ReaderT.instLawfulMonad.{max 1 u v, max 1 u v}) : type_of% @funext.{u,v} :=
  funextFromEndomorphisms (viaMonad law)

public theorem fromStateTMonad
    (law : type_of% @StateT.instLawfulMonad.{max 1 u v, max 1 u v}) : type_of% @funext.{u,v} :=
  funextFromEndomorphisms (viaState law)

@[instance_reducible] private def attached {T : Type u} (f : T → T) : MonadAttach (ErrorM f) where
  CanReturn {_} x a := match x with | .ok b => b = a | .error _ => False
  attach x := match x with | .ok b => .ok ⟨b, rfl⟩ | .error e => .error e

private theorem attachedLaw {T : Type u} (f : T → T) :
    letI := exceptionMonad (resetGraph f); letI := attached f; LawfulMonadAttach (ErrorM f) := by
  letI := exceptionMonad (resetGraph f)
  letI := attached f
  exact {
    map_attach := by
      intro _ x
      cases x with
      | error e => exact congrArg Except.error (resetGraph_eq f e)
      | ok _ => rfl
    canReturn_map_imp := by
      intro α P x a h
      cases x with
      | error e => exact False.elim h
      | ok b => exact h ▸ b.property
  }
private theorem ReaderTAttach {T : Type u} {f g : T → T} (agree : ∀ x, f x = g x)
    (law : letI := exceptionMonad (resetGraph f); letI := attached f;
      WeaklyLawfulMonadAttach (ReaderT T (ErrorM f))) : f = g := by
  letI := exceptionMonad (resetGraph f)
  letI := attached f
  letI : WeaklyLawfulMonadAttach (ReaderT T (ErrorM f)) := law
  let input : ReaderT T (ErrorM f) PUnit := fun t => .error ⟨t, g t, agree t⟩
  let output (a : ReaderT T (ErrorM f) PUnit) (t : T) :=
    match a t with | .error e => e.2.val | .ok _ => t
  exact congrArg output (WeaklyLawfulMonadAttach.map_attach (x := input))

public theorem fromReaderTWeakAttach (law : type_of% @instWeaklyLawfulMonadAttachReaderTOfLawfulMonad.{max 1 u v, max 1 u v}) :
    type_of% @funext.{u,v} := by
  apply funextFromEndomorphisms
  intro T f g agree
  letI := exceptionMonad (resetGraph f)
  letI : LawfulMonad (ErrorM f) := lawful (resetGraph f) (resetGraph_eq f)
  letI := attached f
  letI : LawfulMonadAttach (ErrorM f) := attachedLaw f
  exact ReaderTAttach agree ((law (ρ := T) (m := ErrorM f)))

public theorem fromReaderTAttach (law : type_of% @instLawfulMonadAttachReaderTOfLawfulMonad.{max 1 u v, max 1 u v}) :
    type_of% @funext.{u,v} := by
  apply funextFromEndomorphisms
  intro T f g agree
  letI := exceptionMonad (resetGraph f)
  letI : LawfulMonad (ErrorM f) := lawful (resetGraph f) (resetGraph_eq f)
  letI := attached f
  letI : LawfulMonadAttach (ErrorM f) := attachedLaw f
  exact ReaderTAttach agree ((law (ρ := T) (m := ErrorM f)).toWeaklyLawfulMonadAttach)

private theorem StateTAttach {T : Type u} {f g : T → T} (agree : ∀ x, f x = g x)
    (law : letI := exceptionMonad (resetGraph f); letI := attached f;
      WeaklyLawfulMonadAttach (StateT T (ErrorM f))) : f = g := by
  letI := exceptionMonad (resetGraph f)
  letI := attached f
  letI : WeaklyLawfulMonadAttach (StateT T (ErrorM f)) := law
  let input : StateT T (ErrorM f) PUnit := fun t => .error ⟨t, g t, agree t⟩
  let output (a : StateT T (ErrorM f) PUnit) (t : T) :=
    match a t with | .error e => e.2.val | .ok _ => t
  exact congrArg output (WeaklyLawfulMonadAttach.map_attach (x := input))

public theorem fromStateTWeakAttach (law : type_of% @instWeaklyLawfulMonadAttachStateTOfLawfulMonad.{max 1 u v, max 1 u v}) :
    type_of% @funext.{u,v} := by
  apply funextFromEndomorphisms
  intro T f g agree
  letI := exceptionMonad (resetGraph f)
  letI : LawfulMonad (ErrorM f) := lawful (resetGraph f) (resetGraph_eq f)
  letI := attached f
  letI : LawfulMonadAttach (ErrorM f) := attachedLaw f
  exact StateTAttach agree ((law (σ := T) (m := ErrorM f)))

public theorem fromStateTAttach (law : type_of% @instLawfulMonadAttachStateTOfLawfulMonad.{max 1 u v, max 1 u v}) :
    type_of% @funext.{u,v} := by
  apply funextFromEndomorphisms
  intro T f g agree
  letI := exceptionMonad (resetGraph f)
  letI : LawfulMonad (ErrorM f) := lawful (resetGraph f) (resetGraph_eq f)
  letI := attached f
  letI : LawfulMonadAttach (ErrorM f) := attachedLaw f
  exact StateTAttach agree ((law (σ := T) (m := ErrorM f)).toWeaklyLawfulMonadAttach)

open Lean in
run_cmd
  for n in [``fromReaderTWeakAttach, ``fromReaderTAttach, ``fromStateTWeakAttach, ``fromStateTAttach,
      ``fromReaderTFunctor, ``fromReaderTApplicative, ``fromReaderTMonad, ``fromStateTMonad] do
    unless (← collectAxioms n).isEmpty do throwError "transformer law witness {n} uses axioms"

private theorem constructorEndomorphisms (make : type_of% @LawfulMonad.mk'.{u,u})
    {T : Type u} {f g : T → T} (agree : ∀ x, f x = g x) : f = g := by
  let base : Monad (Except (Graph f)) := inferInstance
  let custom : Monad (ErrorM f) := { base with mapConst := fun a x =>
    match x with | .ok _ => .ok a | .error e => .error (resetGraph f e) }
  letI : Monad (ErrorM f) := custom
  let law := make (ErrorM f) (fun x => by cases x <;> rfl) (fun _ _ => rfl)
    (fun x _ _ => by cases x <;> rfl) (fun a x => by
      cases x with
      | ok b => rfl
      | error e => exact congrArg Except.error (resetGraph_eq f e))
    (fun x y => by cases x <;> cases y <;> rfl)
    (fun x y => by cases x <;> cases y <;> rfl)
    (fun k x => by cases x <;> rfl)
    (fun k x => by cases k <;> cases x <;> rfl)
  let input (t : T) : ErrorM f PUnit := .error ⟨t, g t, agree t⟩
  let see (k : PUnit → ErrorM f PUnit → ErrorM f PUnit) (t : T) :=
    match k .unit (input t) with | .error e => e.2.val | .ok _ => t
  exact congrArg see (@LawfulFunctor.map_const (ErrorM f) _ law.toLawfulApplicative.toLawfulFunctor PUnit PUnit)

public theorem fromMonadConstructor (make : type_of% @LawfulMonad.mk'.{max 1 u v, max 1 u v}) :
    type_of% @funext.{u,v} :=
  funextFromEndomorphisms (constructorEndomorphisms @make)

open Lean in
run_cmd
  unless (← collectAxioms ``fromMonadConstructor).isEmpty do throwError "monad constructor witness uses axioms"

private def normalize {ε α : Type u} (reset : ε → ε) : Except ε α → Except ε α
  | .error e => .error (reset e)
  | .ok a => .ok a
private theorem normal {ε α : Type u} (reset : ε → ε) (fixed : ∀ e, reset e = e) (x : Except ε α) :
    normalize reset x = x := by
  cases x with
  | ok _ => rfl
  | error e => exact congrArg Except.error (fixed e)
@[instance_reducible] private def normalized {ε : Type u} (reset : ε → ε) : Monad (fun α : Type u => Except ε α) where
  pure := Except.ok
  bind x k := match x with | .ok a => normalize reset (k a) | .error e => .error e

private theorem normalizedLawful {ε : Type u} (reset : ε → ε) (fixed : ∀ e, reset e = e) :
    letI := normalized reset; LawfulMonad (fun α : Type u => Except ε α) := by
  letI := normalized reset
  exact {
    map_const := rfl
    id_map := by intro _ x; cases x <;> rfl
    comp_map := by intro _ _ _ g h x; cases x <;> rfl
    pure_seq := by intro _ _ f x; cases x <;> first | rfl | exact congrArg Except.error (fixed _)
    map_pure := by intros; rfl
    seq_pure := by intro _ _ g x; cases g <;> rfl
    seqLeft_eq := by intro _ _ x y; cases x <;> cases y <;> first | rfl | exact congrArg Except.error (fixed _).symm
    seqRight_eq := by intro _ _ x y; cases x <;> cases y <;> first | rfl | exact congrArg Except.error (fixed _).symm
    seq_assoc := by intro _ _ _ x g h; cases x <;> cases g <;> cases h <;> first | rfl | exact congrArg Except.error (fixed _) | exact congrArg Except.error (fixed _).symm
    bind_pure_comp := by intro _ _ f x; cases x <;> rfl
    bind_map := by intro _ _ f x; cases f <;> cases x <;> first | rfl | exact congrArg Except.error (fixed _)
    pure_bind := by intro _ _ a k; exact normal reset fixed (k a)
    bind_assoc := by
      intro α β γ x f g
      cases x with
      | error e => rfl
      | ok a =>
        change ((normalize reset (f a)) >>= g) = normalize reset (f a >>= g)
        rw [normal reset fixed, normal reset fixed]
  }

private theorem viaStateCpsLift (law : type_of% @StateCpsT.instLawfulMonadLiftOfLawfulMonad.{u,u})
    {T : Type u} {f g : T → T} (agree : ∀ x, f x = g x) : f = g := by
  letI := normalized (resetGraph f)
  letI : LawfulMonad (ErrorM f) := normalizedLawful (resetGraph f) (resetGraph_eq f)
  letI : LawfulMonadLift (ErrorM f) (StateCpsT PUnit (ErrorM f)) := law
  let use (t : T) : ErrorM f PUnit := .error ⟨t, g t, agree t⟩
  let observe (a : StateCpsT PUnit (ErrorM f) PUnit) (t : T) :=
    match a PUnit .unit (fun _ _ => use t) with
    | .error err => err.2.val
    | .ok _ => t
  exact congrArg observe (LawfulMonadLift.monadLift_pure (m := ErrorM f) (n := StateCpsT PUnit (ErrorM f)) PUnit.unit)

private theorem viaExceptCpsLift (law : type_of% @ExceptCpsT.instLawfulMonadLiftOfLawfulMonad.{u,u})
    {T : Type u} {f g : T → T} (agree : ∀ x, f x = g x) : f = g := by
  letI := normalized (resetGraph f)
  letI : LawfulMonad (ErrorM f) := normalizedLawful (resetGraph f) (resetGraph_eq f)
  letI : LawfulMonadLift (ErrorM f) (ExceptCpsT PUnit (ErrorM f)) := law
  let use (t : T) : ErrorM f PUnit := .error ⟨t, g t, agree t⟩
  let observe (a : ExceptCpsT PUnit (ErrorM f) PUnit) (t : T) :=
    match a PUnit (fun _ => use t) (fun _ => use t) with
    | .error err => err.2.val
    | .ok _ => t
  exact congrArg observe (LawfulMonadLift.monadLift_pure (m := ErrorM f) (n := ExceptCpsT PUnit (ErrorM f)) PUnit.unit)

public theorem fromStateCpsLift
    (law : type_of% @StateCpsT.instLawfulMonadLiftOfLawfulMonad.{max 1 u v, max 1 u v}) : type_of% @funext.{u,v} :=
  funextFromEndomorphisms (viaStateCpsLift law)

public theorem fromExceptCpsLift
    (law : type_of% @ExceptCpsT.instLawfulMonadLiftOfLawfulMonad.{max 1 u v, max 1 u v}) : type_of% @funext.{u,v} :=
  funextFromEndomorphisms (viaExceptCpsLift law)

open Lean in
run_cmd
  for n in [``fromStateCpsLift, ``fromExceptCpsLift] do
    unless (← collectAxioms n).isEmpty do throwError "continuation lift witness {n} uses axioms"

@[instance_reducible] private def reader (T : Type u) : Monad (fun α : Type u => T → α) where
  pure a _ := a
  bind x k t := k (x t) t

private theorem readerLaws (T : Type u) :
    letI := reader T; LawfulMonad (fun α : Type u => T → α) := by
  letI := reader T
  exact {
    map_const := rfl
    id_map := by intros; rfl
    comp_map := by intros; rfl
    pure_seq := by intros; rfl
    map_pure := by intros; rfl
    seq_pure := by intros; rfl
    seqLeft_eq := by intros; rfl
    seqRight_eq := by intros; rfl
    seq_assoc := by intros; rfl
    bind_pure_comp := by intros; rfl
    bind_map := by intros; rfl
    pure_bind := by intros; rfl
    bind_assoc := by intros; rfl
  }

namespace OptionIteration

/-- Moving a map outside the two identical continuation branches, uniformly as a function. -/
def Fusion : Prop := ∀ {β : Type u} {δ : Type v} (k : β → δ),
  (fun r : ForInStep β => match r with | .done b | .yield b => k b) =
    (fun r => k r.value)

abbrev SomeRule := type_of% @Option.forIn_some.{u,v,w}

private theorem someStep (rule : SomeRule.{u,v,w}) {m : Type u → Type v} [Monad m] [LawfulMonad m]
    {α : Type w} {β : Type u} (a : α) (b : β) (f : (x : α) → x ∈ some a → β → m (ForInStep β)) :
    forIn' (some a) b f = bind (f a rfl b) (fun r => pure r.value) :=
  @rule m α β _ _ a b (fun _ y => f a rfl y)

theorem someOfFusion (fusion : Fusion.{u,v}) : SomeRule.{u,v,w} := by
  intro m α β _ _ a b f
  exact congrArg (Bind.bind (f a b)) (fusion pure)

theorem dependentSome (rule : SomeRule.{u,v,w}) : type_of% @Option.forIn'_some.{u,v,w} := by
  intro m α β _ _ a b f
  exact someStep rule a b f

theorem ofDependentSome (rule : type_of% @Option.forIn'_some.{u,v,w}) : SomeRule.{u,v,w} := by
  intro m α β _ _ a b f
  exact rule a b fun x _ => f x

theorem dependentElim (rule : SomeRule.{u,v,w}) : type_of% @Option.forIn'_eq_pelim.{u,v,w} := by
  intro m α β _ _ o f b
  cases o with
  | none => rfl
  | some a => exact (someStep rule a b f).trans (bind_pure_comp _ _)

theorem elimRule (rule : SomeRule.{u,v,w}) : type_of% @Option.forIn_eq_elim.{u,v,w} := by
  intro m α β _ _ o f b
  cases o with
  | none => rfl
  | some a => exact (someStep rule a b (fun x _ => f x)).trans (bind_pure_comp _ _)

theorem dependentYield (rule : SomeRule.{u,v,w}) : type_of% @Option.forIn'_yield_eq_pelim.{u,v,w} := by
  intro m α β γ _ _ o f g b
  cases o with
  | none => rfl
  | some a =>
    exact (dependentElim rule _ _ b).trans (LawfulFunctor.comp_map _ _ _).symm

theorem yieldRule (rule : SomeRule.{u,v,w}) : type_of% @Option.forIn_yield_eq_elim.{u,v,w} := by
  intro m α β γ _ _ o f g b
  cases o with
  | none => rfl
  | some a => exact (elimRule rule _ _ b).trans (LawfulFunctor.comp_map _ _ _).symm

theorem dependentJoin (rule : SomeRule.{u,v,w}) {m : Type u → Type v} {β : Type u} {α : Type w}
    [Monad m] [LawfulMonad m] (b : β) (o : Option (Option α))
    (f : (a : α) → a ∈ o.join → β → m (ForInStep β)) :
    forIn' o.join b f = forIn' o b (fun o' ho' b => ForInStep.yield <$>
      forIn' o' b (fun a ha b' => f a (by cases o <;> cases ho' <;> exact ha) b')) := by
  cases o with
  | none => rfl
  | some inner =>
    rw [dependentSome rule]
    exact (id_map _).symm.trans ((LawfulFunctor.comp_map ForInStep.yield ForInStep.value _).trans
      (bind_pure_comp _ _).symm)

example (rule : SomeRule.{u,v,w}) : type_of% @Option.forIn'_join.{u,v,w} := @dependentJoin rule

theorem joinRule (rule : SomeRule.{u,v,w}) : type_of% @Option.forIn_join.{u,v,w} := by
  intro m α β init _ _ o f
  exact dependentJoin rule init o fun a _ => f a

theorem ofElim (rule : type_of% @Option.forIn_eq_elim.{u,v,w}) : SomeRule.{u,v,w} := by
  intro m α β _ _ a b f
  exact (rule (some a) f b).trans (bind_pure_comp _ _).symm

theorem ofDependentElim (rule : type_of% @Option.forIn'_eq_pelim.{u,v,w}) : SomeRule.{u,v,w} := by
  intro m α β _ _ a b f
  exact (rule (some a) (fun x _ => f x) b).trans (bind_pure_comp _ _).symm

/-- Applying the pinned option loop to a reader retains equality of the complete functions. -/
def ReaderStep := ∀ {σ β : Type u} (_ : β) (steps : σ → ForInStep β),
  (fun t => (match steps t with | .done v | .yield v => fun _ : σ => v) t) =
    (fun t => (steps t).value)

theorem readerStep (rule : SomeRule.{u,u,u}) : ReaderStep.{u} := by
  intro σ β b steps
  letI := reader σ
  letI := readerLaws σ
  exact @rule (fun γ => σ → γ) (PUnit.{u+1}) β _ _ .unit b (fun _ _ => steps)


def directConsequences : List (Name × Name × Name) := [
  (``Option.forIn_some, ``ReaderStep, ``readerStep),
  (``Option.forIn'_some, ``SomeRule, ``ofDependentSome),
  (``Option.forIn_eq_elim, ``SomeRule, ``ofElim),
  (``Option.forIn'_eq_pelim, ``SomeRule, ``ofDependentElim)]

def constructions : List Name :=
  [``someOfFusion, ``dependentSome, ``dependentElim, ``elimRule, ``dependentYield, ``yieldRule, ``dependentJoin, ``joinRule]

end OptionIteration

private def input? {T : Type u} {f : T → T} : Option (Graph f) → Option T
  | none => none
  | some p => some p.1

private def graph? {T : Type u} (f : T → T) : Option T → Option (Graph f)
  | none => none
  | some t => some ⟨t, f t, rfl⟩

private theorem graphInverse {T : Type u} {f : T → T} (p : Option (Graph f)) :
    graph? f (input? p) = p := by
  cases p with
  | none => rfl
  | some p => exact congrArg some (resetGraph_eq f p)

private theorem injectivityEndomorphisms
    (cancel : ∀ {T : Type u} {f : T → T} {x y : T → Option (Graph f)},
       (fun t => input? (x t)) = (fun t => input? (y t)) → x = y)
    {T : Type u} {f g : T → T} (agree : ∀ x, f x = g x) : f = g := by
  let x (t : T) : Option (Graph f) := some ⟨t, f t, rfl⟩
  let y (t : T) : Option (Graph f) := some ⟨t, g t, agree t⟩
  let output (r : T → Option (Graph f)) (t : T) := (r t).elim t (fun p => p.2.val)
  exact congrArg output (cancel (x := x) (y := y) rfl)

public theorem fromMapInjectiveLeftInverse (cancel : type_of% @map_inj_of_left_inverse.{max 1 u v, max 1 u v}) :
    type_of% @funext.{u,v} := by
  apply funextFromEndomorphisms
  apply injectivityEndomorphisms
  intro T f x y h
  letI := reader T
  letI : LawfulMonad (fun α : Type (max 1 u v) => T → α) := readerLaws T
  exact (cancel (m := fun α => T → α) (f := input?) ⟨graph? f, graphInverse⟩).mp h

public theorem fromMapInjectiveNonempty (cancel : type_of% @map_inj_right_of_nonempty.{max 1 u v, max 1 u v}) :
    type_of% @funext.{u,v} := by
  apply funextFromEndomorphisms
  apply injectivityEndomorphisms
  intro T f x y h
  letI := reader T
  letI : LawfulMonad (fun α : Type (max 1 u v) => T → α) := readerLaws T
  exact (cancel (m := fun α => T → α) (f := input? (f := f))
    (fun {x y} eq => (graphInverse x).symm.trans ((congrArg (graph? f) eq).trans (graphInverse y)))).mp h

public theorem fromMapInjectiveMonad (cancel : type_of% @map_inj_right.{max 1 u v, max 1 u v}) :
    type_of% @funext.{u,v} := by
  apply funextFromEndomorphisms
  apply injectivityEndomorphisms
  intro T f x y h
  letI := reader T
  letI : LawfulMonad (fun α : Type (max 1 u v) => T → α) := readerLaws T
  exact (cancel (m := fun α => T → α) (f := input? (f := f))
    (fun {x y} eq => (graphInverse x).symm.trans ((congrArg (graph? f) eq).trans (graphInverse y)))).mp h

open Lean in
run_cmd
  for n in [``fromMapInjectiveLeftInverse, ``fromMapInjectiveNonempty, ``fromMapInjectiveMonad] do
    unless (← collectAxioms n).isEmpty do throwError "map injectivity witness {n} uses axioms"

/-- Shifting two witnesses makes consecutive applications of the pointwise identity observable. -/
private def Window {T : Type u} (f : T → T) :=
  (t : T) × {x : T // f t = x} × {x : T // f t = x}

private def shift {T : Type u} {f : T → T} (w : Window f) : Window f :=
  ⟨w.1, w.2.2, ⟨f w.1, rfl⟩⟩

private theorem shift_eq {T : Type u} {f : T → T} (w : Window f) : shift w = w := by
  rcases w with ⟨t, ⟨x, hx⟩, y, hy⟩
  cases hx
  cases hy
  rfl

private abbrev WindowM {T : Type u} (f : T → T) (α : Type u) := Except (Window f) α

private def failure {T : Type u} {f g : T → T} (agree : ∀ t, f t = g t) :
    StateT T (WindowM f) PUnit :=
  fun t => .error ⟨t, ⟨g t, agree t⟩, ⟨g t, agree t⟩⟩

private def readWindow {T : Type u} {f : T → T} (x : StateT T (WindowM f) PUnit) (t : T) : T :=
  match x t with | .error w => w.2.1.val | .ok _ => t

private theorem viaStateSeqLeft (law : type_of% @StateT.seqLeft_eq.{u,u})
    {T : Type u} {f g : T → T} (agree : ∀ t, f t = g t) : f = g := by
  letI := exceptionMonad (shift (f := f))
  letI : LawfulMonad (WindowM f) := lawful shift shift_eq
  exact (congrArg readWindow (law (failure agree) (failure agree))).symm

private theorem viaStateSeqRight (law : type_of% @StateT.seqRight_eq.{u,u})
    {T : Type u} {f g : T → T} (agree : ∀ t, f t = g t) : f = g := by
  letI := exceptionMonad (shift (f := f))
  letI : LawfulMonad (WindowM f) := lawful shift shift_eq
  exact (congrArg readWindow (law (failure agree) (failure agree))).symm

public theorem fromStateSeqLeft (law : type_of% @StateT.seqLeft_eq.{max 1 u v, max 1 u v}) :
    type_of% @funext.{u,v} :=
  funextFromEndomorphisms (viaStateSeqLeft law)

public theorem fromStateSeqRight (law : type_of% @StateT.seqRight_eq.{max 1 u v, max 1 u v}) :
    type_of% @funext.{u,v} :=
  funextFromEndomorphisms (viaStateSeqRight law)

open Lean in
run_cmd
  for n in [``fromStateSeqLeft, ``fromStateSeqRight] do
    unless (← collectAxioms n).isEmpty do throwError "state sequencing witness {n} uses axioms"

namespace MapAfterBind

/-- Two readers with a proof that the entire functions agree. -/
private abbrev Paired (T A : Type u) := {p : (T → A) × (T → A) // p.1 = p.2}

private def diagonal {T A : Type u} (f : T → A) : Paired T A := ⟨(f, f), rfl⟩

private theorem diagonalExists {T A : Type u} (x : Paired T A) : ∃ f, x = diagonal f := by
  rcases x with ⟨⟨f, g⟩, h⟩
  cases h
  exact ⟨f, rfl⟩

private def bindPair {T A B : Type u} (x : Paired T A) (k : A → Paired T B) : Paired T B :=
  ⟨(fun t => (k (x.val.1 t)).val.2 t, fun t => (k (x.val.2 t)).val.2 t),
    congrArg (fun r (t : T) => (k (r t)).val.2 t) x.property⟩

@[instance_reducible] private def monad (T : Type u) : Monad (Paired T) where
  pure a := diagonal fun _ => a
  bind x k := bindPair x k
  map f x := diagonal fun t => f (x.val.1 t)

private theorem lawful (T : Type u) : letI := monad T; LawfulMonad (Paired T) := by
  letI := monad T
  exact {
    map_const := rfl
    id_map := by intro α x; obtain ⟨f, rfl⟩ := diagonalExists x; rfl
    comp_map := by intros; rfl
    map_pure := by intros; rfl
    pure_seq := by intros; rfl
    seq_pure := by intro α β g x; obtain ⟨f, rfl⟩ := diagonalExists g; rfl
    seqLeft_eq := by
      intro α β x y
      obtain ⟨f, rfl⟩ := diagonalExists x
      obtain ⟨g, rfl⟩ := diagonalExists y
      rfl
    seqRight_eq := by
      intro α β x y
      obtain ⟨f, rfl⟩ := diagonalExists x
      obtain ⟨g, rfl⟩ := diagonalExists y
      rfl
    seq_assoc := by
      intro α β γ x g h
      obtain ⟨a, rfl⟩ := diagonalExists x
      obtain ⟨b, rfl⟩ := diagonalExists g
      obtain ⟨c, rfl⟩ := diagonalExists h
      rfl
    bind_pure_comp := by intro α β f x; obtain ⟨g, rfl⟩ := diagonalExists x; rfl
    bind_map := by intro A B x y; obtain ⟨r, rfl⟩ := diagonalExists y; rfl
    pure_bind := by
      intro α β x f
      change diagonal (f x).val.2 = f x
      obtain ⟨g, hg⟩ := diagonalExists (f x)
      rw [hg]
      rfl
    bind_assoc := by intros; rfl
  }

/-- Mapping selects the first reader. Binding selects the second result of its continuation,
even when the continuation depends on the input. -/
public theorem funextFromMapBind (law : type_of% @map_bind.{max 1 u v, max 1 u v}) : type_of% @funext.{u,v} := by
  apply funextFromEndomorphisms
  intro T f g agree
  letI := monad T
  letI := lawful T
  let read : Paired T T := diagonal id
  let action (t : T) : Paired T T := ⟨(fun _ => f t, fun _ => g t), congrArg (fun x (_ : T) => x) (agree t)⟩
  exact (congrArg (fun z : Paired T T => z.val.1) (@law (Paired T) T T T _ _ id read action)).symm

/-- Lifting a bind through the exception transformer compares the two readers of its continuation. -/
public theorem funextFromExceptLiftBind
    (law : type_of% @ExceptT.lift_bind.{max 1 u v, max 1 u v}) : type_of% @funext.{u,v} := by
  apply funextFromEndomorphisms
  intro T f g agree
  letI := monad T
  letI := lawful T
  let read : Paired T T := diagonal id
  let action (t : T) : Paired T T := ⟨(fun _ => f t, fun _ => g t), congrArg (fun x (_ : T) => x) (agree t)⟩
  let observe (z : Paired T (Except T T)) (t : T) :=
    match z.val.1 t with | .ok a => a | .error e => e
  exact (congrArg observe (law (ε := T) read action)).symm

public theorem funextFromExceptLift
    (law : type_of% @ExceptT.instLawfulMonadLift.{max 1 u v, max 1 u v}) : type_of% @funext.{u,v} := by
  apply funextFromExceptLiftBind
  intro m _ _ α β ε ma f
  letI : LawfulMonadLift m (ExceptT ε m) := law
  exact LawfulMonadLift.monadLift_bind (m := m) (n := ExceptT ε m) ma f

/-- Sequencing stateful readers can compare the two projections of an input-dependent action. -/
public theorem funextFromStateRunSeq (rule : type_of% @StateT.run_seq.{max 1 u v,max 1 u v}) :
    type_of% @funext.{u,v} := by
  apply funextFromEndomorphisms
  intro T f g h
  letI := monad T
  letI := lawful T
  let read : StateT (Option T) (Paired T) (T → T) := fun _ => diagonal fun t => (id, some t)
  let action : StateT (Option T) (Paired T) T
    | none => diagonal fun t => (t, none)
    | some t => ⟨(fun _ => (f t, none), fun _ => (g t, none)), congrArg (fun (a : T) (_ : T) => (a, (none : Option T))) (h t)⟩
  exact (congrArg (fun z : Paired T (T × Option T) => fun t => (z.val.1 t).1) (rule read action none)).symm

private def scanAction {T : Type u} {f g : T → T} (h : ∀ t, f t = g t) : Option T → Bool → Paired T (Option T)
  | _, false => diagonal (fun t => some t)
  | none, true => diagonal fun _ => none
  | some t, true => ⟨(fun _ => some (f t), fun _ => some (g t)), congrArg (fun a (_ : T) => some a) (h t)⟩

private def thirdState {T : Type u} (m : Paired T (List (Option T))) (t : T) : T :=
  (m.val.1 t).tail.tail.head?.join.getD t

/-- The second scan step reads the state returned by the first step. -/
public theorem funextFromScanlCons (rule : type_of% @List.scanlM_cons.{max 1 u v,max 1 u v,0}) : type_of% @funext.{u,v} := by
  apply funextFromEndomorphisms
  intro T f g h
  letI := monad T
  letI := lawful T
  let e := rule (f := scanAction h) (init := none) (x := false) (xs := [true])
  exact (congrArg thirdState e).symm

open Lean in
run_cmd
  for name in [``funextFromMapBind, ``funextFromExceptLiftBind, ``funextFromExceptLift,
      ``funextFromStateRunSeq, ``funextFromScanlCons] do
    unless (← collectAxioms name).isEmpty do throwError "monad witness {name} depends on axioms"

end MapAfterBind

namespace ReturnImage

variable {m : Type u → Type v} [Monad m] [LawfulMonad m] [MonadAttach m] [LawfulMonadAttach m]
         {n : Type u → Type w} [Monad n] [LawfulMonad n] [MonadAttach n] [LawfulMonadAttach n]
         [MonadLiftT m n] [LawfulMonadLiftT m n]

/-- A computation factors through the subtype of results satisfying P. -/
def IsImage {α : Type u} (P : α → Prop) (x : m α) : Prop :=
  ∃ y : m (Subtype P), Subtype.val <$> y = x

/-- Lawful attachment constructs a witness for every postcondition on the possible results. -/
theorem imageIff {α : Type u} {P : α → Prop} {x : m α} :
    IsImage P x ↔ (∀ a, MonadAttach.CanReturn x a → P a) := by
  constructor
  · rintro ⟨y, rfl⟩ a h
    exact LawfulMonadAttach.canReturn_map_imp h
  · intro ensures
    let pack (a : Subtype (MonadAttach.CanReturn x)) : Subtype P := ⟨a.val, ensures a.val a.property⟩
    refine ⟨pack <$> MonadAttach.attach x, ?_⟩
    exact (comp_map pack Subtype.val _).symm.trans WeaklyLawfulMonadAttach.map_attach

/-- Lifting an action projected from the subtype of P still factors through that subtype. -/
def LiftImages (m : Type u → Type v) (n : Type u → Type w) [Monad m] [Monad n] [MonadLiftT m n] : Prop :=
  ∀ {α : Type u} (P : α → Prop) (x : m (Subtype P)), IsImage P (liftM (n := n) (Subtype.val <$> x))

omit [LawfulMonad m] [LawfulMonadLiftT m n] in
theorem liftIff :
    (∀ {α : Type u} (x : m α) (a : α), MonadAttach.CanReturn (liftM (n := n) x) a → MonadAttach.CanReturn x a) ↔
      LiftImages m n := by
  constructor
  · intro lift α P x
    exact imageIff.mpr fun a h => LawfulMonadAttach.canReturn_map_imp (lift _ a h)
  · intro images α x a h
    have e := images (MonadAttach.CanReturn x) (MonadAttach.attach x)
    rw [WeaklyLawfulMonadAttach.map_attach] at e
    exact imageIff.mp e a h

/-- Given a certified input and a continuation whose reachable outputs factor through Q,
sequencing the input and continuation also factors through Q. -/
def BindImages (m : Type u → Type v) [Monad m] : Prop :=
  ∀ {α β : Type u} (P : α → Prop) (Q : β → Prop) (x : m (Subtype P)) (f : α → m β),
    (∀ a, P a → IsImage Q (f a)) → IsImage Q ((Subtype.val <$> x) >>= f)

theorem bindIff :
    (∀ {α β : Type u} (x : m α) (f : α → m β) (b : β), MonadAttach.CanReturn (x >>= f) b →
      ∃ a, MonadAttach.CanReturn x a ∧ MonadAttach.CanReturn (f a) b) ↔ BindImages m := by
  constructor
  · intro law α β P Q x f restrict
    apply imageIff.mpr
    intro b hb
    obtain ⟨a, ha, hfb⟩ := law _ f b hb
    exact imageIff.mp (restrict a (LawfulMonadAttach.canReturn_map_imp ha)) b hfb
  · intro images α β x f b hb
    let P (a : α) := MonadAttach.CanReturn x a
    let Q (b : β) := ∃ a, P a ∧ MonadAttach.CanReturn (f a) b
    have hx := images P Q (MonadAttach.attach x) f (fun a ha =>
      imageIff.mpr fun _ h => ⟨a, ha, h⟩)
    rw [WeaklyLawfulMonadAttach.map_attach] at hx
    exact imageIff.mp hx b hb

abbrev PreservesBindImages := ∀ (m : Type u → Type v) [Monad m] [LawfulMonad m] [MonadAttach m] [LawfulMonadAttach m],
  BindImages m

abbrev PreservesLiftImages := ∀ (m : Type u → Type v) (n : Type u → Type w)
  [Monad m] [MonadAttach m] [LawfulMonad m] [LawfulMonadAttach m]
  [Monad n] [MonadAttach n] [LawfulMonad n] [LawfulMonadAttach n]
  [MonadLiftT m n] [LawfulMonadLiftT m n], LiftImages m n

theorem bindRule : (type_of% @LawfulMonadAttach.canReturn_bind_imp'.{u,v}) ↔ PreservesBindImages.{u,v} := by
  constructor
  · intro rule m _ _ _ _
    exact bindIff.mp fun x f b h => rule (x := x) (f := f) (b := b) h
  · intro images m α β b _ _ _ _ x f h
    exact bindIff.mpr (images m) x f b h

theorem liftRule : (type_of% @LawfulMonadAttach.canReturn_liftM_imp'.{u,v,w}) ↔ PreservesLiftImages.{u,v,w} := by
  constructor
  · intro rule m n _ _ _ _ _ _ _ _ _ _
    exact liftIff.mp fun x a h => rule (m := m) (n := n) (x := x) (a := a) h
  · intro images m n α _ _ _ _ _ _ _ _ _ _ x a h
    exact liftIff.mpr (images m n) x a h

def equivalences : List (Name × Name × Name) := [
  (``LawfulMonadAttach.canReturn_bind_imp', ``PreservesBindImages, ``bindRule),
  (``LawfulMonadAttach.canReturn_liftM_imp', ``PreservesLiftImages, ``liftRule)]

end ReturnImage

namespace FiniteFold

/-- An error value carries two representatives of the same value. -/
private abbrev Twin (T : Type u) := {p : T × T // p.1 = p.2}
private def swap {T : Type u} (p : Twin T) : Twin T := ⟨(p.val.2, p.val.1), p.2.symm⟩
private theorem swap_eq {T : Type u} (p : Twin T) : swap p = p := by
  obtain ⟨⟨a, b⟩, h⟩ := p
  cases h
  rfl
private def step {T : Type u} {f g : T → T} (h : ∀ x, f x = g x) (x : T) : Except (Twin T) T :=
  .error ⟨(f x, g x), h x⟩
private def observe {T : Type u} (v : T → Except (Twin T) T) (x : T) : T :=
  match v x with | .ok t => t | .error e => e.val.1


/-- The two ways of composing a monadic step with the unit agree as functions. -/
abbrev MoveUnit := ∀ {m : Type u → Type u} [Monad m] [LawfulMonad m] {T : Type u} (s : T → m T),
  (fun x => s x >>= pure) = fun x => pure x >>= s
/-- A second composition with the unit preserves the entire Kleisli arrow. -/
abbrev RepeatUnit := ∀ {m : Type u → Type u} [Monad m] [LawfulMonad m] {T : Type u} (s : T → m T),
  (fun x => s x >>= pure) = fun x => (s x >>= pure) >>= pure

theorem funextOfMoveUnit (law : MoveUnit.{max 1 u v}) : type_of% @funext.{u,v} := by
  apply funextFromEndomorphisms
  intro T f g h
  letI := exceptionMonad (@swap T)
  letI := lawful (@swap T) swap_eq
  exact (congrArg observe (@law (Except (Twin T)) _ _ T (step h))).symm

theorem funextOfRepeatUnit (law : RepeatUnit.{max 1 u v}) : type_of% @funext.{u,v} := by
  apply funextFromEndomorphisms
  intro T f g h
  letI := exceptionMonad (@swap T)
  letI := lawful (@swap T) swap_eq
  exact (congrArg observe (@law (Except (Twin T)) _ _ T (step h))).symm

public theorem funextOfLeftSuccessor (rule : type_of% @Fin.foldlM_succ_last.{max 1 u v, max 1 u v}) :
    type_of% @funext.{u,v} := by
  apply funextOfMoveUnit
  intro m _ _ T s
  have e := @rule m T 0 _ _ (fun x _ => s x)
  rw [Fin.foldlM_succ, Fin.foldlM_zero] at e
  exact e

public theorem funextOfRightSuccessor (rule : type_of% @Fin.foldrM_succ.{max 1 u v, max 1 u v}) :
    type_of% @funext.{u,v} := by
  apply funextOfMoveUnit
  intro m _ _ T s
  have e := @rule m 0 T _ _ (fun _ x => s x)
  rw [Fin.foldrM_succ_last, Fin.foldrM_zero] at e
  exact e

public theorem funextOfLeftAddition (rule : type_of% @Fin.foldlM_add.{max 1 u v, max 1 u v}) :
    type_of% @funext.{u,v} := by
  apply funextOfRepeatUnit
  intro m _ _ T s
  have e := @rule m T 1 0 _ _ (fun x _ => s x)
  change Fin.foldlM 1 (fun x _ => s x) = fun x => Fin.foldlM 1 (fun x _ => s x) x >>= Fin.foldlM 0 (fun x _ => s x) at e
  rw [Fin.foldlM_succ, Fin.foldlM_zero] at e
  exact e

public theorem funextOfRightAddition (rule : type_of% @Fin.foldrM_add.{max 1 u v, max 1 u v}) :
    type_of% @funext.{u,v} := by
  apply funextOfRepeatUnit
  intro m _ _ T s
  have e := @rule m 0 1 T _ _ (fun _ x => s x)
  change Fin.foldrM 1 (fun _ x => s x) = fun x => Fin.foldrM 1 (fun _ x => s x) x >>= Fin.foldrM 0 (fun _ x => s x) at e
  rw [Fin.foldrM_succ_last, Fin.foldrM_zero] at e
  exact e

open Lean in
run_cmd
  for n in [``funextOfMoveUnit, ``funextOfRepeatUnit] do
    unless (← collectAxioms n).isEmpty do throwError "finite fold witness {n} uses axioms"

end FiniteFold

end TransformerLaws

namespace AttachDecision

/-- The identity action returns its argument. Its weak attachment may also permit an arbitrary proposition. -/
@[instance_reducible] private def attach (p : Prop) : MonadAttach Id where
  CanReturn x a := a = x ∨ p
  attach x := ⟨x, Or.inl rfl⟩

private theorem weak (p : Prop) : @WeaklyLawfulMonadAttach Id _ (attach p) := by
  letI := attach p
  exact ⟨rfl⟩

/-- In the right-hand continuation of bind_attach_of_nonempty the action can be false
and the argument true. Deciding the attachment predicate there decides p. -/
def decideFromBranch (classify : ∀ [a : MonadAttach Id] [WeaklyLawfulMonadAttach Id],
    Decidable (a.CanReturn (α := Bool) false true)) (p : Prop) : Decidable p := by
  letI := attach p
  letI := weak p
  cases classify with
  | isTrue yes => exact isTrue (yes.elim Bool.noConfusion id)
  | isFalse no => exact isFalse fun hp => no (Or.inr hp)

private def pinnedBranch [a : MonadAttach Id] [w : WeaklyLawfulMonadAttach Id] :=
  @WeaklyLawfulMonadAttach.bind_attach_of_nonempty Id Unit Bool _ a _ w ⟨()⟩ false (fun _ => ())

open Meta Elab.Command in
run_cmd
  liftTermElabM do
    let site ← getConstInfo ``pinnedBranch
    forallTelescope site.type fun args conclusion => do
      let some (_, _, rhs) := conclusion.eq? | throwError "expected an equality at the pinned attachment law"
      unless rhs.isAppOfArity ``Bind.bind 6 do throwError "expected the right-hand bind"
      let cont := rhs.appArg!
      unless cont.isLambda do throwError "expected the attached value's continuation"
      let branch := cont.bindingBody!.instantiate1 (mkConst ``Bool.true)
      unless branch.isAppOfArity ``dite 5 do throwError "missing dependent branch in the pinned statement"
      let decision := branch.getAppArgs[2]!
      unless decision.isAppOfArity ``Classical.propDecidable 1 do throwError "unexpected attachment decision"
      let required ← mkForallFVars args (← inferType decision)
      let reduction ← getConstInfo ``decideFromBranch
      unless Kernel.isDefEqGuarded (← getEnv) {} required reduction.type.bindingDomain! do
        throwError "the pinned branch decision differs from the proposition decider input"
    unless (← collectAxioms ``decideFromBranch).isEmpty do throwError "the attachment reduction depends on axioms"

end AttachDecision

end OmegaChecks.InitBoundaries
