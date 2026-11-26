module
public import Lean
import Lean.Replay
import all Lean.Util.CollectAxioms
public import OmegaChecks.InitInventory.Extensionality

public section

open Lean
namespace OmegaChecks.InitBoundaries
universe u v w z

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

end TransformerLaws

end OmegaChecks.InitBoundaries
