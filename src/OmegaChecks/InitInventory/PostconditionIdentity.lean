module
public import Init.Data.Iterators.PostconditionMonad

public section
namespace OmegaChecks.InitBoundaries.PostconditionIdentity
open Std.Iterators

/-- An operation carries no values, so an arbitrary postcondition can be supplied without a proof of it. -/
private abbrev Silent (_ : Type) := Unit
private instance : Monad Silent where pure _ := (); bind _ _ := ()
private instance : LawfulMonad Silent := by
  exact {
    map_const := by intros; rfl
    id_map := by intros; rfl
    comp_map := by intros; rfl
    seqLeft_eq := by intros; rfl
    seqRight_eq := by intros; rfl
    pure_seq := by intros; rfl
    map_pure := by intros; rfl
    seq_pure := by intros; rfl
    seq_assoc := by intros; rfl
    bind_pure_comp := by intros; rfl
    bind_map := by intros; rfl
    pure_bind := by intros; rfl
    bind_assoc := by intros; rfl
  }

def RightIdentity := ∀ p : Prop, (∃ a : Unit, p ∧ a = ()) = p

theorem rightIdentity (law : type_of% (@PostconditionT.bind_pure.{0,0})) : RightIdentity := by
  intro p
  let x : PostconditionT Silent Unit := ⟨fun _ => p, ()⟩
  exact congrArg (fun (t : PostconditionT Silent Unit) => t.Property ()) (law (x := x))

def LeftIdentity := ∀ p : Prop, (∃ a : Unit, () = a ∧ p) = p

theorem leftIdentity (law : type_of% (@PostconditionT.pure_bind.{0,0})) : LeftIdentity := by
  intro p
  let f (_ : Unit) : PostconditionT Silent Unit := ⟨fun _ => p, ()⟩
  exact congrArg (fun (t : PostconditionT Silent Unit) => t.Property ()) (law (a := ()) (f := f))

theorem ofMonad (law : type_of% (@Std.Iterators.instLawfulMonadPostconditionT.{0,0})) : LeftIdentity := by
  intro p
  let f (_ : Unit) : PostconditionT Silent Unit := ⟨fun _ => p, ()⟩
  letI : LawfulMonad (PostconditionT Silent) := law
  exact congrArg (fun (t : PostconditionT Silent Unit) => t.Property ()) (pure_bind () f)

/-- Mapping a pure value identifies its image predicate with equality at that value. -/
def PureImage := ∀ p q : Prop, (∃ z : {r : Prop // p = r}, z.val = q) = (p = q)

theorem pureImage (law : type_of% (@PostconditionT.map_pure.{0,0})) : PureImage := by
  intro p q
  exact congrArg (fun (t : PostconditionT Silent Prop) => t.Property q) (law (f := id) (a := p))

/-- The map-to-bind law identifies an image over a subtype with a conjunction over its carrier. -/
def ImageBind := ∀ p : Prop, (∃ z : {_a : Unit // p}, z.val = ()) = (∃ a : Unit, p ∧ a = ())

theorem imageBind (law : type_of% (@PostconditionT.map_eq_pure_bind.{0,0})) : ImageBind := by
  intro p
  let x : PostconditionT Silent Unit := ⟨fun _ => p, ()⟩
  exact congrArg (fun (t : PostconditionT Silent Unit) => t.Property ()) (law (f := id) (x := x))

/-- Associativity identifies the two distinct nestings of existential postconditions. -/
def AssociatedPredicates := ∀ p q r : Prop,
  (∃ _ : Unit, (∃ _ : Unit, p ∧ q) ∧ r) = (∃ _ : Unit, p ∧ ∃ _ : Unit, q ∧ r)

theorem associatedPredicates (law : type_of% (@PostconditionT.bind_assoc.{0,0})) : AssociatedPredicates := by
  intro p q r
  let action (s : Prop) : PostconditionT Silent Unit := ⟨fun _ => s, ()⟩
  exact congrArg (fun (t : PostconditionT Silent Unit) => t.Property ())
    (law (x := action p) (f := fun _ => action q) (g := fun _ => action r))

end OmegaChecks.InitBoundaries.PostconditionIdentity
