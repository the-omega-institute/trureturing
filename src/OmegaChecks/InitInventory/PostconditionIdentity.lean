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
end OmegaChecks.InitBoundaries.PostconditionIdentity
