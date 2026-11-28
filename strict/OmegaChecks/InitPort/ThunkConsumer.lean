module
prelude
public import OmegaInit.Core

/-! Exercise creation, forcing, and field and pattern access in an ordinary strict consumer. -/

@[export omega_memo_make] public def memoMake (f : Unit → Nat) : Omega.Thunk Nat := ⟨f⟩
@[export omega_memo_pure] public def memoPure (v : Nat) := Omega.Thunk.pure v
@[export omega_memo_get] public def memoGet (t : Omega.Thunk Nat) := t.get
@[export omega_memo_field] public def memoField (t : Omega.Thunk Nat) := t.fn ()
@[export omega_memo_impl] public def memoImpl (t : Omega.Thunk Nat) := Omega.Thunk.fnImpl t ()
@[export omega_memo_cases] public def memoCases (t : Omega.Thunk Nat) := match t with | ⟨f⟩ => f ()
@[export omega_memo_map] public def memoMap (f : Nat → Nat) (t : Omega.Thunk Nat) := Omega.Thunk.map f t
@[export omega_memo_bind] public def memoBind (t : Omega.Thunk Nat) (f : Nat → Omega.Thunk Nat) := Omega.Thunk.bind t f
@[export omega_memo_default] public def memoDefault (n : Nat) : Omega.Thunk Nat :=
  @Omega.Inhabited.default _ (@Omega.instInhabitedThunk Nat ⟨n⟩)
