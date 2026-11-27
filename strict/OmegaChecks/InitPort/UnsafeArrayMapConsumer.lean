module
prelude
public import OmegaInit.Data.Array.Basic

@[export omega_test_array_map_unsafe]
public unsafe def mapUnsafe {α β : Type} {m : Type → Type} [Omega.Monad m]
    (f : α → m β) (xs : Omega.Array α) : m (Omega.Array β) :=
  Omega.Array.mapMUnsafe f xs

@[export omega_test_array_index_map_unsafe]
public unsafe def mapIndexedUnsafe {α β : Type} {m : Type → Type} [Omega.Monad m]
    (xs : Omega.Array α) (f : (i : Nat) → α → (Nat.lt i (Omega.Array.size xs)) → m β) : m (Omega.Array β) :=
  Omega.Array.mapFinIdxMUnsafe xs f
