import OmegaInit.Data.Erased

example {α : Sort u} {a b : α} (same : Omega.Erased.mk a = Omega.Erased.mk b) : a = b :=
  Omega.Erased.mk_inj.mp same

example {α : Sort u} {a b : α} (same : a = b) : Omega.Erased.mk a = Omega.Erased.mk b :=
  Omega.Erased.mk_inj.mpr same

example (a : Nat) : (Omega.Erased.mk a).val a := rfl
