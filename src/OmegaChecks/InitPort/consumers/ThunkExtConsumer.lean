import OmegaInit.Ext

example {a b : Omega.Thunk α} (h : a.get = b.get) : a = b := Omega.Thunk.ext h
example {a b : Omega.Thunk α} (h : a = b) : a.get = b.get := Omega.Thunk.ext_iff.mp h
example {α : Type u} [Omega.Inhabited α] : Omega.Inhabited (Omega.Thunk α) := inferInstance
