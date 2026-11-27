module
prelude
public import OmegaInit.System.ST

namespace OmegaStrictReference

public abbrev Choice := (α : Type) → Omega.Nonempty α → α

private noncomputable def world : Omega.Void Omega.Unit := Omega.Void.mk (Omega.PUnit.unit : Omega.Unit)

private noncomputable def address : Omega.ST.RefPointed.type :=
  (Omega.ST.Prim.mkRef (Omega.PUnit.unit : Omega.Unit) world).val.ref

/-- The physical handle field and the world are independent of the requested payload type. -/
public noncomputable def selector
    (read : {α : Type} → Omega.ST.Ref Omega.Unit α → Omega.ST Omega.Unit α) : Choice :=
  fun α h => (read (α := α) ⟨address, h⟩ world).val

end OmegaStrictReference
