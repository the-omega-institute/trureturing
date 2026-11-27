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

/-- At the concrete world, the successful return field must inhabit the requested type. -/
public noncomputable def Lean.Order.ST.bot'
    (bottom : {α σ : Type} → [Omega.Nonempty α] → Omega.Void σ → Omega.ST.Out σ α) : Choice :=
  fun α h => (@bottom α Omega.Unit h world).val

/-- With an empty success type the error field must inhabit the requested type. -/
public noncomputable def Lean.Order.EST.bot
    (bottom : {ε σ α : Type} → [Omega.Nonempty ε] → Omega.EST ε σ α) : Choice :=
  fun α h => match @bottom α Omega.Unit Omega.Empty h world with
    | .ok impossible _ => impossible.elim
    | .error element _ => element

end OmegaStrictReference
