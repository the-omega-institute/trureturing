module
public import Init.Control.StateRef
import all Init.System.Promise
public import Lean.Data.Name

namespace OmegaChecks.InitBoundaries.ReferenceSelection

/-- A selector exists simultaneously for all nonempty types in the state monad’s universe. -/
public abbrev Selection := Nonempty ((α : Type) → Nonempty α → α)

/-- Any implementations of the two original public constructors supply the world and the
address. The returned selector uses no operation on the hidden representation of either. -/
public noncomputable def choiceUsing (mkWorld : type_of% @Void.mk) (alloc : type_of% @ST.Prim.mkRef)
    (read : ∀ {α}, ST.Ref Unit α → ST Unit α) (α : Type) (h : Nonempty α) : α :=
  let world := mkWorld (σ := Unit) ()
  let address := (alloc (σ := Unit) (α := Unit) () world).val.ref
  (read (α := α) ⟨address, h⟩ world).val

/-- The two hidden representatives are selected within the proposition `Nonempty`. -/
private theorem fromRead (read : ∀ {α}, ST.Ref Unit α → ST Unit α) : Selection := by
  obtain ⟨address⟩ := ST.RefPointed.property
  obtain ⟨state⟩ := Void.instNonempty (σ := Unit)
  exact ⟨fun α h => (read (α := α) ⟨address, h⟩ state).val⟩

public theorem primGet (f : type_of% @ST.Prim.Ref.get) : Selection := fromRead f
public theorem primTake (f : type_of% @ST.Prim.Ref.take) : Selection := fromRead f
public theorem primModifyGet (f : type_of% @ST.Prim.Ref.modifyGet) : Selection :=
  fromRead fun r => f r (fun x => (x, x))
public theorem primModifyGetUnsafe (f : type_of% @ST.Prim.Ref.modifyGetUnsafe) : Selection :=
  fromRead fun r => f r (fun x => (x, x))
public theorem get (f : type_of% @ST.Ref.get) : Selection := fromRead (f (m := ST Unit))
public theorem take (f : type_of% @ST.Ref.take) : Selection := fromRead (f (m := ST Unit))
public theorem modifyGet (f : type_of% @ST.Ref.modifyGet) : Selection :=
  fromRead fun r => f (m := ST Unit) r (fun x => (x, x))
public theorem monadState (f : type_of% @ST.Ref.toMonadStateOf) : Selection :=
  fromRead fun r => (f (m := ST Unit) r).get
public theorem stateGet (f : type_of% @StateRefT'.get) : Selection := fromRead (f (m := ST Unit))
public theorem stateModifyGet (f : type_of% @StateRefT'.modifyGet) : Selection :=
  fromRead fun r => f (m := ST Unit) (fun x => (x, x)) r
public theorem stateInstance (f : type_of% @StateRefT'.instMonadStateOfOfMonadLiftTST) : Selection :=
  fromRead fun r => (f (m := ST Unit)).get r

/-- One hidden promise handle suffices across all payload types. -/
public theorem promiseResult (result : type_of% @IO.Promise.result!) : Selection := by
  obtain ⟨address⟩ := (private_decl% IO.PromisePointed).property
  exact ⟨fun α h => (result (α := α) ⟨address, h⟩).get⟩

/-- Each source keeps its original pinned type through `type_of%` in the corresponding theorem. -/
public def witnesses : List (Lean.Name × Lean.Name × Lean.Name) := [
  (`Init.System.ST, ``ST.Prim.Ref.get, ``primGet),
  (`Init.System.ST, ``ST.Prim.Ref.take, ``primTake),
  (`Init.System.ST, ``ST.Prim.Ref.modifyGet, ``primModifyGet),
  (`Init.System.ST, ``ST.Prim.Ref.modifyGetUnsafe, ``primModifyGetUnsafe),
  (`Init.System.ST, ``ST.Ref.get, ``get),
  (`Init.System.ST, ``ST.Ref.take, ``take),
  (`Init.System.ST, ``ST.Ref.modifyGet, ``modifyGet),
  (`Init.System.ST, ``ST.Ref.toMonadStateOf, ``monadState),
  (`Init.Control.StateRef, ``StateRefT'.get, ``stateGet),
  (`Init.Control.StateRef, ``StateRefT'.modifyGet, ``stateModifyGet),
  (`Init.Control.StateRef, ``StateRefT'.instMonadStateOfOfMonadLiftTST, ``stateInstance),
  (`Init.System.Promise, ``IO.Promise.result!, ``promiseResult)]

end OmegaChecks.InitBoundaries.ReferenceSelection
