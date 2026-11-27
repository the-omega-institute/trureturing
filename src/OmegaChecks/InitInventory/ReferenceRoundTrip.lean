module
public import Init.System.ST

namespace OmegaChecks.InitBoundaries.ReferenceRoundTrip

public abbrev Snapshot := ST.RefPointed.type × Void Unit
public abbrev Callback := Snapshot → Bool

private def observe (read : ST.Ref Unit Callback → ST Unit Callback) (s : Snapshot) : Bool :=
  (read ⟨s.1, ⟨fun _ => false⟩⟩ s.2).val s

/-- A read after allocation uses exactly the handle and world returned by the allocator. -/
public def readsInitialValue (alloc : Callback → ST Unit (ST.Ref Unit Callback))
    (read : ST.Ref Unit Callback → ST Unit Callback) : Prop :=
  ∀ f initial, let out := alloc f initial
               (read out.val out.state).val = f

/-- A read after a write uses the same handle and the world returned by the writer. -/
public def readsWrittenValue (write : ST.Ref Unit Callback → Callback → ST Unit Unit)
    (read : ST.Ref Unit Callback → ST Unit Callback) : Prop :=
  ∀ r f initial, (read r (write r f initial).state).val = f

private theorem noEncoding (pack : Callback → Snapshot) (read : ST.Ref Unit Callback → ST Unit Callback)
    (recover : ∀ f, observe read (pack f) = f (pack f)) : False := by
  let negate : Callback := fun s => !(observe read s)
  have fixed := recover negate
  change observe read (pack negate) = !(observe read (pack negate)) at fixed
  cases h : observe read (pack negate) <;> rw [h] at fixed <;> cases fixed

private theorem noAlloc {alloc read} (recovers : readsInitialValue alloc read) : False := by
  obtain ⟨initial⟩ := Void.instNonempty (σ := Unit)
  let pack (f : Callback) : Snapshot :=
    let out := alloc f initial
    (out.val.ref, out.state)
  exact noEncoding pack read (fun f => congrFun (recovers f initial) (pack f))

private theorem noWrite {write read} (recovers : readsWrittenValue write read) : False := by
  obtain ⟨initial⟩ := Void.instNonempty (σ := Unit)
  obtain ⟨address⟩ := ST.RefPointed.property
  let r : ST.Ref Unit Callback := ⟨address, ⟨fun _ => false⟩⟩
  let pack (f : Callback) : Snapshot := (address, (write r f initial).state)
  exact noEncoding pack read (fun f => congrFun (recovers r f initial) (pack f))

public theorem primAlloc (alloc : type_of% @ST.Prim.mkRef) (read : type_of% @ST.Prim.Ref.get) :
    readsInitialValue alloc read → False := noAlloc
public theorem alloc (alloc : type_of% @ST.mkRef) (read : type_of% @ST.Ref.get) :
    readsInitialValue (alloc (m := ST Unit)) (read (m := ST Unit)) → False := noAlloc

public theorem primSet (write : type_of% @ST.Prim.Ref.set) (read : type_of% @ST.Prim.Ref.get) :
    readsWrittenValue write read → False := noWrite
public theorem set (write : type_of% @ST.Ref.set) (read : type_of% @ST.Ref.get) :
    readsWrittenValue (write (m := ST Unit)) (read (m := ST Unit)) → False := noWrite

/-- Constant updates suffice to recover every payload in the world returned by a modifier. -/
public def readsModifiedValue (update : ST.Ref Unit Callback → (Callback → Callback) → ST Unit Unit)
    (read : ST.Ref Unit Callback → ST Unit Callback) : Prop :=
  ∀ r f initial, (read r (update r (fun _ => f) initial).state).val = f

public theorem primModify (update : type_of% @ST.Prim.Ref.modify) (read : type_of% @ST.Prim.Ref.get) :
    readsModifiedValue update read → False :=
  noWrite (write := fun r f => update r (fun _ => f))

public theorem modify (update : type_of% @ST.Ref.modify) (read : type_of% @ST.Ref.get) :
    readsModifiedValue (update (m := ST Unit)) (read (m := ST Unit)) → False :=
  noWrite (write := fun r f => update (m := ST Unit) r (fun _ => f))

end OmegaChecks.InitBoundaries.ReferenceRoundTrip
