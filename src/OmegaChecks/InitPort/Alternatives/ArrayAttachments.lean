module
public import Init.Data.Vector.Attach
import all Init.Data.Vector.Attach
public import Init.Data.Array.Mem
public import Init.Data.Array.Attach
import all Init.Data.Array.Attach

/-! Membership and projection laws for arrays and vectors carrying proofs on their elements. -/
namespace OmegaChecks.InitPort.Alternatives

@[expose] public def List.pmapImpl : type_of% @_root_.List.pmapImpl := @_root_.List.pmap

public theorem List.pmap_eq_pmapImpl : @_root_.List.pmap = @List.pmapImpl := rfl

@[expose] public def Array.pmapImpl : type_of% @_root_.Array.pmapImpl := @_root_.Array.pmap

public theorem Array.pmap_eq_pmapImpl : @_root_.Array.pmap = @Array.pmapImpl := rfl

@[expose] public def Vector.pmapImpl : type_of% @_root_.Vector.pmapImpl := @_root_.Vector.pmap

public theorem Vector.pmap_eq_pmapImpl : @_root_.Vector.pmap = @Vector.pmapImpl := rfl

public theorem Array.attach_congr : type_of% @_root_.Array.attach_congr := by
  intro α xs ys h
  subst ys
  exact (Array.map_id xs.attach).symm

public theorem Array.attach_map_subtype_val : type_of% @_root_.Array.attach_map_subtype_val := by
  intro α xs
  exact (Array.attach_map_val xs id).trans (Array.map_id xs)

public theorem Array.attachWith_map_subtype_val : type_of% @_root_.Array.attachWith_map_subtype_val := by
  intro α p xs H
  exact (Array.attachWith_map_val (f := id) H).trans (Array.map_id xs)

public theorem Array.mem_attach : type_of% @_root_.Array.mem_attach := by
  intro α xs x
  exact (Array.mem_attachWith (q := (· ∈ xs)) _ x).mpr x.2

public theorem Array.mem_pmap : type_of% @_root_.Array.mem_pmap := by
  intro α β pred f xs h b
  rw [Array.pmap_eq_map_attach, Array.mem_map]
  constructor
  · rintro ⟨⟨a, mem⟩, _, eq⟩
    exact ⟨a, mem, eq⟩
  · rintro ⟨a, mem, eq⟩
    exact ⟨⟨a, mem⟩, Array.mem_attach _ _, eq⟩

public theorem Array.attach_push : type_of% @_root_.Array.attach_push := by
  intro α a xs
  apply (Array.map_inj_right (f := Subtype.val) (fun _ _ => Subtype.ext)).mp
  rw [Array.attach_map_subtype_val, Array.map_push, Array.map_map]
  change xs.push a = (xs.attach.map Subtype.val).push a
  rw [Array.attach_map_subtype_val]

public theorem Array.attach_append : type_of% @_root_.Array.attach_append := by
  intro α xs ys
  apply (Array.map_inj_right (f := Subtype.val) (fun _ _ => Subtype.ext)).mp
  rw [Array.attach_map_subtype_val, Array.map_append, Array.map_map, Array.map_map]
  change xs ++ ys = xs.attach.map Subtype.val ++ ys.attach.map Subtype.val
  rw [Array.attach_map_subtype_val, Array.attach_map_subtype_val]

public theorem Array.attach_reverse : type_of% @_root_.Array.attach_reverse := by
  intro α xs
  apply (Array.map_inj_right (f := Subtype.val) (fun _ _ => Subtype.ext)).mp
  rw [Array.attach_map_subtype_val, Array.map_map]
  change xs.reverse = xs.attach.reverse.map Subtype.val
  rw [Array.map_reverse, Array.attach_map_subtype_val]

public theorem Array.reverse_attach : type_of% @_root_.Array.reverse_attach := by
  intro α xs
  apply (Array.map_inj_right (f := Subtype.val) (fun _ _ => Subtype.ext)).mp
  rw [Array.map_map]
  change xs.attach.reverse.map Subtype.val = xs.reverse.attach.map Subtype.val
  rw [Array.map_reverse, Array.attach_map_subtype_val, Array.attach_map_subtype_val]

public theorem Array.unattach_flatten : type_of% @_root_.Array.unattach_flatten := by
  intros
  exact Array.map_flatten

private theorem filterMapValues {f g : α → Option β} (same : ∀ a, f a = g a) (xs : Array α) :
    xs.filterMap f = xs.filterMap g := by
  cases xs with
  | mk xs =>
    rw [List.filterMap_toArray, List.filterMap_toArray]
    apply congrArg List.toArray
    induction xs with
    | nil => rfl
    | cons x xs ih => rw [List.filterMap_cons, List.filterMap_cons, same, ih]

private theorem projectFound {q : α → Prop} (o : Option α) (w : ∀ a, o = some a → q a) :
    o = (o.pbind (fun a h => some (⟨a, w a h⟩ : Subtype q))).map Subtype.val := by
  cases o <;> rfl

public theorem Array.attach_filterMap : type_of% @_root_.Array.attach_filterMap := by
  intro α β xs f
  apply (Array.map_inj_right (f := Subtype.val) (fun _ _ => Subtype.ext)).mp
  rw [Array.attach_map_subtype_val, Array.map_filterMap]
  conv => lhs; rw [← Array.attach_map_subtype_val xs, Array.filterMap_map]
  apply filterMapValues
  intro ⟨a, ha⟩
  exact projectFound (f a) _

public theorem Array.attach_filter : type_of% @_root_.Array.attach_filter := by
  intro α xs p
  apply (Array.map_inj_right (f := Subtype.val) (fun _ _ => Subtype.ext)).mp
  rw [Array.attach_map_subtype_val, Array.map_filterMap]
  conv => lhs; rw [← Array.filterMap_eq_filter (p := p) rfl, ← Array.attach_map_subtype_val xs, Array.filterMap_map]
  apply filterMapValues
  intro ⟨a, ha⟩
  by_cases h : p a <;> simp only [Function.comp_def, Option.guard, h, Bool.false_eq_true, ite_false, ite_true, dite_true, dite_false, Option.map_some, Option.map_none]

public theorem Array.sizeOf_get : type_of% @_root_.Array.sizeOf_get := by
  intro α inst xs i h
  cases xs with
  | mk xs =>
    apply Nat.lt_trans (List.sizeOf_get xs ⟨i, h⟩)
    change sizeOf xs < 1 + sizeOf xs
    rw [Nat.one_add]
    exact Nat.lt_succ_self _


public theorem Vector.attach_congr : type_of% @_root_.Vector.attach_congr := by
  intro α n xs ys h
  subst ys
  exact (Vector.map_id xs.attach).symm

public theorem Vector.attach_map_subtype_val : type_of% @_root_.Vector.attach_map_subtype_val := by
  intro α n xs
  exact (Vector.attach_map_val xs id).trans (Vector.map_id xs)

public theorem Vector.attachWith_map_subtype_val : type_of% @_root_.Vector.attachWith_map_subtype_val := by
  intro α n p xs H
  exact (Vector.attachWith_map_val (f := id) H).trans (Vector.map_id xs)

public theorem Vector.mem_attach : type_of% @_root_.Vector.mem_attach := by
  intro α n xs x
  exact (Vector.mem_attachWith (q := (· ∈ xs)) _ x).mpr x.2

public theorem Vector.mem_pmap : type_of% @_root_.Vector.mem_pmap := by
  intro α β n pred f xs h b
  rw [Vector.pmap_eq_map_attach, Vector.mem_map]
  constructor
  · rintro ⟨⟨a, mem⟩, _, eq⟩
    exact ⟨a, mem, eq⟩
  · rintro ⟨a, mem, eq⟩
    exact ⟨⟨a, mem⟩, Vector.mem_attach _ _, eq⟩

public theorem Vector.attach_append : type_of% @_root_.Vector.attach_append := by
  intro α n m xs ys
  apply (Vector.map_inj_right (f := Subtype.val) (fun _ _ => Subtype.ext)).mp
  rw [Vector.attach_map_subtype_val, Vector.map_append, Vector.map_map, Vector.map_map]
  change xs ++ ys = xs.attach.map Subtype.val ++ ys.attach.map Subtype.val
  rw [Vector.attach_map_subtype_val, Vector.attach_map_subtype_val]

public theorem Vector.attach_reverse : type_of% @_root_.Vector.attach_reverse := by
  intro α n xs
  apply (Vector.map_inj_right (f := Subtype.val) (fun _ _ => Subtype.ext)).mp
  rw [Vector.attach_map_subtype_val, Vector.map_map]
  change xs.reverse = xs.attach.reverse.map Subtype.val
  rw [Vector.map_reverse, Vector.attach_map_subtype_val]

public theorem Vector.unattach_flatten : type_of% @_root_.Vector.unattach_flatten := by
  intros
  exact Vector.map_flatten

end OmegaChecks.InitPort.Alternatives
