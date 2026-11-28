module
import all Init.Data.Array.Basic
import all Init.Data.Array.BasicAux
import all Init.Data.List.Control
import all Init.Data.Array.BinSearch
public import Init.Data.Array.Lemmas
public import Init.Data.Array.Find
public import Init.Data.List.Find
public import Init.Data.List.ToArray

namespace OmegaChecks.InitPort.Alternatives

/- Expand the bounded traversal in place so the exported definition uses only Init primitives. -/
local macro "reversePrefix% " f:term:max as:term:max : term =>
  `(let n := ($as).size
    Nat.rec (motive := fun i => i ≤ n → _) (fun _ => pure none)
      (fun i earlier hi =>
        ($f) (($as)[i]'hi) >>= fun r =>
          Option.casesOn r (earlier (@Nat.le_of_succ_le i n hi)) (fun b => pure (some b))))

@[inline] private noncomputable def revPrefix {α : Type u} {β : Type v} {m : Type v → Type w}
    [Monad m] (f : α → m (Option β)) (as : Array α) :
    (i : Nat) → i ≤ as.size → m (Option β) :=
  reversePrefix% f as

@[expose, implemented_by _root_.Array.findSomeRevM?] public noncomputable def Array.findSomeRevM?
    {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m]
    (f : α → m (Option β)) (as : Array α) : m (Option β) :=
  let n := as.size
  (reversePrefix% f as) n (Nat.le_refl n)

public theorem List.findSomeRevM?_toArray [Monad m] [LawfulMonad m] (f : α → m (Option β)) (l : List α) :
    Array.findSomeRevM? f l.toArray = l.reverse.findSomeM? f := by
  have run (i : Nat) (h : i ≤ l.toArray.size) :
      revPrefix f l.toArray i h = (l.take i).reverse.findSomeM? f := by
    induction i with
    | zero => rw [_root_.List.take_zero, _root_.List.reverse_nil, _root_.List.findSomeM?_nil]; rfl
    | succ i ih =>
      have hi : i < l.length := h
      rw [_root_.List.take_succ_eq_append_getElem hi, _root_.List.reverse_append]
      rw [_root_.List.reverse_singleton, _root_.List.singleton_append, _root_.List.findSomeM?_cons]
      unfold _root_.List.findSomeM?_cons.match_1
      exact congrArg (fun tail => f l[i] >>= fun r => Option.casesOn r tail (fun b => pure (some b)))
        (ih (Nat.le_of_lt hi))
  exact (run l.length (Nat.le_refl _)).trans
    (congrArg (fun xs => _root_.List.findSomeM? f xs.reverse) _root_.List.take_length)

public theorem Array.findSomeRev?_eq_findSome?_reverse {f : α → Option β} {xs : Array α} :
    (Array.findSomeRevM? (m := Id) f xs).run = xs.reverse.findSome? f := by
  cases xs with
  | mk xs =>
    rw [List.findSomeRevM?_toArray, _root_.List.reverse_toArray, _root_.List.findSome?_toArray]
    exact _root_.List.findSome?_eq_findSomeM?.symm

public theorem Array.findRev?_eq_find?_reverse {α : Type} {f : α → Bool} {xs : Array α} :
    (Array.findSomeRevM? (m := Id) (Option.guard f) xs).run = xs.reverse.find? f := by
  cases xs with
  | mk xs =>
    rw [List.findSomeRevM?_toArray, _root_.List.reverse_toArray, _root_.List.find?_toArray,
      ← _root_.List.findSome?_guard]
    exact _root_.List.findSome?_eq_findSomeM?.symm

public theorem Array.findFinIdx?_congr : type_of% @_root_.Array.findFinIdx?_congr := by
  intro α p xs ys eq
  subst ys
  cases xs.findFinIdx? p <;> rfl

public theorem Array.findFinIdx?_eq_none_iff : type_of% @_root_.Array.findFinIdx?_eq_none_iff := by
  intro α xs p
  have missing : xs.findFinIdx? p = none ↔ xs.findIdx? p = none := by
    rw [Array.findIdx?_eq_map_findFinIdx?_val]
    exact Option.map_eq_none_iff.symm
  exact ⟨fun h x mem => Bool.eq_false_iff.mp (Array.findIdx?_eq_none_iff.mp (missing.mp h) x mem),
    fun h => missing.mpr (Array.findIdx?_eq_none_iff.mpr (fun x mem => Bool.eq_false_iff.mpr (h x mem)))⟩

public theorem Array.findFinIdx?_eq_some_iff : type_of% @_root_.Array.findFinIdx?_eq_some_iff := by
  intro α xs p i
  have atIndex : xs.findFinIdx? p = some i ↔ xs.findIdx? p = some i.val := by
    rw [Array.findIdx?_eq_map_findFinIdx?_val]
    exact (Option.map_inj_right (o' := some i) (f := Fin.val) (fun _ _ => Fin.eq_of_val_eq)).symm
  constructor
  · intro hit
    obtain ⟨_, here, before⟩ := Array.findIdx?_eq_some_iff_getElem.mp (atIndex.mp hit)
    exact ⟨here, fun j hj => before j.val hj⟩
  · rintro ⟨here, before⟩
    exact atIndex.mpr (Array.findIdx?_eq_some_iff_getElem.mpr
      ⟨i.isLt, here, fun j hj => before ⟨j, Nat.lt_trans hj i.isLt⟩ hj⟩)

public theorem Array.findIdx?_append : type_of% @_root_.Array.findIdx?_append := by
  intro α xs ys p
  cases xs with
  | mk as =>
    cases ys with
    | mk bs =>
      rw [List.append_toArray, List.findIdx?_toArray, List.findIdx?_toArray, List.findIdx?_toArray,
        List.size_toArray]
      exact List.findIdx?_append

public theorem List.head?_filter : type_of% @_root_.List.head?_filter := by
  intro α p xs
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.filter_cons, List.find?_cons]
    cases p x with
    | true => rfl
    | false => exact ih

public theorem List.find?_eq_bind_findIdx?_getElem? : type_of% @_root_.List.find?_eq_bind_findIdx?_getElem? := by
  intro α xs p
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.find?_cons, List.findIdx?_cons]
    cases h : p x with
    | true => rfl
    | false =>
      change xs.find? p = ((xs.findIdx? p).map Nat.succ).bind _
      rw [ih]
      cases xs.findIdx? p <;> rfl

public theorem Array.find?_eq_bind_findIdx?_getElem? : type_of% @_root_.Array.find?_eq_bind_findIdx?_getElem? := by
  intro α xs p
  cases xs with
  | mk xs =>
    rw [_root_.List.find?_toArray, _root_.List.findIdx?_toArray, _root_.List.find?_eq_bind_findIdx?_getElem?]
    cases xs.findIdx? p with
    | none => rfl
    | some i => exact List.getElem?_toArray.symm

private theorem findSomePointwise {xs : List α} {f g : α → Option β} (h : ∀ x, f x = g x) :
    xs.findSome? f = xs.findSome? g := by
  induction xs with
  | nil => rfl
  | cons x xs ih => rw [List.findSome?_cons, List.findSome?_cons, h]; cases g x <;> first | rfl | exact ih

public theorem Array.getElem?_zero_flatten : type_of% @_root_.Array.getElem?_zero_flatten := by
  intro α xss
  rw [← Array.getElem?_toList, Array.toList_flatten, ← List.head?_eq_getElem?, List.head?_flatten,
    List.findSome?_map, ← Array.findSome?_toList]
  apply findSomePointwise
  intro xs
  exact List.head?_eq_getElem?.trans Array.getElem?_toList

public theorem Array.getElem_zero_flatten.proof : type_of% @_root_.Array.getElem_zero_flatten.proof := by
  intro α xss h
  rw [← _root_.Array.getElem?_zero_flatten, _root_.Array.getElem?_eq_getElem h]
  rfl

public theorem Array.getElem_zero_flatten : type_of% @_root_.Array.getElem_zero_flatten := by
  intro α xss h
  apply Option.some.inj
  exact (_root_.Array.getElem?_eq_getElem h).symm.trans ((_root_.Array.getElem?_zero_flatten xss).trans (Option.some_get _).symm)

public theorem Array.find?_flatten : type_of% @_root_.Array.find?_flatten := by
  intro α xss p
  rw [← Array.find?_toList, Array.toList_flatten, List.find?_flatten, List.findSome?_map, ← Array.findSome?_toList]
  exact findSomePointwise (fun xs => _root_.Array.find?_toList (xs := xs))

public theorem Array.find?_flatMap : type_of% @_root_.Array.find?_flatMap := by
  intro α β xs f p
  rw [← Array.find?_toList, Array.toList_flatMap, List.find?_flatMap, ← Array.findSome?_toList]
  exact findSomePointwise (fun x => _root_.Array.find?_toList (xs := f x))

private theorem flipped {b : Bool} : (!b = true) ↔ ¬ (b = true) := by
  cases b <;> decide

public theorem Array.find?_flatten_eq_none_iff : type_of% @_root_.Array.find?_flatten_eq_none_iff := by
  intro α xss p
  rw [_root_.Array.find?_flatten, _root_.Array.findSome?_eq_none_iff]
  exact ⟨fun h a m y hy => flipped.mpr (_root_.Array.find?_eq_none.mp (h a m) y hy),
    fun h a m => _root_.Array.find?_eq_none.mpr (fun y hy => flipped.mp (h a m y hy))⟩

public theorem Array.find?_flatMap_eq_none_iff : type_of% @_root_.Array.find?_flatMap_eq_none_iff := by
  intro α β xs f p
  rw [_root_.Array.find?_flatMap, _root_.Array.findSome?_eq_none_iff]
  exact ⟨fun h a m y hy => flipped.mpr (_root_.Array.find?_eq_none.mp (h a m) y hy),
    fun h a m => _root_.Array.find?_eq_none.mpr (fun y hy => flipped.mp (h a m y hy))⟩

public theorem Array.findIdx_push : type_of% @_root_.Array.findIdx_push := by
  intro α xs a p
  rw [Array.push_eq_append, Array.findIdx_append, Array.findIdx_singleton]
  split
  · rfl
  · exact Nat.add_comm ..

public theorem Array.findIdx?_push : type_of% @_root_.Array.findIdx?_push := by
  intro α xs a p
  rw [Array.push_eq_append, Array.findIdx?_append, Array.findIdx?_singleton]
  cases p a <;> simp only [ite_true, Bool.false_eq_true, ite_false, Option.map_some, Option.map_none, Nat.zero_add]

public theorem Array.findIdx?_eq_guard_findIdx_lt : type_of% @_root_.Array.findIdx?_eq_guard_findIdx_lt := by
  intro α xs p
  cases hit : xs.findIdx? p with
  | none =>
    have eq := _root_.Array.findIdx?_eq_none_iff_findIdx_eq.mp hit
    rw [eq]; simp only [Option.guard, decide_eq_false (Nat.lt_irrefl _), Bool.false_eq_true, ite_false]
  | some i =>
    have ⟨hi, eq⟩ := _root_.Array.findIdx?_eq_some_iff_findIdx_eq.mp hit
    subst i
    simp only [Option.guard, decide_eq_true hi, ite_true]

public theorem Array.of_findIdx?_eq_some : type_of% @_root_.Array.of_findIdx?_eq_some := by
  intro i α xs p hit
  obtain ⟨hi, pass, _⟩ := _root_.Array.findIdx?_eq_some_iff_getElem.mp hit
  rw [Array.getElem?_eq_getElem hi]
  exact pass

public theorem Array.of_findIdx?_eq_none : type_of% @_root_.Array.of_findIdx?_eq_none := by
  intro α xs p empty i
  by_cases hi : i < xs.size
  · rw [Array.getElem?_eq_getElem hi]
    exact fun pass => Bool.noConfusion ((_root_.Array.findIdx?_eq_none_iff.mp empty _ (Array.getElem_mem hi)).symm.trans pass)
  · rw [Array.getElem?_eq_none (Nat.le_of_not_gt hi)]

public theorem List.findIdx?_take : type_of% @_root_.List.findIdx?_take := by
  intro α xs i p
  induction xs generalizing i with
  | nil => rw [List.take_nil]; rfl
  | cons x xs ih =>
    cases i with
    | zero => cases (x :: xs).findIdx? p with
      | none => rfl
      | some n => simp only [List.take_zero, List.findIdx?_nil, Option.bind_some, Option.guard, decide_eq_false (Nat.not_lt_zero n), Bool.false_eq_true, ite_false]
    | succ i =>
      rw [List.take_succ_cons, List.findIdx?_cons, List.findIdx?_cons]
      cases test : p x with
      | true => simp only [ite_true, Option.bind_some, Option.guard, decide_eq_true (Nat.zero_lt_succ i)]
      | false =>
        change (List.findIdx? p (xs.take i)).map Nat.succ = ((xs.findIdx? p).map Nat.succ).bind _
        rw [ih]
        cases xs.findIdx? p with
        | none => rfl
        | some n =>
          by_cases inside : n < i
          · have next := Nat.succ_lt_succ inside
            simp only [Option.bind_some, Option.map_some, Option.guard, decide_eq_true inside, decide_eq_true next, ite_true]
          · have outside : ¬ n.succ < i.succ := fun h => inside (Nat.lt_of_succ_lt_succ h)
            simp only [Option.bind_some, Option.map_some, Option.guard, decide_eq_false inside, decide_eq_false outside, Bool.false_eq_true, ite_false, Option.map_none]

public theorem Array.findIdx?_take : type_of% @_root_.Array.findIdx?_take := by
  intro α xs i p
  cases xs with
  | mk xs => rw [List.take_toArray, List.findIdx?_toArray, List.findIdx?_toArray]; exact List.findIdx?_take

public theorem Array.findFinIdx?_append : type_of% @_root_.Array.findFinIdx?_append := by
  intro α xs ys p
  apply (Option.map_inj_right (f := Fin.val) (fun _ _ => Fin.eq_of_val_eq)).mp
  rw [← Array.findIdx?_eq_map_findFinIdx?_val, Array.findIdx?_append,
    Array.findIdx?_eq_map_findFinIdx?_val, Array.findIdx?_eq_map_findFinIdx?_val]
  cases xs.findFinIdx? p <;> cases ys.findFinIdx? p <;> try rfl
  rename_i i
  exact congrArg some ((Nat.add_comm _ _).trans (_root_.Fin.val_natAdd xs.size i).symm)

public theorem Array.findFinIdx?_push : type_of% @_root_.Array.findFinIdx?_push := by
  intro α xs a p
  apply (Option.map_inj_right (f := Fin.val) (fun _ _ => Fin.eq_of_val_eq)).mp
  rw [← Array.findIdx?_eq_map_findFinIdx?_val, Array.findIdx?_push, Array.findIdx?_eq_map_findFinIdx?_val]
  cases xs.findFinIdx? p <;> cases p a <;> rfl

public theorem Array.findIdx?_eq_bind_find?_idxOf? : type_of% @_root_.Array.findIdx?_eq_bind_find?_idxOf? := by
  intro α _ _ xs p
  cases xs with
  | mk xs =>
    rw [List.findIdx?_toArray, List.find?_toArray, List.findIdx?_eq_bind_find?_idxOf?]
    cases xs.find? p with
    | none => rfl
    | some a => exact (List.idxOf?_toArray a xs).symm

public theorem Array.findFinIdx?_eq_bind_find?_finIdxOf? : type_of% @_root_.Array.findFinIdx?_eq_bind_find?_finIdxOf? := by
  intro α _ _ xs p
  apply (Option.map_inj_right (f := Fin.val) (fun _ _ => Fin.eq_of_val_eq)).mp
  rw [← Array.findIdx?_eq_map_findFinIdx?_val, _root_.Array.findIdx?_eq_bind_find?_idxOf?]
  cases xs.find? p with
  | none => rfl
  | some a => exact Array.idxOf?_eq_map_finIdxOf?_val

public theorem Array.findIdx_eq_getD_bind_find?_idxOf? : type_of% @_root_.Array.findIdx_eq_getD_bind_find?_idxOf? := by
  intros
  rw [_root_.Array.findIdx_eq_getD_findIdx?, _root_.Array.findIdx?_eq_bind_find?_idxOf?]

public theorem Array.find?_replicate_eq_none_iff : type_of% @_root_.Array.find?_replicate_eq_none_iff := by
  intros
  rw [← List.toArray_replicate, List.find?_toArray]
  exact _root_.List.find?_replicate_eq_none_iff

public theorem List.min_findIdx_findIdx : type_of% @_root_.List.min_findIdx_findIdx := by
  intro α xs p q
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.findIdx_cons, List.findIdx_cons, List.findIdx_cons]
    cases p x <;> cases q x <;> simp only [Bool.false_or, Bool.true_or, Bool.false_eq_true, ite_false, ite_true,
      Nat.zero_min, Nat.min_zero, Nat.add_min_add_right, ih]

public theorem Array.find?_filter : type_of% @_root_.Array.find?_filter := by
  intro α xs p q
  rw [← Array.find?_toList, Array.toList_filter, _root_.List.find?_filter, ← Array.find?_toList]

public theorem Array.findIdx?_eq_some_le_of_findIdx?_eq_some : type_of% @_root_.Array.findIdx?_eq_some_le_of_findIdx?_eq_some := by
  intro α xs p q implies i hit
  cases xs with
  | mk xs =>
    rw [List.findIdx?_toArray] at hit ⊢
    apply _root_.List.findIdx?_eq_some_le_of_findIdx?_eq_some _ hit
    exact fun x mem => implies x (List.mem_toArray.mpr mem)

public theorem Array.find?_flatten_eq_some_iff : type_of% @_root_.Array.find?_flatten_eq_some_iff := by
  intro α xss p a
  rw [Array.find?_flatten, Array.findSome?_eq_some_iff]
  constructor
  · rintro ⟨pre, row, post, eq, hit, absent⟩
    obtain ⟨ok, left, right, rfl, misses⟩ := Array.find?_eq_some_iff_append.mp hit
    exact ⟨ok, pre, left, right, post, eq,
      fun ys mem x hx => flipped.mpr (Array.find?_eq_none.mp (absent ys mem) x hx), misses⟩
  · rintro ⟨ok, pre, left, right, post, eq, misses, absent⟩
    exact ⟨pre, left.push a ++ right, post, eq,
      Array.find?_eq_some_iff_append.mpr ⟨ok, left, right, rfl, absent⟩,
      fun ys mem => Array.find?_eq_none.mpr (fun x hx => flipped.mp (misses ys mem x hx))⟩

public theorem List.findIdx?_eq_some_le_of_findIdx?_eq_some : type_of% @_root_.List.findIdx?_eq_some_le_of_findIdx?_eq_some := by
  intro α xs p q implies i hit
  obtain ⟨hi, eq⟩ := List.findIdx?_eq_some_iff_findIdx_eq.mp hit
  have le := Nat.le_trans (List.findIdx_le_findIdx implies) (Nat.le_of_eq eq)
  exact ⟨xs.findIdx q, le, List.findIdx?_eq_some_iff_findIdx_eq.mpr ⟨Nat.lt_of_le_of_lt le hi, rfl⟩⟩

private theorem mapSearch {xs : List α} {p q : α → Bool} (h : ∀ x, p x = q x) : xs.findIdx? p = xs.findIdx? q := by
  induction xs with
  | nil => rfl
  | cons x xs ih => rw [List.findIdx?_cons, List.findIdx?_cons, h]; cases q x <;> first | rfl | exact congrArg (Option.map Nat.succ) ih

public theorem Array.findIdx?_flatten : type_of% @_root_.Array.findIdx?_flatten := by
  intro α xss p
  cases xss using Array.array₂_induction with
  | of rows =>
    simp only [Array.flatten_toArray_map_toArray, List.findIdx?_toArray, List.findIdx?_flatten, List.findIdx?_map]
    rw [mapSearch (xs := rows) (q := (fun ys => ys.any p) ∘ List.toArray) (fun ys => (List.any_toArray (p := p) (l := ys)).symm)]
    cases rows.findIdx? ((fun ys => ys.any p) ∘ List.toArray) with
    | none => rfl
    | some i =>
      simp only [Option.map_some]
      have lengths := List.map_congr_left (l := rows.take i) (f := fun ys => ys.toArray.size) (g := List.length) (fun _ _ => List.size_toArray)
      simp only [List.take_toArray, List.map_toArray, List.sum_toArray, ← List.map_take,
        List.map_map, List.getElem?_toArray, List.getElem?_map, Function.comp_def, lengths]
      cases rows[i]? with
      | none => rfl
      | some row => simp only [Option.map_some, Option.getD_some, List.findIdx_toArray]

public theorem Array.binInsertM._proof_8 : type_of% (private_decl% @_root_.Array.binInsertM._proof_8) := by
  intro α lt xs k notEmpty notBefore
  have zero : 0 < xs.size := Nat.pos_of_ne_zero notEmpty
  change lt (xs[0]'zero) k = true
  cases h : lt (xs[0]'zero) k with
  | true => rfl
  | false => exact (notBefore (congrArg Bool.not h)).elim

private theorem accumulatedSize {as : List α} {bs : Array α} :
    (as.toArrayAux bs).size = as.length + bs.size := by
  induction as generalizing bs with
  | nil => exact (Nat.zero_add bs.size).symm
  | cons a as ih =>
    change (as.toArrayAux (bs.push a)).size = (as.length + 1) + bs.size
    rw [ih, Array.size_push, Nat.succ_add, Nat.add_succ]

public theorem List.size_toArrayAux {as : List α} {bs : Array α} :
    (as.toArrayAux bs).size = as.length + bs.size := accumulatedSize

public theorem List.of_toArrayAux_eq_toArrayAux :
    type_of% (private_decl% @_root_.List.of_toArrayAux_eq_toArrayAux) := by
  intro α as bs cs ds h sizes
  induction as generalizing bs cs ds with
  | nil =>
    cases bs with
    | nil => exact ⟨rfl, h⟩
    | cons b bs =>
      change cs = bs.toArrayAux (ds.push b) at h
      have sz := congrArg Array.size h
      rw [accumulatedSize, Array.size_push, sizes] at sz
      exact (Nat.not_lt_of_ge (Nat.le_of_eq sz.symm)
        (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_add_left _ _))).elim
  | cons a as ih =>
    cases bs with
    | nil =>
      change as.toArrayAux (cs.push a) = ds at h
      have sz := congrArg Array.size h
      rw [accumulatedSize, Array.size_push, ← sizes] at sz
      exact (Nat.not_lt_of_ge (Nat.le_of_eq sz)
        (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_add_left _ _))).elim
    | cons b bs =>
      have step := ih (bs := bs) (cs := cs.push a) (ds := ds.push b) h
        (by rw [Array.size_push, Array.size_push, sizes])
      obtain ⟨tails, pushes⟩ := step
      obtain ⟨arrays, heads⟩ := Array.of_push_eq_push pushes
      cases heads
      exact ⟨congrArg (a :: ·) tails, arrays⟩

end OmegaChecks.InitPort.Alternatives
