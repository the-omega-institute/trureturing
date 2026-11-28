module
public import Init.Data.ByteArray.Lemmas
import Init.Data.Array.Extract

namespace OmegaChecks.InitPort.Alternatives

public theorem Nat.min_zero (a : Nat) : min a 0 = 0 := Nat.min_eq_right (Nat.zero_le a)

public theorem Nat.zero_min (a : Nat) : min 0 a = 0 := Nat.min_eq_left (Nat.zero_le a)

public theorem Nat.add_min_add_left (a b c : Nat) : min (a + b) (a + c) = a + min b c := by
  cases Nat.le_total b c with
  | inl h => rw [Nat.min_eq_left (Nat.add_le_add_left h a), Nat.min_eq_left h]
  | inr h => rw [Nat.min_eq_right (Nat.add_le_add_left h a), Nat.min_eq_right h]

public theorem Nat.add_min_add_right (a b c : Nat) : min (a + c) (b + c) = min a b + c := by
  cases Nat.le_total a b with
  | inl h => rw [Nat.min_eq_left (Nat.add_le_add_right h c), Nat.min_eq_left h]
  | inr h => rw [Nat.min_eq_right (Nat.add_le_add_right h c), Nat.min_eq_right h]

public theorem Nat.add_max_add_left (a b c : Nat) : max (a + b) (a + c) = a + max b c := by
  cases Nat.le_total b c with
  | inl h => rw [Nat.max_eq_right (Nat.add_le_add_left h a), Nat.max_eq_right h]
  | inr h => rw [Nat.max_eq_left (Nat.add_le_add_left h a), Nat.max_eq_left h]

public theorem Nat.add_max_add_right (a b c : Nat) : max (a + c) (b + c) = max a b + c := by
  cases Nat.le_total a b with
  | inl h => rw [Nat.max_eq_right (Nat.add_le_add_right h c), Nat.max_eq_right h]
  | inr h => rw [Nat.max_eq_left (Nat.add_le_add_right h c), Nat.max_eq_left h]

public theorem Nat.min_assoc (a b c : Nat) : min (min a b) c = min a (min b c) :=
  Nat.le_antisymm
    (Nat.le_min.mpr ⟨Nat.le_trans (Nat.min_le_left ..) (Nat.min_le_left ..),
      Nat.le_min.mpr ⟨Nat.le_trans (Nat.min_le_left ..) (Nat.min_le_right ..), Nat.min_le_right ..⟩⟩)
    (Nat.le_min.mpr ⟨Nat.le_min.mpr ⟨Nat.min_le_left ..,
      Nat.le_trans (Nat.min_le_right ..) (Nat.min_le_left ..)⟩,
      Nat.le_trans (Nat.min_le_right ..) (Nat.min_le_right ..)⟩)

public theorem Nat.sub_min_sub_right (a b c : Nat) :
    min (a - c) (b - c) = min a b - c := by
  cases Nat.le_total a b with
  | inl h => rw [Nat.min_eq_left (Nat.sub_le_sub_right h c), Nat.min_eq_left h]
  | inr h => rw [Nat.min_eq_right (Nat.sub_le_sub_right h c), Nat.min_eq_right h]

public theorem List.ext_getElem : type_of% @_root_.List.ext_getElem := by
  intro α xs ys lengths atIndex
  apply List.ext_getElem?
  intro i
  by_cases hx : i < xs.length
  · have hy : i < ys.length := lengths ▸ hx
    exact (List.getElem?_eq_getElem hx).trans
      ((congrArg some (atIndex i hx hy)).trans (List.getElem?_eq_getElem hy).symm)
  · have hx := Nat.le_of_not_lt hx
    have hy : ys.length ≤ i := lengths ▸ hx
    exact (List.getElem?_eq_none hx).trans (List.getElem?_eq_none hy).symm

private theorem extractLoopList {α : Type u} (xs : _root_.Array α) (count start : Nat)
    (acc : _root_.Array α) :
    (_root_.Array.extract.loop xs count start acc).toList =
      acc.toList ++ (xs.toList.drop start).take count := by
  induction count generalizing start acc with
  | zero => rw [Array.extract_loop_zero, List.take_zero, List.append_nil]
  | succ count ih =>
    by_cases h : start < xs.size
    · rw [Array.extract_loop_succ h, ih, Array.toList_push, List.append_assoc,
        List.drop_eq_getElem_cons (l := xs.toList) h]
      rfl
    · have past : xs.toList.length ≤ start := Nat.le_of_not_lt h
      rw [Array.extract_loop_of_ge past, List.drop_eq_nil_of_le past, List.take_nil, List.append_nil]

public theorem Array.toList_extract : type_of% @_root_.Array.toList_extract := by
  intro α xs start stop
  unfold _root_.Array.extract _root_.List.extract
  rw [extractLoopList, Array.emptyWithCapacity_eq, Array.toList_empty, List.nil_append]
  change (xs.toList.drop start).take (min stop xs.size - start) = _
  by_cases h : stop ≤ xs.size
  · rw [Nat.min_eq_left h]
  · have past := Nat.le_of_not_le h
    rw [Nat.min_eq_right past]
    have len : (xs.toList.drop start).length = xs.size - start := List.length_drop
    exact (List.take_of_length_le (Nat.le_of_eq len)).trans
      (List.take_of_length_le (Nat.le_trans (Nat.le_of_eq len) (Nat.sub_le_sub_right past start))).symm

public theorem Array.getElem_extract_loop_ge : type_of% @_root_.Array.getElem_extract_loop_ge := by
  intro α i xs ys size start hge h
  have eqList := List.getElem_of_eq (extractLoopList xs size start ys) h
  apply eqList.trans
  rw [List.getElem_append_right hge, List.getElem_take, List.getElem_drop]
  apply getElem_congr_idx
  exact (Nat.add_sub_assoc hge start).symm

public theorem Array.getElem_extract : type_of% @_root_.Array.getElem_extract := by
  intro α i xs start stop h
  have same := List.getElem_of_eq (Array.toList_extract (xs := xs) (start := start) (stop := stop)) h
  exact same.trans (List.getElem_take.trans List.getElem_drop)

public theorem Array.push_eq_append : type_of% @_root_.Array.push_eq_append := by
  intro α a xs
  exact Array.ext' (Array.toList_push.trans Array.toList_append.symm)

public theorem Array.append_singleton : type_of% @_root_.Array.append_singleton := by
  intro α a xs
  exact Array.push_eq_append.symm

public theorem Array.push_eq_append_singleton {α : Type u} {xs : _root_.Array α} {x : α} :
    xs.push x = xs ++ #[x] := Array.push_eq_append

public theorem Array.extract_size : type_of% @_root_.Array.extract_size := by
  intro α xs
  apply Array.ext'
  exact Array.toList_extract.trans (show (xs.toList.drop 0).take (xs.size - 0) = xs.toList from
    @List.take_length α xs.toList)

public theorem Array.extract_eq_empty_of_le :
    type_of% @_root_.Array.extract_eq_empty_of_le := by
  intro α stop xs start h
  apply Array.eq_empty_of_size_eq_zero
  exact Array.size_extract.trans (Nat.sub_eq_zero_of_le h)

public theorem ByteArray.data_extract :
    type_of% @_root_.ByteArray.data_extract := by
  intro a b e
  change #[] ++ a.data.extract b (b + (e - b)) ++ (#[] : Array UInt8).extract _ _ = a.data.extract b e
  rw [Array.extract_empty, Array.append_empty, Array.empty_append]
  cases Nat.le_total b e with
  | inl h => rw [Nat.add_comm, Nat.sub_add_cancel h]
  | inr h =>
    rw [Nat.sub_eq_zero_of_le h, Nat.add_zero, Array.extract_eq_empty_of_le (Nat.min_le_left ..),
      Array.extract_eq_empty_of_le (Nat.le_trans (Nat.min_le_left ..) h)]

public theorem ByteArray.extract_same :
    type_of% @_root_.ByteArray.extract_same := by
  intro b i
  apply ByteArray.ext
  exact ByteArray.data_extract.trans (Array.extract_eq_empty_of_le (Nat.min_le_left ..))

public theorem ByteArray.extract_zero_size : type_of% @_root_.ByteArray.extract_zero_size := by
  intro b
  apply ByteArray.ext
  exact ByteArray.data_extract.trans Array.extract_size

public theorem ByteArray.extract_eq_empty_iff : type_of% @_root_.ByteArray.extract_eq_empty_iff := by
  intro b i j
  exact Iff.trans ByteArray.size_eq_zero_iff.symm
    ⟨fun h => Nat.le_of_sub_eq_zero (ByteArray.size_extract.symm.trans h),
      fun h => ByteArray.size_extract.trans (Nat.sub_eq_zero_of_le h)⟩

public theorem ByteArray.extract_append_eq_right : type_of% @_root_.ByteArray.extract_append_eq_right := by
  intro a b i j hi hj
  subst i
  subst j
  apply ByteArray.ext
  apply Array.ext'
  rw [ByteArray.data_extract, ByteArray.data_append, Array.toList_extract, Array.toList_append]
  change ((a.data.toList ++ b.data.toList).drop a.data.toList.length).take
    (a.size + b.size - a.size) = b.data.toList
  rw [List.drop_left, Nat.add_sub_cancel_left]
  exact List.take_length

public theorem ByteArray.extract_append_eq_left : type_of% @_root_.ByteArray.extract_append_eq_left := by
  intro a b i hi
  subst i
  apply ByteArray.ext
  apply Array.ext'
  rw [ByteArray.data_extract, ByteArray.data_append, Array.toList_extract, Array.toList_append]
  exact List.take_left

private theorem sliceAppend (xs ys : List α) (i j : Nat) :
    ((xs ++ ys).drop i).take (j - i) = (xs.drop i).take (j - i) ++
      (ys.drop (i - xs.length)).take ((j - xs.length) - (i - xs.length)) := by
  induction xs generalizing i j with
  | nil => simp only [List.nil_append, List.drop_nil, List.take_nil, List.length_nil, Nat.sub_zero]
  | cons x xs ih =>
    cases i <;> cases j <;> simp only [List.cons_append, List.drop_zero, List.drop_succ_cons, List.take_zero,
      List.take_succ_cons, List.length_cons, Nat.zero_sub, Nat.sub_zero, Nat.succ_sub_succ, List.nil_append]
    · rename_i n
      apply congrArg (List.cons x)
      simpa only [Nat.sub_zero, Nat.zero_sub, List.drop_zero] using ih 0 n
    · exact ih _ _

public theorem Array.extract_append : type_of% @_root_.Array.extract_append := by
  intro α as bs i j
  apply _root_.Array.ext'
  rw [_root_.Array.toList_extract, _root_.Array.toList_append, _root_.Array.toList_append,
    _root_.Array.toList_extract, _root_.Array.toList_extract]
  exact sliceAppend as.toList bs.toList i j

public theorem ByteArray.extract_append : type_of% @_root_.ByteArray.extract_append := by
  intro as bs i j
  apply _root_.ByteArray.ext
  rw [_root_.ByteArray.data_extract, _root_.ByteArray.data_append, _root_.ByteArray.data_append,
    _root_.ByteArray.data_extract, _root_.ByteArray.data_extract]
  exact _root_.Array.extract_append

public theorem List.takeWhile_filterMap : type_of% @_root_.List.takeWhile_filterMap := by
  intro α β f p xs
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases h : f x with
    | none => simpa only [List.filterMap_cons, h, List.takeWhile_cons, Option.all_none, ite_true] using ih
    | some y => cases e : p y <;>
        simp only [List.filterMap_cons, h, List.takeWhile_cons, Option.all_some, e, Bool.false_eq_true,
          ite_true, ite_false, List.filterMap_nil, ih]

public theorem List.dropWhile_filterMap : type_of% @_root_.List.dropWhile_filterMap := by
  intro α β f p xs
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases h : f x with
    | none => simpa only [List.filterMap_cons, h, List.dropWhile_cons, Option.all_none, ite_true] using ih
    | some y => cases e : p y <;>
        simp only [List.filterMap_cons, h, List.dropWhile_cons, Option.all_some, e, Bool.false_eq_true,
          ite_true, ite_false, ih]

public theorem List.takeWhile_filter : type_of% @_root_.List.takeWhile_filter := by
  intro α p q xs
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases hp : p x <;> cases hq : q x <;>
      simp only [List.filter_cons, List.takeWhile_cons, hp, hq, Bool.not_true, Bool.not_false,
        Bool.true_or, Bool.false_or, Bool.false_eq_true, ite_true, ite_false, List.filter_nil, ih]

public theorem List.dropWhile_filter : type_of% @_root_.List.dropWhile_filter := by
  intro α p q xs
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases hp : p x <;> cases hq : q x <;>
      simp only [List.filter_cons, List.dropWhile_cons, hp, hq, Bool.not_true, Bool.not_false,
        Bool.true_or, Bool.false_or, Bool.false_eq_true, ite_true, ite_false, ih]

public theorem List.head_takeWhile : type_of% @_root_.List.head_takeWhile := by
  intro α p xs present
  cases xs with
  | nil => exact (present rfl).elim
  | cons x xs =>
    cases head : p x with
    | false => exact (present (by simp only [List.takeWhile_cons, head, Bool.false_eq_true, ite_false])).elim
    | true => simp only [List.takeWhile_cons, head, ite_true, List.head_cons]

public theorem List.filter_replicate : type_of% @_root_.List.filter_replicate := by
  intro n α a p
  cases test : p a with
  | true =>
    induction n with
    | zero => rfl
    | succ n ih => rw [List.replicate_succ, List.filter_cons, ite_eq_left test]; exact congrArg (List.cons a) ih
  | false =>
    have absent : ¬ p a := fun yes => Bool.noConfusion (test.symm.trans yes)
    induction n with
    | zero => rfl
    | succ n ih => rw [List.replicate_succ, List.filter_cons, ite_eq_right absent]; exact ih

public theorem List.takeWhile_replicate : type_of% @_root_.List.takeWhile_replicate := by
  intro α n a p
  cases test : p a with
  | true =>
    induction n with
    | zero => rfl
    | succ n ih => rw [List.replicate_succ, List.takeWhile_cons, ite_eq_left test]; exact congrArg (List.cons a) ih
  | false =>
    have absent : ¬ p a := fun yes => Bool.noConfusion (test.symm.trans yes)
    cases n with
    | zero => rfl
    | succ n => rw [List.replicate_succ, List.takeWhile_cons, ite_eq_right absent]; rfl

public theorem List.dropWhile_replicate : type_of% @_root_.List.dropWhile_replicate := by
  intro α n a p
  cases test : p a with
  | true =>
    induction n with
    | zero => rfl
    | succ n ih => rw [List.replicate_succ, List.dropWhile_cons, ite_eq_left test]; exact ih
  | false =>
    have absent : ¬ p a := fun yes => Bool.noConfusion (test.symm.trans yes)
    cases n with
    | zero => rfl
    | succ n => rw [List.replicate_succ, List.dropWhile_cons, ite_eq_right absent]; rfl

public theorem List.takeWhile_replicate_eq_filter : type_of% @_root_.List.takeWhile_replicate_eq_filter := by
  intro α n a p
  rw [List.takeWhile_replicate, List.filter_replicate]

public theorem List.dropWhile_replicate_eq_filter_not : type_of% @_root_.List.dropWhile_replicate_eq_filter_not := by
  intro α n a p
  rw [List.dropWhile_replicate, List.filter_replicate]
  cases p a <;> rfl

public theorem List.replace_takeWhile : type_of% @_root_.List.replace_takeWhile := by
  intro α a b _ _ xs p hp
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    by_cases eq : a == x
    · have same := eq_of_beq eq
      subst x
      cases test : p a <;> simp only [List.replace_cons, List.takeWhile_cons, beq_self_eq_true, ite_true,
        ← hp, test, Bool.false_eq_true, ite_false, List.replace_nil]
    · cases test : p x <;> simp only [List.replace_cons, List.takeWhile_cons, eq, test, ite_false, ite_true,
        Bool.false_eq_true, List.replace_nil, ih]

public theorem Array.getElem?_extract_of_succ : type_of% @_root_.Array.getElem?_extract_of_succ := by
  intro α as j
  rw [Array.getElem?_extract, Nat.sub_zero, Nat.zero_add]
  by_cases inside : j < as.size
  · exact ite_eq_left (Nat.lt_min.mpr ⟨Nat.lt_succ_self _, inside⟩)
  · rw [ite_eq_right (fun lt => inside (Nat.lt_of_lt_of_le lt (Nat.min_le_right ..)))]
    exact (Array.getElem?_eq_none (Nat.le_of_not_gt inside)).symm

public theorem Array.popWhile_replicate : type_of% @_root_.Array.popWhile_replicate := by
  intro α n a p
  rw [Array.popWhile_replicate_eq_filter_not, Array.filter_replicate Array.size_replicate]
  cases p a <;> rfl

public theorem Array.extract_push : type_of% @_root_.Array.extract_push := by
  intro α as b start stop
  rw [_root_.Array.push_eq_append, _root_.Array.extract_append]
  by_cases before : stop ≤ as.size
  · rw [ite_eq_left before, Nat.sub_eq_zero_of_le before,
      Array.extract_empty_of_stop_le_start (Nat.zero_le _), Array.append_empty]
  · have past := Nat.lt_of_not_ge before
    rw [ite_eq_right before, Array.extract_of_size_lt past]
    by_cases begin : start ≤ as.size
    · have full : #[b].size ≤ stop - as.size := Nat.sub_pos_of_lt past
      rw [ite_eq_left begin, Nat.sub_eq_zero_of_le begin, Array.extract_eq_self_of_le full,
        _root_.Array.push_eq_append]
    · have skip : #[b].size ≤ start - as.size := Nat.sub_pos_of_lt (Nat.lt_of_not_ge begin)
      rw [ite_eq_right begin, Array.extract_empty_of_size_le_start skip,
        Array.extract_empty_of_size_le_start (Nat.le_of_not_ge begin), Array.append_empty]

public theorem Array.extract_set : type_of% @_root_.Array.extract_set := by
  intro α as i j k valid a
  by_cases before : k < i
  · rw [dite_eq_left before]
    apply Array.ext
    · simp only [Array.size_extract, Array.size_set]
    · intro t h₁ h₂
      rw [Array.getElem_extract, Array.getElem_extract, Array.getElem_set_ne]
      omega
  · rw [dite_eq_right before]
    by_cases inside : k < min j as.size
    · rw [dite_eq_left inside]
      have bound : k - i < (as.extract i j).size := by rw [Array.size_extract]; omega
      have index : i + (k - i) = k := Nat.add_sub_cancel' (Nat.le_of_not_gt before)
      rw [Array.set_extract bound]
      congr 1
      simp only [index]
    · rw [dite_eq_right inside]
      apply Array.ext
      · simp only [Array.size_extract, Array.size_set]
      · intro t h₁ h₂
        rw [Array.getElem_extract, Array.getElem_extract, Array.getElem_set_ne]
        rw [Array.size_extract] at h₂
        omega

end OmegaChecks.InitPort.Alternatives
