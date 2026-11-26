module
import all Init.Data.Array.Sort.Basic
import all Init.Data.Array.Sort.Lemmas
import all Init.Data.Slice.Array.Lemmas
import all Init.Data.List.Sort.Lemmas
import all Init.Data.Slice.List.Lemmas
import all Init.Data.Array.Lemmas

/-! Merge the two subarray heads according to the supplied comparison. -/
namespace OmegaChecks.InitPort.Alternatives

private theorem splitHead (s : Subarray α) (h : 0 < s.size) :
    s.toList = s[0] :: (s.drop 1).toList := by
  have hl : 0 < s.toList.length := _root_.Subarray.length_toList.symm ▸ h
  rw [_root_.Subarray.toList_drop, _root_.Subarray.getElem_eq_getElem_toList]
  exact List.drop_eq_getElem_cons hl

private theorem leftHead (le : α → α → Bool) (xs ys : Subarray α)
    (hx : 0 < xs.size) (hy : 0 < ys.size) (h : le xs[0] ys[0]) :
    List.merge xs.toList ys.toList le = xs[0] :: List.merge (xs.drop 1).toList ys.toList le := by
  conv => lhs; rw [splitHead xs hx, splitHead ys hy, List.cons_merge_cons_pos le _ _ h]
  rw [← splitHead ys hy]

private theorem rightHead (le : α → α → Bool) (xs ys : Subarray α)
    (hx : 0 < xs.size) (hy : 0 < ys.size) (h : ¬ le xs[0] ys[0]) :
    List.merge xs.toList ys.toList le = ys[0] :: List.merge xs.toList (ys.drop 1).toList le := by
  conv => lhs; rw [splitHead xs hx, splitHead ys hy, List.cons_merge_cons_neg le _ _ h]
  rw [← splitHead xs hx]

private theorem dropLast (s : Subarray α) (h : ¬ 1 < s.size) : (s.drop 1).toList = [] := by
  rw [_root_.Subarray.toList_drop]
  exact List.drop_eq_nil_of_le (_root_.Subarray.length_toList.symm ▸ Nat.le_of_not_lt h)

private theorem pushAppend (acc : Array α) (a : α) (xs : List α) :
    (acc.push a).toList ++ xs = acc.toList ++ (a :: xs) :=
  (congrArg (· ++ xs) _root_.Array.toList_push).trans (List.append_assoc ..)

private theorem collectTail (xs : Subarray α) (acc : Array α) :
    (xs.foldl (fun out y => out.push y) acc).toList = acc.toList ++ xs.toList := by
  rw [← _root_.Subarray.foldl_toList, List.foldl_push_eq_append', _root_.Array.toList_append]

public theorem Array.MergeSort.merge.go_eq_listMerge :
    type_of% (private_decl% @_root_.Array.MergeSort.merge.go_eq_listMerge) := by
  intro α xs ys hxs hys le acc
  fun_induction _root_.Array.MergeSort.Internal.merge.go le xs ys hxs hys acc
  · rename_i xs ys hx hy acc x y chooseLeft _ ih
    rw [leftHead le xs ys hx hy chooseLeft]
    exact ih.trans (pushAppend ..)
  · rename_i xs ys hx hy acc x y chooseLeft last
    rw [leftHead le xs ys hx hy chooseLeft, dropLast xs last, List.nil_merge]
    exact (collectTail ys (acc.push x)).trans (pushAppend ..)
  · rename_i xs ys hx hy acc x y chooseRight _ ih
    rw [rightHead le xs ys hx hy chooseRight]
    exact ih.trans (pushAppend ..)
  · rename_i xs ys hx hy acc x y chooseRight last
    rw [rightHead le xs ys hx hy chooseRight, dropLast ys last, List.merge_right]
    exact (collectTail xs (acc.push y)).trans (pushAppend ..)

public theorem Subarray.toList_mergeSort : type_of% @_root_.Subarray.toList_mergeSort := by
  intro α xs le
  fun_induction _root_.Subarray.mergeSort xs le
  · rename_i s h cut left right ihLeft ihRight
    rw [_root_.Array.MergeSort.merge_eq_listMerge, ihLeft, ihRight]
    conv => rhs; rw [_root_.List.mergeSort_eq_merge_mkSlice, _root_.Subarray.length_toList, ite_eq_left h]
    rw [_root_.List.toList_mkSlice_rio, _root_.List.toList_mkSlice_rci,
      _root_.Subarray.toList_mkSlice_rio, _root_.Subarray.toList_mkSlice_rci]
  · rename_i s h
    rw [_root_.List.mergeSort_eq_merge_mkSlice, _root_.Subarray.length_toList, ite_eq_right h]
    exact _root_.Subarray.toList_toArray

public theorem Array.mergeSort_zipIdx : type_of% @_root_.Array.mergeSort_zipIdx := by
  intro α le xs
  apply _root_.Array.ext'
  rw [_root_.Array.toList_map, _root_.Array.toList_mergeSort, _root_.Array.toList_map,
    _root_.Array.toList_zipIdx, _root_.Array.toList_mergeSort]
  change (((xs.toList.zipIdx.map id).mergeSort (List.zipIdxLE le)).map Prod.fst) = _
  rw [List.map_id]
  exact List.mergeSort_zipIdx

end OmegaChecks.InitPort.Alternatives
