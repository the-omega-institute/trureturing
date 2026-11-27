module
public import Init.Data.List.Sort.Impl
public import Init.Data.List.Sort.Lemmas
import all Init.Data.List.Sort.Lemmas
import all Init.Data.List.Sort.Basic

/-! Length, membership and stability of the comparison used by merge sort. -/
namespace OmegaChecks.InitPort.Alternatives

public theorem List.length_merge : type_of% @_root_.List.length_merge := by
  intros
  exact (_root_.List.merge_perm_append _).length_eq.trans _root_.List.length_append

public theorem List.mem_merge : type_of% @_root_.List.mem_merge := by
  intros
  exact (_root_.List.merge_perm_append _).mem_iff.trans _root_.List.mem_append

private theorem zipIdxSpec {α : Type u} {le : α → α → Bool} {a b : α × Nat} :
    _root_.List.zipIdxLE le a b ↔ le a.1 b.1 ∧ (le b.1 a.1 → a.2 ≤ b.2) := by
  unfold _root_.List.zipIdxLE
  by_cases ab : le a.1 b.1
  · rw [ite_eq_left ab]
    by_cases ba : le b.1 a.1
    · rw [ite_eq_left ba]
      exact ⟨fun yes => ⟨ab, fun _ => of_decide_eq_true yes⟩,
        fun ⟨_, order⟩ => decide_eq_true (order ba)⟩
    · rw [ite_eq_right ba]
      exact ⟨fun _ => ⟨ab, fun h => (ba h).elim⟩, fun _ => rfl⟩
  · rw [ite_eq_right ab]
    exact ⟨(fun h => nomatch h), fun h => (ab h.1).elim⟩

public theorem List.zipIdxLE_trans : type_of% @_root_.List.zipIdxLE_trans := by
  intro α le trans a b c hab hbc
  obtain ⟨ab, iab⟩ := zipIdxSpec.mp hab
  obtain ⟨bc, ibc⟩ := zipIdxSpec.mp hbc
  exact zipIdxSpec.mpr ⟨trans _ _ _ ab bc, fun ca =>
    Nat.le_trans (iab (trans _ _ _ bc ca)) (ibc (trans _ _ _ ca ab))⟩

public theorem List.zipIdxLE_total : type_of% @_root_.List.zipIdxLE_total := by
  intro α le total a b
  apply Bool.or_eq_true_iff.mpr
  by_cases ab : le a.1 b.1
  · by_cases ba : le b.1 a.1
    · obtain (h | h) := Nat.le_total a.2 b.2
      · exact .inl (zipIdxSpec.mpr ⟨ab, fun _ => h⟩)
      · exact .inr (zipIdxSpec.mpr ⟨ba, fun _ => h⟩)
    · exact .inl (zipIdxSpec.mpr ⟨ab, fun h => (ba h).elim⟩)
  · have ba := (Bool.or_eq_true_iff.mp (total a.1 b.1)).resolve_left ab
    exact .inr (zipIdxSpec.mpr ⟨ba, fun h => (ab h).elim⟩)

public theorem List.pairwise_merge : type_of% @_root_.List.pairwise_merge := by
  intro α le trans total xs ys px py
  induction xs generalizing ys with
  | nil => rw [_root_.List.nil_merge]; exact py
  | cons x xs ih =>
    induction ys with
    | nil => rw [_root_.List.merge_right]; exact px
    | cons y ys iy =>
      obtain ⟨headX, tailX⟩ := _root_.List.pairwise_cons.mp px
      obtain ⟨headY, tailY⟩ := _root_.List.pairwise_cons.mp py
      by_cases h : le x y
      · rw [_root_.List.cons_merge_cons_pos le _ _ h]
        refine .cons ?_ (ih _ tailX py)
        intro z mem
        obtain (m | m) := List.mem_merge.mp mem
        · exact headX z m
        · cases m with
          | head => exact h
          | tail _ m => exact trans _ _ _ h (headY z m)
      · rw [_root_.List.cons_merge_cons_neg le _ _ h]
        have yx := (Bool.or_eq_true_iff.mp (total x y)).resolve_left h
        refine .cons ?_ (iy tailY)
        intro z mem
        obtain (m | m) := List.mem_merge.mp mem
        · cases m with
          | head => exact yx
          | tail _ m => exact trans _ _ _ yx (headX z m)
        · exact headY z m

open _root_.List.MergeSort.Internal in
public theorem List.MergeSort.Internal.splitInTwo_cons_cons_zipIdx_fst :
    type_of% @_root_.List.MergeSort.Internal.splitInTwo_cons_cons_zipIdx_fst := by
  intro α a b i xs
  have takeZip (n : Nat) (ys : _root_.List α) (j : Nat) :
      (ys.zipIdx j).take n = (ys.take n).zipIdx j := by
    induction n generalizing ys j with
    | zero => rfl
    | succ n ih =>
      cases ys with
      | nil => rfl
      | cons y ys => exact congrArg ((y, j) :: ·) (ih ys (j + 1))
  rw [splitInTwo_fst, splitInTwo_fst]
  change ((a :: b :: xs).zipIdx i).take _ = ((a :: b :: xs).take _).zipIdx i
  simp only [_root_.List.length_cons, _root_.List.length_zipIdx]
  exact takeZip _ _ _

open _root_.List.MergeSort.Internal in
public theorem List.MergeSort.Internal.splitInTwo_cons_cons_zipIdx_snd :
    type_of% @_root_.List.MergeSort.Internal.splitInTwo_cons_cons_zipIdx_snd := by
  intro α a b i xs
  have dropZip (n : Nat) (ys : _root_.List α) (j : Nat) :
      (ys.zipIdx j).drop n = (ys.drop n).zipIdx (j + n) := by
    induction n generalizing ys j with
    | zero => rfl
    | succ n ih =>
      cases ys with
      | nil => rfl
      | cons y ys =>
        change (ys.zipIdx (j+1)).drop n = (ys.drop n).zipIdx (j + (n+1))
        rw [ih, Nat.succ_add, Nat.add_succ]
  rw [splitInTwo_snd, splitInTwo_snd]
  change ((a :: b :: xs).zipIdx i).drop _ = ((a :: b :: xs).drop _).zipIdx _
  simp only [_root_.List.length_cons, _root_.List.length_zipIdx]
  exact dropZip _ _ _

open _root_.List _root_.List.MergeSort.Internal in
public theorem List.mergeSort_append : type_of% @_root_.List.mergeSort_append := by
  intro α le xs ys hlo hhi
  cases xs with
  | nil =>
    obtain rfl := length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hlo)
    rw [nil_append, mergeSort_nil, nil_merge]
  | cons a xs =>
    cases xs with
    | nil =>
      cases ys with
      | nil => rw [append_nil, mergeSort_nil, merge_right]
      | cons b ys =>
        have z : ys.length ≤ 0 := Nat.le_of_succ_le_succ hlo
        obtain rfl := length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero z)
        rw [mergeSort_singleton, mergeSort_singleton]
        rw [singleton_append, _root_.List.mergeSort, splitInTwo_fst, splitInTwo_snd]
        simp only [length_cons, length_nil]
        change merge (mergeSort (take ((2+1)/2) [a,b]) le)
          (mergeSort (drop ((2+1)/2) [a,b]) le) le = _
        rw [show (2+1)/2 = 1 from by decide]
        change merge (mergeSort [a] le) (mergeSort [b] le) le = _
        rw [mergeSort_singleton, mergeSort_singleton]
    | cons b xs =>
      rw [cons_append, cons_append, _root_.List.mergeSort, splitInTwo_fst, splitInTwo_snd]
      have cut : (((a :: b :: xs) ++ ys).length + 1) / 2 = (a :: b :: xs).length := by
        simp only [length_cons] at hlo hhi
        simp only [length_append, length_cons]
        omega
      change merge (mergeSort (take _ ((a :: b :: xs) ++ ys)) le)
        (mergeSort (drop _ ((a :: b :: xs) ++ ys)) le) le = _
      rw [show ((a :: b :: (xs ++ ys)).length + 1) / 2 = (a :: b :: xs).length from cut,
        take_left, drop_left]

open _root_.List in
public theorem List.mergeSort_cons : type_of% @_root_.List.mergeSort_cons := by
  intro α le trans total a xs
  let order := zipIdxLE le
  have pivot : (a, 0) ∈ mergeSort ((a :: xs).zipIdx) order :=
    mem_mergeSort.mpr mem_cons_self
  obtain ⟨left, right, split⟩ := append_of_mem pivot
  have sorted := pairwise_mergeSort (List.zipIdxLE_trans trans) (List.zipIdxLE_total total) ((a :: xs).zipIdx)
  have perm := mergeSort_perm ((a :: xs).zipIdx) order
  change (mergeSort ((a :: xs).zipIdx) order).Pairwise _ at sorted
  rw [split] at perm sorted
  have tailPerm : mergeSort (xs.zipIdx 1) order ~ left ++ right :=
    (mergeSort_perm _ _).trans (perm.symm.trans perm_middle).cons_inv
  refine ⟨left.map Prod.fst, right.map Prod.fst, ?_, ?_, ?_⟩
  · rw [← mergeSort_zipIdx, split, map_append, map_cons]
  · rw [← mergeSort_zipIdx.go 1, ← map_append]
    apply congrArg (map Prod.fst)
    apply Perm.eq_of_pairwise (le := fun x y => order x y = true) _ _ _ tailPerm
    · intro ⟨x, i⟩ ⟨y, j⟩ hx hy xy yx
      have mx := mem_mergeSort.mp hx
      have my := mem_mergeSort.mp (tailPerm.mem_iff.mpr hy)
      have hxy := zipIdxSpec.mp xy
      have hyx := zipIdxSpec.mp yx
      cases Nat.le_antisymm (hxy.2 hyx.1) (hyx.2 hxy.1)
      have eqxy := (mem_zipIdx mx).2.2.trans (mem_zipIdx my).2.2.symm
      exact congrArg (fun z => (z, i)) eqxy
    · exact pairwise_mergeSort (List.zipIdxLE_trans trans) (List.zipIdxLE_total total) _
    · exact sorted.sublist ((sublist_cons_self (a, 0) right).append_left left)
  · intro b hb
    obtain ⟨⟨v, j⟩, hm, rfl⟩ := mem_map.mp hb
    have prior : (v, j) ∈ mergeSort (xs.zipIdx 1) order :=
      tailPerm.mem_iff.mpr (mem_append.mpr (.inl hm))
    have pos : 1 ≤ j := (mem_zipIdx (mem_mergeSort.mp prior)).1
    have cmp := zipIdxSpec.mp (sorted.rel_of_mem_append hm mem_cons_self)
    cases h : le a v with
    | false => rfl
    | true => exact (Nat.not_succ_le_zero 0 (Nat.le_trans pos (cmp.2 h))).elim

open _root_.List in
public theorem List.sublist_mergeSort : type_of% @_root_.List.sublist_mergeSort := by
  intro α le xs trans total ys sorted sub
  induction sub with
  | slnil => exact nil_sublist _
  | @cons ys xs a sub ih =>
    obtain ⟨left, right, pivot, tail, _⟩ := List.mergeSort_cons trans total a xs
    rw [pivot]
    have subTail := ih sorted
    rw [tail] at subTail
    exact subTail.middle a
  | @cons_cons ys xs a sub ih =>
    obtain ⟨left, right, pivot, tail, prior⟩ := List.mergeSort_cons trans total a xs
    have subTail := ih sorted.tail
    rw [tail] at subTail
    rw [pivot]
    apply sublist_append_of_sublist_right
    apply Sublist.cons_cons
    apply Sublist.of_sublist_append_right _ subTail
    intro b inYs inLeft
    have yes := rel_of_pairwise_cons sorted inYs
    have no := prior b inLeft
    rw [yes] at no
    exact Bool.noConfusion no

@[expose] public def List.MergeSort.Internal.mergeTR : type_of% @_root_.List.MergeSort.Internal.mergeTR :=
  @_root_.List.merge

public theorem List.MergeSort.Internal.merge_eq_mergeTR :
    @_root_.List.merge = @List.MergeSort.Internal.mergeTR := rfl

@[expose] public def List.MergeSort.Internal.mergeSortTR : type_of% @_root_.List.MergeSort.Internal.mergeSortTR :=
  @_root_.List.mergeSort

public theorem List.MergeSort.Internal.mergeSort_eq_mergeSortTR :
    @_root_.List.mergeSort = @List.MergeSort.Internal.mergeSortTR := rfl

@[expose] public def List.MergeSort.Internal.mergeSortTR₂ : type_of% @_root_.List.MergeSort.Internal.mergeSortTR₂ :=
  @_root_.List.mergeSort

public theorem List.MergeSort.Internal.mergeSort_eq_mergeSortTR₂ :
    @_root_.List.mergeSort = @List.MergeSort.Internal.mergeSortTR₂ := rfl

end OmegaChecks.InitPort.Alternatives
