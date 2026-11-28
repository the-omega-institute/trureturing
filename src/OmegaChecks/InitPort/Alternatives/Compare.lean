module
import all Init.Data.Ord.Array
public import Init.Data.Int.Compare
public import Init.Data.Nat.Compare
public import Init.Data.Order.Ord

namespace OmegaChecks.InitPort.Alternatives

public theorem Nat.compare_ne_gt : type_of% @_root_.Nat.compare_ne_gt :=
  Iff.trans (not_congr _root_.Nat.compare_eq_gt) _root_.Nat.not_lt

public theorem Nat.compare_ne_lt : type_of% @_root_.Nat.compare_ne_lt :=
  Iff.trans (not_congr _root_.Nat.compare_eq_lt) _root_.Nat.not_lt

public theorem Int.compare_ne_gt : type_of% @_root_.Int.compare_ne_gt :=
  Iff.trans (not_congr _root_.Int.compare_eq_gt) _root_.Int.not_lt

public theorem Int.compare_ne_lt : type_of% @_root_.Int.compare_ne_lt :=
  Iff.trans (not_congr _root_.Int.compare_eq_lt) _root_.Int.not_lt

public theorem Ordering.then.eq_2 : type_of% @_root_.Ordering.then.eq_2 := by
  intro a b different
  cases a with
  | lt | gt => rfl
  | eq => exact (different rfl).elim

public theorem Std.OrientedCmp.not_lt_of_isLE : type_of% @_root_.Std.OrientedCmp.not_lt_of_isLE := by
  intro α cmp oriented a b le lt
  exact Std.OrientedCmp.not_isLE_of_lt lt le

public theorem Std.OrientedCmp.not_gt_of_isGE : type_of% @_root_.Std.OrientedCmp.not_gt_of_isGE := by
  intro α cmp oriented a b ge gt
  exact Std.OrientedCmp.not_isGE_of_gt gt ge

public theorem Std.OrientedCmp.not_lt_of_lt : type_of% @_root_.Std.OrientedCmp.not_lt_of_lt := by
  intro α cmp oriented a b ab ba
  exact Std.OrientedCmp.not_isLE_of_lt ab (Ordering.isLE_of_eq_lt ba)

public theorem Std.OrientedCmp.not_gt_of_gt : type_of% @_root_.Std.OrientedCmp.not_gt_of_gt := by
  intro α cmp oriented a b ab ba
  exact Std.OrientedCmp.not_isGE_of_gt ab (Ordering.isGE_of_eq_gt ba)

public theorem Std.OrientedCmp.lt_of_not_isLE : type_of% @_root_.Std.OrientedCmp.lt_of_not_isLE := by
  intro α cmp oriented a b h
  apply Std.OrientedCmp.lt_of_gt
  cases hab : cmp a b with
  | lt => exact (h (Ordering.isLE_of_eq_lt hab)).elim
  | eq => exact (h (Ordering.isLE_of_eq_eq hab)).elim
  | gt => rfl

public theorem Std.OrientedCmp.gt_of_not_isGE : type_of% @_root_.Std.OrientedCmp.gt_of_not_isGE := by
  intro α cmp oriented a b h
  apply Std.OrientedCmp.gt_of_lt
  cases hab : cmp a b with
  | gt => exact (h (Ordering.isGE_of_eq_gt hab)).elim
  | eq => exact (h (Ordering.isGE_of_eq_eq hab)).elim
  | lt => rfl

private theorem compareIsLE {α : Type u} [LT α] [DecidableLT α] [DecidableEq α] (x y : α) :
    (compareOfLessAndEq x y).isLE ↔ x < y ∨ x = y := by
  unfold compareOfLessAndEq
  split
  next xy => exact ⟨fun _ => .inl xy, fun _ => rfl⟩
  next noLt =>
    split
    next xy => exact ⟨fun _ => .inr xy, fun _ => rfl⟩
    next ne => exact ⟨(fun h => nomatch h), fun h => h.elim (fun lt => (noLt lt).elim) (fun eq => (ne eq).elim)⟩

public theorem lt_iff_not_gt_and_ne_of_antisymm_of_total_of_not_le :
    type_of% @_root_.lt_iff_not_gt_and_ne_of_antisymm_of_total_of_not_le := by
  intro α lt le decLt decEq antisymm total notLE x y
  constructor
  · intro xy
    have forward := (total y x).resolve_left (notLE.mpr xy)
    exact ⟨fun yx => notLE.mpr yx forward, fun eq => notLE.mpr xy (eq ▸ forward)⟩
  · intro ⟨noReverse, different⟩
    apply notLE.mp
    intro reverse
    exact noReverse (notLE.mp (fun forward => different (antisymm forward reverse)))

public theorem compareOfLessAndEq_eq_eq : type_of% @_root_.compareOfLessAndEq_eq_eq := by
  intro α lt le decLt decLe decEq refl notLE x y
  unfold compareOfLessAndEq
  split
  next xy =>
    exact ⟨(fun h => nomatch h), fun eq => (notLE.mpr xy (eq ▸ refl x)).elim⟩
  next =>
    split
    next eq => exact ⟨fun _ => eq, fun _ => rfl⟩
    next ne => exact ⟨(fun h => nomatch h), fun eq => (ne eq).elim⟩

public theorem Std.TransOrd.compareOfLessAndEq_of_lt_trans_of_lt_iff :
    type_of% @_root_.Std.TransOrd.compareOfLessAndEq_of_lt_trans_of_lt_iff := by
  intro α lt decLt decEq trans character
  refine { eq_swap := compareOfLessAndEq_eq_swap_of_lt_iff_not_gt_and_ne character, isLE_trans := ?_ }
  · intro x y z xy yz
    apply (compareIsLE x z).mpr
    cases (compareIsLE x y).mp xy with
    | inr eq => exact eq ▸ (compareIsLE y z).mp yz
    | inl hxy =>
      cases (compareIsLE y z).mp yz with
      | inr eq => exact eq ▸ Or.inl hxy
      | inl hyz => exact .inl (trans hxy hyz)

public theorem Std.TransOrd.compareOfLessAndEq_of_antisymm_of_trans_of_total_of_not_le :
    type_of% @_root_.Std.TransOrd.compareOfLessAndEq_of_antisymm_of_trans_of_total_of_not_le := by
  intro α lt le decLt decLe decEq antisymm trans total notLE
  apply Std.TransOrd.compareOfLessAndEq_of_lt_trans_of_lt_iff
  · intro a b c ab bc
    apply notLE.mp
    intro ca
    have forward := (total b a).resolve_left (notLE.mpr ab)
    exact notLE.mpr bc (trans ca forward)
  · exact lt_iff_not_gt_and_ne_of_antisymm_of_total_of_not_le antisymm total notLE

public theorem Std.LawfulEqCmp.opposite : type_of% @_root_.Std.LawfulEqCmp.opposite := by
  intro α cmp oriented lawful
  exact { compare_self := Std.ReflCmp.compare_self (cmp := cmp)
          eq_of_compare := fun h => Std.LawfulEqCmp.eq_of_compare (cmp := cmp) (Std.OrientedCmp.eq_symm h) }

public theorem Std.LawfulBEqCmp.opposite : type_of% @_root_.Std.LawfulBEqCmp.opposite := by
  intro α beq cmp oriented lawful
  exact ⟨Std.OrientedCmp.eq_comm.trans lawful.compare_eq_iff_beq⟩

public theorem Std.LawfulBEqCmp.equivBEq : type_of% @_root_.Std.LawfulBEqCmp.equivBEq := by
  intro α beq cmp lawful transCmp
  exact { toReflBEq := _root_.Std.LawfulBEqCmp.reflBEq (cmp := cmp)
          symm := fun h => lawful.compare_eq_iff_beq.mp (Std.OrientedCmp.eq_symm (lawful.compare_eq_iff_beq.mpr h))
          trans := fun h k => lawful.compare_eq_iff_beq.mp
            (Std.TransCmp.eq_trans (lawful.compare_eq_iff_beq.mpr h) (lawful.compare_eq_iff_beq.mpr k)) }

public theorem Std.LawfulBEqCmp.lawfulBEq : type_of% @_root_.Std.LawfulBEqCmp.lawfulBEq := by
  intro α beq cmp lawful eqCmp
  exact { toReflBEq := _root_.Std.LawfulBEqCmp.reflBEq (cmp := cmp)
          eq_of_beq := fun h => eqCmp.eq_of_compare (lawful.compare_eq_iff_beq.mpr h) }

private theorem consSizeLE (a : α) (xs : List α) (i : Nat) :
    (a :: xs).toArray.size ≤ i+1 ↔ xs.toArray.size ≤ i := by
  rw [List.size_toArray, List.size_toArray]
  exact Nat.succ_le_succ_iff

private theorem consArrayAt (a : α) (xs : List α) (i : Nat)
    (h : i+1 < (a :: xs).toArray.size) (k : i < xs.toArray.size) :
    (a :: xs).toArray[i+1] = xs.toArray[i] := by
  rw [List.getElem_toArray, List.getElem_toArray, List.getElem_cons_succ]

public theorem Array.compareLex.go_succ : type_of% (private_decl% @_root_.Array.compareLex.go_succ) := by
  intro α cmp x y xs ys i
  induction i using Array.compareLex.go.induct cmp xs.toArray ys.toArray
  all_goals
    rw [Array.compareLex.go.eq_1 cmp (x :: xs).toArray (y :: ys).toArray,
      Array.compareLex.go.eq_1 cmp xs.toArray ys.toArray]
  case case1 i hx hy => rw [dite_eq_left hx, ite_eq_left hy, dite_eq_left ((consSizeLE ..).mpr hx), ite_eq_left ((consSizeLE ..).mpr hy)]
  case case2 i hx hy => rw [dite_eq_left hx, ite_eq_right hy, dite_eq_left ((consSizeLE ..).mpr hx), ite_eq_right (fun h => hy ((consSizeLE ..).mp h))]
  case case3 i hx hy => rw [dite_eq_right hx, dite_eq_left hy, dite_eq_right (fun h => hx ((consSizeLE ..).mp h)), dite_eq_left ((consSizeLE ..).mpr hy)]
  case' case4 i hx hy hcmp => skip
  case' case5 i hx hy hcmp ih => skip
  case' case6 i hx hy hcmp => skip
  all_goals
    rw [dite_eq_right hx, dite_eq_right hy, dite_eq_right (fun h => hx ((consSizeLE ..).mp h)),
      dite_eq_right (fun h => hy ((consSizeLE ..).mp h)),
      consArrayAt x xs i _ (Nat.lt_of_not_ge hx), consArrayAt y ys i _ (Nat.lt_of_not_ge hy)]
    rw [hcmp] <;> assumption

public theorem List.compareLex_eq_compareLex_toArray : type_of% @_root_.List.compareLex_eq_compareLex_toArray := by
  intro α cmp xs ys
  unfold _root_.Array.compareLex
  have emptyBound : ([] : List α).toArray.size ≤ 0 := Nat.le_refl 0
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rw [Array.compareLex.go.eq_1, dite_eq_left emptyBound, ite_eq_left emptyBound]; rfl
    | cons y ys =>
      rw [Array.compareLex.go.eq_1, dite_eq_left emptyBound, ite_eq_right]
      · rfl
      · rw [List.size_toArray]; exact Nat.not_succ_le_zero _
  | cons x xs ih =>
    cases ys with
    | nil =>
      rw [Array.compareLex.go.eq_1, dite_eq_right, dite_eq_left emptyBound]
      · rfl
      · rw [List.size_toArray]; exact Nat.not_succ_le_zero _
    | cons y ys =>
      have positive (a : α) (l : List α) : ¬ (a :: l).toArray.size ≤ 0 := by
        rw [List.size_toArray]; exact Nat.not_succ_le_zero _
      rw [Array.compareLex.go.eq_1, dite_eq_right (positive x xs), dite_eq_right (positive y ys),
        List.getElem_toArray, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_zero,
        _root_.List.compareLex_cons_cons]
      cases cmp x y with
      | lt | gt => rfl
      | eq => exact (ih (ys := ys)).trans (private_decl% _root_.Array.compareLex.go_succ).symm

public theorem isLE_compareOfLessAndEq : type_of% @_root_.isLE_compareOfLessAndEq := by
  intro α lt le decLt decLe decEq antisymm notLE total x y
  refine (compareIsLE x y).trans ⟨?_, ?_⟩
  · rintro (xy | rfl)
    · exact (total y x).resolve_left (notLE.mpr xy)
    · exact (total x x).elim id id
  · intro xy
    by_cases rev : y ≤ x
    · exact .inr (antisymm xy rev)
    · exact .inl (notLE.mp rev)

public theorem List.instLawfulBEqCmpCompareLex : type_of% @_root_.List.instLawfulBEqCmpCompareLex := by
  intro α cmp beq lawful
  constructor
  intro xs ys
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => exact ⟨fun _ => rfl, fun _ => rfl⟩
    | cons y ys => exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
  | cons x xs ih =>
    cases ys with
    | nil => exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
    | cons y ys =>
      rw [_root_.List.compareLex_cons_cons, List.cons_beq_cons]
      exact Ordering.then_eq_eq.trans
        ((and_congr lawful.compare_eq_iff_beq ih).trans Bool.and_eq_true_iff.symm)

public theorem Array.isEqv_eq_decide : type_of% @_root_.Array.isEqv_eq_decide := by
  intro α xs ys r
  apply Bool.eq_iff_iff.mpr
  split
  next sizes =>
    refine Array.isEqv_iff_rel.trans ⟨?_, ?_⟩
    · rintro ⟨_, all⟩
      exact decide_eq_true all
    · exact fun h => ⟨sizes, of_decide_eq_true h⟩
  next different =>
    constructor
    · intro h
      obtain ⟨sizes, _⟩ := Array.isEqv_iff_rel.mp h
      exact (different sizes).elim
    · exact fun h => nomatch h

public theorem Array.beq_eq_decide : type_of% @_root_.Array.beq_eq_decide := by
  intros
  exact Array.isEqv_eq_decide _ _ _

public theorem Array.instLawfulBEqCmpCompareLex : type_of% @_root_.Array.instLawfulBEqCmpCompareLex := by
  intro α cmp beq lawful
  constructor
  intro xs ys
  rw [_root_.Array.compareLex_eq_compareLex_toList, ← Array.beq_toList]
  exact Std.LawfulBEqCmp.compare_eq_iff_beq (cmp := List.compareLex cmp)

end OmegaChecks.InitPort.Alternatives
