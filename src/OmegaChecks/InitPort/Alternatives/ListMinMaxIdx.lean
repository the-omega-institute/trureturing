module
public import Init.Data.List.MinMaxIdx
import all Init.Data.Order.Opposite
import all Init.Data.List.MinMaxIdx
import all Init.Data.List.MinMaxOn

/-! The first minimum of an append belongs to the left list also when both minima tie. -/

open scoped Std.OppositeOrderInstances
namespace OmegaChecks.InitPort.Alternatives
public theorem List.minIdxOn_le_of_apply_getElem_le_apply_minOn._proof_1_1.{u, v} :
    type_of% (private_decl% @_root_.List.minIdxOn_le_of_apply_getElem_le_apply_minOn._proof_1_1.{u, v}) := by
  intro _ _ _ _ _ _ _ k hk _ _ denied
  exact denied (Nat.lt_min.mpr ⟨Nat.lt_succ_self k, hk⟩)

public theorem List.getElem_minIdxOn._proof_1_1.{u, v} :
    type_of% (private_decl% @_root_.List.getElem_minIdxOn._proof_1_1.{u, v}) := by
  intro _ _ _ _ _ xs _ _ _ denied
  exact denied (Nat.le_succ xs.length)

public theorem List.minIdxOn_eq_go_drop._proof_1_14.{u, v} :
    type_of% (private_decl% @_root_.List.minIdxOn_eq_go_drop._proof_1_14.{u, v}) := by
  intro _ _ _ _ _ _ _ _ _ _ _ hk denied
  exact denied (Nat.succ_lt_succ hk)

private theorem minimumAfterPrefix.{u, v} {β : Type u} {α : Type v}
    [LE β] [DecidableLE β] [Std.IsLinearPreorder β] {f : α → β} {xs : List α}
    (nonempty : xs ≠ []) {k : Nat} :
    let front := xs.take (k + 1)
    let frontNE : front ≠ [] := fun h =>
      (_root_.List.take_eq_nil_iff.mp h).elim (Nat.succ_ne_zero k) nonempty
    ∃ (i : Nat) (hlt : i < xs.length), i ≤ k ∧ xs[i] = front.minOn f frontNE ∧
      xs.minIdxOn f nonempty = _root_.List.minIdxOn.go f (front.minOn f frontNE) i (k + 1) (xs.drop (k + 1)) := by
  let front := xs.take (k + 1)
  let tail := xs.drop (k + 1)
  have frontNE : front ≠ [] := by cases xs with
    | nil => exact (nonempty rfl).elim
    | cons x xs => exact _root_.List.cons_ne_nil _ _
  let i := front.minIdxOn f frontNE
  have hi : i < front.length := _root_.List.minIdxOn_lt_length frontNE
  have hiFull : i < xs.length :=
    Nat.lt_of_lt_of_le hi (by
      change (xs.take (k + 1)).length ≤ xs.length
      rw [_root_.List.length_take]
      exact Nat.min_le_right _ _)
  refine ⟨i, hiFull, Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hi (_root_.List.length_take_le _ _)), ?_, ?_⟩
  · exact (_root_.List.getElem_take (xs := xs) (j := k + 1) (h := hi)).symm.trans
      (_root_.List.getElem_minIdxOn frontNE)
  · change xs.minIdxOn f nonempty = _root_.List.minIdxOn.go f (front.minOn f frontNE) i (k + 1) tail
    have appendEq : front ++ tail = xs := _root_.List.take_append_drop _ _
    have replace {other : List α} (e : other = xs) (hne : other ≠ []) :
        xs.minIdxOn f nonempty = other.minIdxOn f hne := by cases e; rfl
    cases ht : tail with
    | nil =>
      have same : front = xs := by
        rw [ht, _root_.List.append_nil] at appendEq
        exact appendEq
      exact replace same frontNE
    | cons y ys =>
      have tailNE : tail ≠ [] := fun e => _root_.List.cons_ne_nil y ys (ht.symm.trans e)
      have appendedNE : front ++ tail ≠ [] := fun e => nonempty (appendEq.symm.trans e)
      have fullIndex : k + 1 ≤ xs.length := by
        apply Nat.le_of_not_lt
        intro shorter
        exact tailNE (_root_.List.drop_of_length_le (Nat.le_of_lt shorter))
      have lengthEq : front.length = k + 1 := _root_.List.length_take_of_le fullIndex
      rw [← ht, _root_.List.minIdxOn.go_eq, dite_eq_right tailNE, replace appendEq appendedNE,
        _root_.List.minIdxOn_append frontNE tailNE, lengthEq]
      exact congrArg (fun j => if f (front.minOn f frontNE) ≤ f (tail.minOn f tailNE) then i else j)
        (Nat.add_comm _ _)

public theorem List.minIdxOn_eq_go_drop : type_of% (private_decl% @minimumAfterPrefix) := @minimumAfterPrefix

public theorem List.minIdxOn_append_aux.{u, v} :
    type_of% (private_decl% @_root_.List.minIdxOn_append_aux.{u, v}) := by
  intro β α _ _ _ xs ys f hxs hys
  unfold _root_.List.combineMinIdxOn
  rw [_root_.List.getElem_minIdxOn, _root_.List.getElem_minIdxOn]
  exact _root_.List.minIdxOn_append hxs hys

public theorem List.minIdxOn_cons_aux.{u, v} :
    type_of% (private_decl% @_root_.List.minIdxOn_cons_aux.{u, v}) := by
  intro β α _ _ _ x xs f hxs
  exact (private_decl% _root_.List.minIdxOn_append_aux) (_root_.List.cons_ne_nil x []) hxs

public theorem List.minIdxOn_eq_zero_iff : type_of% @_root_.List.minIdxOn_eq_zero_iff := by
  intro β α _ _ _ xs f nonempty
  cases xs with
  | nil => exact (nonempty rfl).elim
  | cons a xs =>
    constructor
    · intro zero y mem
      have atBest := _root_.List.getElem_minIdxOn (f := f) nonempty
      have headIsBest : a = (a :: xs).minOn f nonempty := by
        simpa only [zero, List.getElem_cons_zero] using atBest
      change f a ≤ f y
      rw [headIsBest]
      exact _root_.List.apply_minOn_le_of_mem mem
    · intro least
      apply (private_decl% @_root_.List.minIdxOn.go_eq_of_forall_le)
      exact fun y mem => least y (.tail _ mem)

public theorem List.maxIdxOn_eq_zero_iff : type_of% @_root_.List.maxIdxOn_eq_zero_iff := by
  intro β α rel dec ord xs f h
  simp only [_root_.List.maxIdxOn_eq_minIdxOn]
  simpa only [LE.le_opposite_iff] using @List.minIdxOn_eq_zero_iff β α rel.opposite
    (@Std.OppositeOrderInstances.instDecidableLEOpposite β rel dec)
    (@Std.OppositeOrderInstances.instIsLinearPreorderOpposite β rel ord) xs f h

public theorem List.minIdxOn?_eq_some_zero_iff : type_of% @_root_.List.minIdxOn?_eq_some_zero_iff := by
  intro β α _ _ _ xs f
  constructor
  · intro e
    have h := _root_.List.ne_nil_of_minIdxOn?_eq_some e
    exact ⟨h, (List.minIdxOn_eq_zero_iff h).mp (Option.some.inj
      ((_root_.List.minIdxOn?_eq_some_minIdxOn h).symm.trans e))⟩
  · rintro ⟨h, least⟩
    exact (_root_.List.minIdxOn?_eq_some_minIdxOn h).trans (congrArg some ((List.minIdxOn_eq_zero_iff h).mpr least))

public theorem List.maxIdxOn?_eq_some_zero_iff : type_of% @_root_.List.maxIdxOn?_eq_some_zero_iff := by
  intro β α rel dec ord xs f
  simp only [_root_.List.maxIdxOn?_eq_minIdxOn?]
  simpa only [LE.le_opposite_iff] using @List.minIdxOn?_eq_some_zero_iff β α rel.opposite
    (@Std.OppositeOrderInstances.instDecidableLEOpposite β rel dec)
    (@Std.OppositeOrderInstances.instIsLinearPreorderOpposite β rel ord) xs f

open scoped Classical.Order in
public theorem List.minIdxOn_append : type_of% @_root_.List.minIdxOn_append := by
  intro β α _ _ _ xs ys f hx hy
  have ix := _root_.List.minIdxOn_lt_length (f := f) hx
  have iy := _root_.List.minIdxOn_lt_length (f := f) hy
  by_cases left : f (xs.minOn f hx) ≤ f (ys.minOn f hy)
  · rw [ite_eq_left left]
    apply (_root_.List.minIdxOn_eq_iff_eq_minOn _).mpr
    refine ⟨?_, ?_, ?_⟩
    · rw [_root_.List.length_append]
      exact Nat.lt_add_right _ ix
    · rw [_root_.List.getElem_append_left ix, _root_.List.getElem_minIdxOn,
        _root_.List.minOn_append hx hy, _root_.minOn_eq_left left]
    · intro j hj
      rw [_root_.List.minOn_append hx hy, _root_.minOn_eq_left left,
        _root_.List.getElem_append_left (Nat.lt_trans hj ix)]
      exact _root_.List.apply_minOn_lt_apply_getElem_of_lt_minIdxOn hx hj
  · rw [ite_eq_right left]
    have less : f (ys.minOn f hy) < f (xs.minOn f hx) :=
      ⟨Std.le_total.resolve_left left, left⟩
    apply (_root_.List.minIdxOn_eq_iff_eq_minOn _).mpr
    refine ⟨?_, ?_, ?_⟩
    · rw [_root_.List.length_append]
      exact Nat.add_lt_add_left iy _
    · simp only [_root_.List.getElem_append_right (Nat.le_add_right ..), Nat.add_sub_cancel_left,
        _root_.List.getElem_minIdxOn, _root_.List.minOn_append hx hy, _root_.minOn_eq_right left]
    · intro j hj
      rw [_root_.List.minOn_append hx hy, _root_.minOn_eq_right left]
      by_cases inLeft : j < xs.length
      · rw [_root_.List.getElem_append_left inLeft]
        exact Std.lt_of_lt_of_le less (_root_.List.apply_minOn_le_of_mem (_root_.List.getElem_mem inLeft))
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt inLeft)
        simp only [_root_.List.getElem_append_right (Nat.le_add_right ..), Nat.add_sub_cancel_left]
        exact _root_.List.apply_minOn_lt_apply_getElem_of_lt_minIdxOn hy (Nat.lt_of_add_lt_add_left hj)

public theorem List.minIdxOn_cons : type_of% @_root_.List.minIdxOn_cons := by
  intro β α _ _ _ x xs f
  cases xs with
  | nil => rfl
  | cons y ys =>
    have hx := _root_.List.cons_ne_nil y ys
    rw [dite_eq_right hx]
    have split := List.minIdxOn_append (f := f) (_root_.List.cons_ne_nil x []) hx
    simpa only [_root_.List.singleton_append, _root_.List.minOn_singleton,
      _root_.List.minIdxOn_singleton, _root_.List.length_singleton, Nat.one_add] using split

public theorem List.minIdxOn?_cons : type_of% @_root_.List.minIdxOn?_cons := by
  intros
  rw [_root_.List.minIdxOn?_cons_eq_some_minIdxOn]
  exact congrArg some List.minIdxOn_cons

public theorem List.left_le_minIdxOn_append : type_of% @_root_.List.left_le_minIdxOn_append := by
  intro β α _ _ _ xs ys f hx
  cases ys with
  | nil => simp only [_root_.List.append_nil, Nat.le_refl]
  | cons y ys =>
    rw [List.minIdxOn_append hx (_root_.List.cons_ne_nil y ys)]
    split
    · exact Nat.le_refl _
    · exact Nat.le_trans (Nat.le_of_lt (_root_.List.minIdxOn_lt_length hx)) (Nat.le_add_right ..)

public theorem List.maxIdxOn_cons : type_of% @_root_.List.maxIdxOn_cons := by
  intro β α rel dec ord x xs f
  simp only [_root_.List.maxIdxOn_eq_minIdxOn, _root_.List.maxOn_eq_minOn]
  simpa only [LE.le_opposite_iff] using @List.minIdxOn_cons β α rel.opposite
    (@Std.OppositeOrderInstances.instDecidableLEOpposite β rel dec)
    (@Std.OppositeOrderInstances.instIsLinearPreorderOpposite β rel ord) x xs f

public theorem List.maxIdxOn_append : type_of% @_root_.List.maxIdxOn_append := by
  intro β α rel dec ord xs ys f hx hy
  simp only [_root_.List.maxIdxOn_eq_minIdxOn, _root_.List.maxOn_eq_minOn]
  simpa only [LE.le_opposite_iff] using @List.minIdxOn_append β α rel.opposite
    (@Std.OppositeOrderInstances.instDecidableLEOpposite β rel dec)
    (@Std.OppositeOrderInstances.instIsLinearPreorderOpposite β rel ord) xs ys f hx hy

public theorem List.maxIdxOn?_cons : type_of% @_root_.List.maxIdxOn?_cons := by
  intros
  rw [_root_.List.maxIdxOn?_cons_eq_some_maxIdxOn]
  exact congrArg some List.maxIdxOn_cons

end OmegaChecks.InitPort.Alternatives
