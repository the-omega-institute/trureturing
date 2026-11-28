module
public import OmegaChecks.InitPort.Alternatives.Order
import all Init.Data.List.MinMaxIdx
import all Init.Data.List.MinMaxOn
import Init.Data.List.MinMax
import all Init.Data.Array.MinMax

/-! Nonemptiness and ordering of list extrema, proved using only membership and order laws. -/

namespace OmegaChecks.InitPort.Alternatives

private theorem emptyHasNoResult {α : Type u} :
    false = true ↔ ([] : List α) ≠ [] :=
  ⟨(fun h => nomatch h), fun h => (h rfl).elim⟩

private theorem consHasResult {x : α} {xs : List α} :
    true = true ↔ x :: xs ≠ [] :=
  ⟨fun _ => List.cons_ne_nil x xs, fun _ => rfl⟩

public theorem List.isSome_min?_iff : type_of% @_root_.List.isSome_min?_iff := by
  intro α inst xs
  cases xs with
  | nil => exact emptyHasNoResult
  | cons => exact consHasResult

public theorem List.isSome_max?_iff : type_of% @_root_.List.isSome_max?_iff := by
  intro α inst xs
  cases xs with
  | nil => exact emptyHasNoResult
  | cons => exact consHasResult

public theorem List.isSome_minOn?_iff : type_of% @_root_.List.isSome_minOn?_iff := by
  intro β α le dec f xs
  cases xs with
  | nil => exact emptyHasNoResult
  | cons => exact consHasResult

public theorem List.isSome_maxOn?_iff : type_of% @_root_.List.isSome_maxOn?_iff := by
  intro β α le dec f xs
  cases xs with
  | nil => exact emptyHasNoResult
  | cons => exact consHasResult

public theorem List.isSome_minIdxOn?_iff : type_of% @_root_.List.isSome_minIdxOn?_iff := by
  intro β α le dec f xs
  cases xs with
  | nil => exact emptyHasNoResult
  | cons => exact consHasResult

public theorem List.le_apply_minOn_iff : type_of% @_root_.List.le_apply_minOn_iff := by
  intro β α le dec order xs f nonempty b
  exact ⟨fun below _ member => Std.IsPreorder.le_trans _ _ _ below (_root_.List.apply_minOn_le_of_mem member),
    fun below => below _ _root_.List.minOn_mem⟩

public theorem List.apply_minOn_le_apply_minOn_of_subset :
    type_of% @_root_.List.apply_minOn_le_apply_minOn_of_subset := by
  intro β α le dec order xs ys f subset nonempty
  exact _root_.List.apply_minOn_le_of_mem (subset _root_.List.minOn_mem)

private theorem foldAfterHead (f : β → α → β) (x : α) (xs : List α) (init : β) :
    (x :: xs).toArray.foldl f init 1 = xs.foldl f init := by
  rw [Array.foldl_eq_foldl_extract, ← Array.foldl_toList, Array.toList_extract]
  change (xs.take (xs.length + 1 - 1)).foldl f init = xs.foldl f init
  rw [Nat.add_sub_cancel, List.take_length]

public theorem List.min_toArray : type_of% @_root_.List.min_toArray := by
  intro α inst xs h
  cases xs with
  | nil => exact (h rfl).elim
  | cons a as => exact foldAfterHead min a as a

public theorem List.max_toArray : type_of% @_root_.List.max_toArray := by
  intro α inst xs h
  cases xs with
  | nil => exact (h rfl).elim
  | cons a as => exact foldAfterHead max a as a

public theorem List.min?_toArray : type_of% @_root_.List.min?_toArray := by
  intro α inst xs
  cases xs with
  | nil => rfl
  | cons a as =>
    unfold Array.min?
    rw [dite_eq_left (fun e => List.cons_ne_nil a as (congrArg Array.toList e))]
    exact congrArg some List.min_toArray

public theorem List.max?_toArray : type_of% @_root_.List.max?_toArray := by
  intro α inst xs
  cases xs with
  | nil => rfl
  | cons a as =>
    unfold Array.max?
    rw [dite_eq_left (fun e => List.cons_ne_nil a as (congrArg Array.toList e))]
    exact congrArg some List.max_toArray

public theorem List.minOn_eq_min : type_of% @_root_.List.minOn_eq_min := by
  intro α β _ _ _ _ _ _ f xs nonempty law
  cases xs with
  | nil => exact (nonempty rfl).elim
  | cons x xs =>
    change xs.foldl (_root_.minOn f) x = xs.foldl min x
    clear nonempty
    induction xs generalizing x with
    | nil => rfl
    | cons a xs ih =>
      rw [_root_.List.foldl_cons, _root_.List.foldl_cons, _root_.minOn_eq_min (law x a)]
      exact ih _

public theorem List.maxOn_eq_max : type_of% @_root_.List.maxOn_eq_max := by
  intro α β _ _ _ _ _ _ f xs nonempty law
  cases xs with
  | nil => exact (nonempty rfl).elim
  | cons x xs =>
    induction xs generalizing x with
    | nil => rw [_root_.List.maxOn_singleton, _root_.List.max_singleton]
    | cons a xs ih =>
      rw [_root_.List.maxOn_cons_cons, _root_.List.max_cons_cons]
      exact (ih (_root_.maxOn f x a) (nonempty := _root_.List.cons_ne_nil _ _)).trans
        (congrArg (fun z => (z :: xs).max (_root_.List.cons_ne_nil _ _)) (_root_.maxOn_eq_max (law a x)))

public theorem List.minOn_id : type_of% @_root_.List.minOn_id := by
  intros
  exact List.minOn_eq_min (fun _ _ => Iff.rfl)

public theorem List.maxOn_id : type_of% @_root_.List.maxOn_id := by
  intros
  exact List.maxOn_eq_max (fun _ _ => Iff.rfl)

public theorem List.minOn?_id : type_of% @_root_.List.minOn?_id := by
  intro α _ _ _ _ xs
  cases xs with
  | nil => rfl
  | cons x xs =>
    have h := _root_.List.cons_ne_nil x xs
    rw [_root_.List.minOn?_eq_some_minOn h, _root_.List.min?_eq_some_min h, List.minOn_id h]

public theorem List.maxOn?_id : type_of% @_root_.List.maxOn?_id := by
  intro α _ _ _ _ xs
  cases xs with
  | nil => rfl
  | cons x xs =>
    have h := _root_.List.cons_ne_nil x xs
    rw [_root_.List.maxOn?_eq_some_maxOn h, _root_.List.max?_eq_some_max h, List.maxOn_id h]

public theorem List.minOn_replicate : type_of% @_root_.List.minOn_replicate := by
  intros
  exact _root_.List.eq_of_mem_replicate _root_.List.minOn_mem

public theorem List.maxOn_replicate : type_of% @_root_.List.maxOn_replicate := by
  intros
  exact _root_.List.eq_of_mem_replicate _root_.List.maxOn_mem

public theorem List.minOn?_replicate : type_of% @_root_.List.minOn?_replicate := by
  intro β α _ _ _ n a f
  cases n with
  | zero => rfl
  | succ n =>
    have h : _root_.List.replicate (n+1) a ≠ [] := by
      rw [_root_.List.replicate_succ]; exact _root_.List.cons_ne_nil _ _
    rw [ite_eq_right (Nat.succ_ne_zero _), _root_.List.minOn?_eq_some_minOn h, List.minOn_replicate]

public theorem List.maxOn?_replicate : type_of% @_root_.List.maxOn?_replicate := by
  intro β α _ _ _ n a f
  cases n with
  | zero => rfl
  | succ n =>
    have h : _root_.List.replicate (n+1) a ≠ [] := by
      rw [_root_.List.replicate_succ]; exact _root_.List.cons_ne_nil _ _
    rw [ite_eq_right (Nat.succ_ne_zero _), _root_.List.maxOn?_eq_some_maxOn h, List.maxOn_replicate]

public theorem List.apply_minOn_lt_iff : type_of% @_root_.List.apply_minOn_lt_iff := by
  intro β α _ _ _ _ _ xs f nonempty b
  exact ⟨fun h => ⟨_, _root_.List.minOn_mem, h⟩,
    fun ⟨x, mem, less⟩ => Std.lt_of_le_of_lt (_root_.List.apply_minOn_le_of_mem mem) less⟩

public theorem List.lt_apply_maxOn_iff : type_of% @_root_.List.lt_apply_maxOn_iff := by
  intro β α _ _ _ _ _ xs f nonempty b
  exact ⟨fun h => ⟨_, _root_.List.maxOn_mem, h⟩,
    fun ⟨x, mem, less⟩ => Std.lt_of_lt_of_le less (_root_.List.le_apply_maxOn_of_mem mem)⟩

public theorem List.minIdxOn.go_eq_of_forall_le :
    type_of% (private_decl% @_root_.List.minIdxOn.go_eq_of_forall_le) := by
  intro β α inst dec f x i j xs below
  induction xs generalizing j with
  | nil => rfl
  | cons y ys ih =>
    rw [_root_.List.minIdxOn.go, ite_eq_left (below y _root_.List.mem_cons_self)]
    exact ih (j := j+1) (fun z mem => below z (.tail _ mem))

public theorem List.minIdxOn_replicate : type_of% @_root_.List.minIdxOn_replicate := by
  intro β α _ _ _ n a f nonempty
  cases n with
  | zero => exact (nonempty rfl).elim
  | succ n =>
    simp only [_root_.List.replicate_succ] at nonempty ⊢
    apply (private_decl% @_root_.List.minIdxOn.go_eq_of_forall_le)
    intro y mem
    cases _root_.List.eq_of_mem_replicate mem
    exact Std.Refl.refl _

private theorem minIdxLookup [LE β] [DecidableLE β] (f : α → β)
    (full tail : _root_.List α) (best : α) (i j : Nat)
    (selected : full[i]? = some best) (suffix : ∀ k, full[j+k]? = tail[k]?) :
    full[_root_.List.minIdxOn.go f best i j tail]? = some (tail.foldl (_root_.minOn f) best) := by
  induction tail generalizing best i j with
  | nil => exact selected
  | cons y ys ih =>
    have next (k : Nat) : full[j+1+k]? = ys[k]? := by
      rw [Nat.succ_add]
      exact suffix (k+1)
    rw [_root_.List.minIdxOn.go, _root_.List.foldl_cons]
    by_cases keep : f best ≤ f y
    · rw [ite_eq_left keep, _root_.minOn_eq_left keep]
      exact ih best i (j+1) selected next
    · rw [ite_eq_right keep, _root_.minOn_eq_right keep]
      exact ih y j (j+1) (suffix 0) next

public theorem List.getElem_minIdxOn : type_of% @_root_.List.getElem_minIdxOn := by
  intro β α _ _ _ f xs nonempty
  cases xs with
  | nil => exact (nonempty rfl).elim
  | cons x xs =>
    apply Option.some.inj
    refine (_root_.List.getElem?_eq_getElem (_root_.List.minIdxOn_lt_length (f := f) nonempty)).symm.trans ?_
    apply minIdxLookup f (x :: xs) xs x 0 1 rfl
    intro k
    rw [Nat.one_add, _root_.List.getElem?_cons_succ]

public theorem List.minOn_eq_head : type_of% @_root_.List.minOn_eq_head := by
  intro β α _ _ _ xs f nonempty below
  cases xs with
  | nil => exact (nonempty rfl).elim
  | cons x xs =>
    change xs.foldl (_root_.minOn f) x = x
    have within (a) (mem : a ∈ xs) : f x ≤ f a := below a (.tail _ mem)
    clear below nonempty
    induction xs with
    | nil => rfl
    | cons y ys ih =>
      rw [_root_.List.foldl_cons, _root_.minOn_eq_left (within y _root_.List.mem_cons_self)]
      exact ih (fun z mem => within z (.tail _ mem))

/-- After a least element is read, every later comparison retains an index no
larger than its position. No decision on equality of list elements is needed. -/
private theorem indexBeforeMinimum [LE β] [DecidableLE β] [Std.IsLinearPreorder β]
    (f : α → β) (pre post : _root_.List α) (best y : α) (i j : Nat)
    (bound : i ≤ j + pre.length) (least : ∀ z ∈ post, f y ≤ f z) :
    _root_.List.minIdxOn.go f best i j (pre ++ y :: post) ≤ j + pre.length := by
  induction pre generalizing best i j with
  | nil =>
    change _root_.List.minIdxOn.go f best i j (y :: post) ≤ j
    rw [_root_.List.minIdxOn.go]
    by_cases keep : f best ≤ f y
    · rw [ite_eq_left keep, (private_decl% @_root_.List.minIdxOn.go_eq_of_forall_le)
        (f := f) (fun z mem => Std.IsPreorder.le_trans _ _ _ keep (least z mem))]
      exact bound
    · rw [ite_eq_right keep, (private_decl% @_root_.List.minIdxOn.go_eq_of_forall_le) least]
      exact Nat.le_refl _
  | cons a pre ih =>
    rw [_root_.List.cons_append, _root_.List.minIdxOn.go, _root_.List.length_cons, ← Nat.add_assoc]
    have offset : j + pre.length + 1 = j + 1 + pre.length := (Nat.succ_add j pre.length).symm
    rw [offset]
    by_cases keep : f best ≤ f a
    · rw [ite_eq_left keep]
      apply ih
      exact offset ▸ bound
    · rw [ite_eq_right keep]
      apply ih
      exact Nat.le_trans (Nat.le_succ _) (Nat.le_add_right _ _)

public theorem List.minIdxOn_le_of_apply_getElem_le_apply_minOn :
    type_of% @_root_.List.minIdxOn_le_of_apply_getElem_le_apply_minOn := by
  intro β α _ _ _ f xs nonempty k bound minimum
  cases xs with
  | nil => exact (nonempty rfl).elim
  | cons x xs =>
    have least (z) (mem : z ∈ xs) := Std.IsPreorder.le_trans _ _ _ minimum
      (_root_.List.apply_minOn_le_of_mem (f := f) (_root_.List.mem_cons_of_mem x mem))
    cases k with
    | zero =>
      change _root_.List.minIdxOn.go f x 0 1 xs ≤ 0
      change ∀ z ∈ xs, f x ≤ f z at least
      rw [(private_decl% @_root_.List.minIdxOn.go_eq_of_forall_le) (f := f) least]
      exact Nat.le_refl _
    | succ k =>
      have hk := Nat.lt_of_succ_lt_succ bound
      let pre := xs.take k
      let post := xs.drop (k+1)
      have split : pre ++ xs[k] :: post = xs :=
        (_root_.List.getElem_cons_drop hk) ▸ _root_.List.take_append_drop k xs
      have width : 1 + pre.length = k + 1 := by
        rw [Nat.one_add, _root_.List.length_take_of_le (Nat.le_of_lt hk)]
      have before := indexBeforeMinimum f pre post x xs[k] 0 1 (Nat.zero_le _)
        (fun z mem => least z (_root_.List.mem_of_mem_drop mem))
      rw [split, width] at before
      exact before

/-- Each comparison is independent of which decision procedure supplied it. -/
public theorem minOn.congr_simp : type_of% @_root_.minOn.congr_simp := by
  intro β α le d₁ d₂ f g rfl x x' rfl y y' rfl
  by_cases yes : f x ≤ f y
  · exact (@_root_.minOn_eq_left β α le d₁ f x y yes).trans (@_root_.minOn_eq_left β α le d₂ f x y yes).symm
  · exact (@_root_.minOn_eq_right β α le d₁ f x y yes).trans (@_root_.minOn_eq_right β α le d₂ f x y yes).symm

public theorem maxOn.congr_simp : type_of% @_root_.maxOn.congr_simp := by
  intro β α le d₁ d₂ f g rfl x x' rfl y y' rfl
  by_cases yes : f y ≤ f x
  · exact (@_root_.maxOn_eq_left β α le d₁ f x y yes).trans (@_root_.maxOn_eq_left β α le d₂ f x y yes).symm
  · exact (@_root_.maxOn_eq_right β α le d₁ f x y yes).trans (@_root_.maxOn_eq_right β α le d₂ f x y yes).symm

public theorem List.minOn.congr_simp : type_of% @_root_.List.minOn.congr_simp := by
  intro β α le d₁ d₂ f g rfl xs ys rfl nonempty
  cases xs with
  | nil => exact (nonempty rfl).elim
  | cons x xs =>
    change xs.foldl (@_root_.minOn _ _ _ d₁ f) x = xs.foldl (@_root_.minOn _ _ _ d₂ f) x
    clear nonempty
    induction xs generalizing x with
    | nil => rfl
    | cons y ys ih =>
      rw [_root_.List.foldl_cons, _root_.List.foldl_cons]
      exact (ih _).trans (congrArg (ys.foldl (@_root_.minOn _ _ _ d₂ f))
        (@OmegaChecks.InitPort.Alternatives.minOn.congr_simp _ _ _ d₁ d₂ f f rfl x x rfl y y rfl))

public theorem List.maxOn.congr_simp : type_of% @_root_.List.maxOn.congr_simp := by
  intro β α le d₁ d₂ f g rfl xs ys rfl nonempty
  exact @List.minOn.congr_simp β α le.opposite
    (@Std.OppositeOrderInstances.instDecidableLEOpposite _ le d₁)
    (@Std.OppositeOrderInstances.instDecidableLEOpposite _ le d₂)
    f f rfl xs xs rfl nonempty

public theorem List.minOn?.congr_simp : type_of% @_root_.List.minOn?.congr_simp := by
  intro β α le d₁ d₂ f g rfl xs ys rfl
  cases xs with
  | nil => rfl
  | cons x xs =>
    exact congrArg some (@List.minOn.congr_simp _ _ _ d₁ d₂ f f rfl _ _ rfl (_root_.List.cons_ne_nil x xs))

public theorem List.maxOn?.congr_simp : type_of% @_root_.List.maxOn?.congr_simp := by
  intro β α le d₁ d₂ f g rfl xs ys rfl
  exact @List.minOn?.congr_simp β α le.opposite
    (@Std.OppositeOrderInstances.instDecidableLEOpposite _ le d₁)
    (@Std.OppositeOrderInstances.instDecidableLEOpposite _ le d₂)
    f f rfl xs xs rfl

private theorem indexDecisionCongr [le : LE β] (d₁ d₂ : DecidableLE β)
    (f : α → β) (xs : _root_.List α) (x : α) (i j : Nat) :
    @_root_.List.minIdxOn.go β α le d₁ f x i j xs =
      @_root_.List.minIdxOn.go β α le d₂ f x i j xs := by
  induction xs generalizing x i j with
  | nil => rfl
  | cons y ys ih =>
    letI := d₁
    by_cases keep : f x ≤ f y
    · simp only [_root_.List.minIdxOn.go, ite_eq_left keep]
      exact ih x i (j+1)
    · simp only [_root_.List.minIdxOn.go, ite_eq_right keep]
      exact ih y j (j+1)

public theorem List.minIdxOn.go.congr_simp.{u, v} :
    type_of% (private_decl% @_root_.List.minIdxOn.go.congr_simp.{u, v}) := by
  intro β α le d₁ d₂ f _ rfl x _ rfl i _ rfl j _ rfl xs _ rfl
  exact indexDecisionCongr d₁ d₂ f xs x i j

public theorem List.combineMinIdxOn.congr_simp.{u, v} :
    type_of% (private_decl% @_root_.List.combineMinIdxOn.congr_simp.{u, v}) := by
  intro β α le d₁ d₂ f _ rfl xs _ rfl ys _ rfl i _ rfl j _ rfl hi hj
  letI := d₁
  unfold _root_.List.combineMinIdxOn
  by_cases keep : f xs[i] ≤ f ys[j]
  · rw [ite_eq_left keep, ite_eq_left keep]
  · rw [ite_eq_right keep, ite_eq_right keep]

public theorem List.minIdxOn.congr_simp : type_of% @_root_.List.minIdxOn.congr_simp := by
  intro β α le d₁ d₂ f g rfl xs ys rfl nonempty
  cases xs with
  | nil => exact (nonempty rfl).elim
  | cons x xs => exact indexDecisionCongr d₁ d₂ f xs x 0 1

public theorem List.minIdxOn?.congr_simp : type_of% @_root_.List.minIdxOn?.congr_simp := by
  intro β α le d₁ d₂ f g rfl xs ys rfl
  cases xs with
  | nil => rfl
  | cons x xs => exact congrArg some (indexDecisionCongr d₁ d₂ f xs x 0 1)

public theorem List.maxIdxOn.congr_simp : type_of% @_root_.List.maxIdxOn.congr_simp := by
  intro β α le d₁ d₂ f g rfl xs ys rfl nonempty
  exact @List.minIdxOn.congr_simp β α le.opposite
    (@Std.OppositeOrderInstances.instDecidableLEOpposite _ le d₁)
    (@Std.OppositeOrderInstances.instDecidableLEOpposite _ le d₂)
    f f rfl xs xs rfl nonempty

public theorem List.maxIdxOn?.congr_simp : type_of% @_root_.List.maxIdxOn?.congr_simp := by
  intro β α le d₁ d₂ f g rfl xs ys rfl
  exact @List.minIdxOn?.congr_simp β α le.opposite
    (@Std.OppositeOrderInstances.instDecidableLEOpposite _ le d₁)
    (@Std.OppositeOrderInstances.instDecidableLEOpposite _ le d₂)
    f f rfl xs xs rfl

public theorem List.minOn?_append : type_of% @_root_.List.minOn?_append := by
  intro β α _ _ _ xs ys f
  cases xs with
  | nil => cases ys <;> rfl
  | cons x xs =>
    cases ys with
    | nil => rw [List.append_nil]; rfl
    | cons y ys =>
      rw [List.minOn?_eq_some_minOn (xs := (x :: xs) ++ y :: ys) (fun h => nomatch h),
        List.minOn?_eq_some_minOn (List.cons_ne_nil _ _), List.minOn?_eq_some_minOn (List.cons_ne_nil _ _)]
      exact congrArg some (List.minOn_append (List.cons_ne_nil _ _) (List.cons_ne_nil _ _))

public theorem List.maxOn?_append : type_of% @_root_.List.maxOn?_append := by
  intro β α _ _ _ xs ys f
  cases xs with
  | nil => cases ys <;> rfl
  | cons x xs =>
    cases ys with
    | nil => rw [List.append_nil]; rfl
    | cons y ys =>
      rw [List.maxOn?_eq_some_maxOn (xs := (x :: xs) ++ y :: ys) (fun h => nomatch h),
        List.maxOn?_eq_some_maxOn (List.cons_ne_nil _ _), List.maxOn?_eq_some_maxOn (List.cons_ne_nil _ _)]
      exact congrArg some (List.maxOn_append (List.cons_ne_nil _ _) (List.cons_ne_nil _ _))

public theorem List.maxOn?_cons : type_of% @_root_.List.maxOn?_cons := by
  intro β α _ _ _ f x xs
  cases xs with
  | nil => rfl
  | cons y ys =>
    rw [List.maxOn?_cons_eq_some_maxOn, List.maxOn?_cons_eq_some_maxOn]
    exact congrArg some (List.maxOn_cons ..)

end OmegaChecks.InitPort.Alternatives
