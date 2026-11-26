module

public import Init.Data.Array.Basic
public import Init.Data.Nat.Basic
import all Init.Data.Array.Basic
import Init.Data.Array.Lemmas

/-! List-backed implementations and induction proofs for the pinned array interfaces. -/

namespace OmegaChecks.InitPort.Alternatives

@[expose] public def Array.eraseIdx {α : Type u} (xs : _root_.Array α) (i : Nat) (_h : i < xs.size) :
    _root_.Array α := ⟨xs.toList.eraseIdx i⟩

@[expose] public def Array.eraseIdxIfInBounds {α : Type u} (xs : _root_.Array α) (i : Nat) :
    _root_.Array α := ⟨xs.toList.eraseIdx i⟩

public theorem Array.size_eraseIdx {α : Type u} {xs : _root_.Array α} (i : Nat) (h : i < xs.size) :
    (Array.eraseIdx xs i h).size = xs.size - 1 :=
  (List.rec (motive := fun xs : List α => ∀ j, j < xs.length →
      (xs.eraseIdx j).length = xs.length - 1)
    (fun j bound => False.elim (Nat.not_succ_le_zero j bound))
    (fun a tail ih j => Nat.casesOn (motive := fun j => j < (a :: tail).length →
        ((a :: tail).eraseIdx j).length = (a :: tail).length - 1) j
      (fun _ => (Nat.add_one_sub_one tail.length).symm)
      (fun k bound =>
        have fits : k < tail.length := Nat.le_of_succ_le_succ bound
        have nonzero : tail.length ≠ 0 := fun e =>
          Nat.not_succ_le_zero k (Eq.subst (motive := (k < ·)) e fits)
        (congrArg Nat.succ (ih k fits)).trans
          ((Nat.succ_pred_eq_of_ne_zero nonzero).trans (Nat.add_one_sub_one tail.length).symm))) xs.toList) i h

public theorem Array.toList_eraseIdx {α : Type u} {xs : _root_.Array α} {i : Nat} {h : i < xs.size} :
    (Array.eraseIdx xs i h).toList = xs.toList.eraseIdx i := rfl

public theorem List.eraseIdx_toArray {α : Type u} (l : _root_.List α) (i : Nat) (h : i < l.toArray.size) :
    Array.eraseIdx l.toArray i h = (l.eraseIdx i).toArray := rfl

public theorem List.eraseIdxIfInBounds_toArray {α : Type u} (l : _root_.List α) (i : Nat) :
    Array.eraseIdxIfInBounds l.toArray i = (l.eraseIdx i).toArray := rfl

public theorem Array.eraseIdx_eq_eraseIdxIfInBounds {α : Type u} {xs : _root_.Array α}
    {i : Nat} (h : i < xs.size) : Array.eraseIdx xs i h = Array.eraseIdxIfInBounds xs i := rfl

private theorem foldLeftLoop {α : Type u} {β : Type v} (f : β → α → β) (xs : _root_.Array α)
    (i j : Nat) (h : xs.size ≤ i + j) (b : β) :
    (_root_.Array.foldlM.loop (m := Id) (fun b a => pure (f b a)) xs xs.size
      (Nat.le_refl _) i j b).run = (xs.toList.drop j).foldl f b := by
  induction i generalizing j b with
  | zero =>
    have done : xs.size ≤ j := (Nat.zero_add j) ▸ h
    rw [List.drop_eq_nil_of_le done]
    unfold _root_.Array.foldlM.loop
    simp only [dite_eq_right (Nat.not_lt_of_ge done)]
    rfl
  | succ i ih =>
    unfold _root_.Array.foldlM.loop
    by_cases bound : j < xs.size
    · rw [dite_eq_left bound]
      have room : xs.size ≤ i + (j + 1) := Eq.subst (motive := (xs.size ≤ ·)) (Nat.succ_add i j) h
      exact (ih (j+1) room (f b xs[j])).trans
        (congrArg (fun l => List.foldl f b l) (List.getElem_cons_drop (as := xs.toList) bound))
    · have done : xs.size ≤ j := Nat.ge_of_not_lt bound
      rw [dite_eq_right bound, List.drop_eq_nil_of_le done]
      rfl

public theorem Array.foldl_toList : type_of% @_root_.Array.foldl_toList := by
  intro α β f b xs
  unfold _root_.Array.foldl _root_.Array.foldlM
  rw [dite_eq_left (Nat.le_refl _)]
  exact (foldLeftLoop f xs xs.size 0 (Nat.le_refl _) b).symm

private theorem takeNext {α : Type u} (xs : List α) (i : Nat) (h : i < xs.length) :
    xs.take i ++ [xs[i]] = xs.take (i+1) := by
  induction xs generalizing i with
  | nil => exact (Nat.not_succ_le_zero _ h).elim
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ k => exact congrArg (x :: ·) (ih k (Nat.le_of_succ_le_succ h))

private theorem takeAll {α : Type u} (xs : List α) : xs.take xs.length = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => exact congrArg (x :: ·) ih

private theorem foldRightLoop {α : Type u} {β : Type v} (f : α → β → β) (xs : _root_.Array α)
    (i : Nat) (h : i ≤ xs.size) (b : β) :
    (_root_.Array.foldrM.fold (m := Id) (fun a b => pure (f a b)) xs 0 i h b).run =
      (xs.toList.take i).foldr f b := by
  induction i generalizing b with
  | zero =>
    unfold _root_.Array.foldrM.fold
    rfl
  | succ i ih =>
    unfold _root_.Array.foldrM.fold
    have within : i < xs.size := h
    have appended := takeNext xs.toList i within
    exact (ih (Nat.le_of_lt within) (f xs[i] b)).trans ((List.foldr_append (l := xs.toList.take i)
      (l' := [xs[i]]) (f := f) (b := b)).symm.trans (congrArg (fun l => l.foldr f b) appended))

public theorem Array.foldr_toList : type_of% @_root_.Array.foldr_toList := by
  intro α β f b xs
  unfold _root_.Array.foldr _root_.Array.foldrM
  rw [dite_eq_left (Nat.le_refl _)]
  by_cases pos : 0 < xs.size
  · rw [ite_eq_left pos]
    exact (congrArg (fun l => l.foldr f b) (takeAll xs.toList).symm).trans
      (foldRightLoop f xs xs.size (Nat.le_refl _) b).symm
  · rw [ite_eq_right pos]
    have len : xs.toList.length = 0 := Nat.eq_zero_of_not_pos pos
    have empty : xs.toList = [] := List.eq_nil_of_length_eq_zero len
    exact congrArg (fun l => l.foldr f b) empty

public theorem Array.mem_map : type_of% @_root_.Array.mem_map := by
  intro α β b f xs
  have lists := _root_.Array.toList_map (xs := xs) (f := f)
  constructor
  · intro h
    obtain ⟨a, m, e⟩ := List.mem_map.mp
      (Eq.subst (motive := (b ∈ ·)) lists (Array.mem_def.mp h))
    exact ⟨a, Array.mem_def.mpr m, e⟩
  · intro ⟨a, m, e⟩
    exact Array.mem_def.mpr (Eq.subst (motive := (b ∈ ·)) lists.symm
      (List.mem_map.mpr ⟨a, Array.mem_def.mp m, e⟩))

private theorem flattenFold {α : Type u} (as : List (_root_.Array α)) (acc : _root_.Array α) :
    (as.foldl (· ++ ·) acc).toList = acc.toList ++ (as.map _root_.Array.toList).flatten := by
  induction as generalizing acc with
  | nil => exact (List.append_nil acc.toList).symm
  | cons xs rest ih =>
    exact (ih (acc ++ xs)).trans
      ((congrArg (· ++ (rest.map _root_.Array.toList).flatten) _root_.Array.toList_append).trans
        (List.append_assoc ..))

public theorem Array.toList_flatten : type_of% @_root_.Array.toList_flatten := by
  intro α xss
  exact (congrArg _root_.Array.toList (Array.foldl_toList (fun acc xs : _root_.Array α => acc ++ xs)).symm).trans
    (flattenFold xss.toList #[])

private theorem pushTail {α : Type u} (acc : _root_.Array α) (x : α) (rest : List α) :
    (acc.push x).toList ++ rest = acc.toList ++ x :: rest :=
  (congrArg (· ++ rest) _root_.Array.toList_push).trans (List.append_assoc ..)

private theorem filterFold {α : Type u} (p : α → Bool) (xs : List α) (acc : _root_.Array α) :
    (xs.foldl (fun out a => if p a then out.push a else out) acc).toList =
      acc.toList ++ xs.filter p := by
  induction xs generalizing acc with
  | nil => exact (List.append_nil acc.toList).symm
  | cons a xs ih =>
    change (xs.foldl _ (if p a then acc.push a else acc)).toList = _
    by_cases h : p a = true
    · rw [ite_eq_left h, List.filter_cons_of_pos h]
      exact (ih (acc.push a)).trans (pushTail acc a _)
    · rw [ite_eq_right h, List.filter_cons_of_neg h]
      exact ih acc

public theorem Array.toList_filter' : type_of% @_root_.Array.toList_filter' := by
  intro α p xs stop eq
  cases eq
  exact (congrArg _root_.Array.toList (Array.foldl_toList (fun acc a => if p a then acc.push a else acc)).symm).trans
    (filterFold p xs.toList #[])

private def selectStep {α : Type u} {β : Type v} (f : α → Option β) (acc : _root_.Array β) (a : α) :
    _root_.Array β :=
  match f a with
  | some b => acc.push b
  | none => acc

private theorem filterMapFold {α : Type u} {β : Type v} (f : α → Option β)
    (xs : List α) (acc : _root_.Array β) :
    (xs.foldl (selectStep f) acc).toList = acc.toList ++ xs.filterMap f := by
  induction xs generalizing acc with
  | nil => exact (List.append_nil acc.toList).symm
  | cons a xs ih =>
    change (xs.foldl _ (selectStep f acc a)).toList = _
    cases h : f a with
    | none =>
      rw [selectStep, h, List.filterMap_cons_none h]
      exact ih acc
    | some b =>
      rw [selectStep, h, List.filterMap_cons_some h]
      exact (ih (acc.push b)).trans (pushTail acc b _)

public theorem Array.toList_filterMap' : type_of% @_root_.Array.toList_filterMap' := by
  intro α β f xs stop eq
  cases eq
  exact (congrArg _root_.Array.toList (Array.foldl_toList (selectStep f)).symm).trans
    (filterMapFold f xs.toList #[])

public theorem Array.toList_filterMap : type_of% @_root_.Array.toList_filterMap := by
  intro α β f xs
  exact Array.toList_filterMap' rfl

end OmegaChecks.InitPort.Alternatives
