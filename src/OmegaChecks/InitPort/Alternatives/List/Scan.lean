module
import all Init.Data.List.Scan.Basic
public import Init.Data.List.Scan.Lemmas

namespace OmegaChecks.InitPort.Alternatives

private theorem scanGoAppend (f : β → α → β) (xs : List α) (b : β) (acc tail : List β) :
    List.scanAuxM.go (m := Id) f xs b (acc ++ tail) =
      (List.scanAuxM.go (m := Id) f xs b acc).run ++ tail := by
  induction xs generalizing b acc with
  | nil => rfl
  | cons x xs ih => exact ih (f b x) (b :: acc)

public theorem List.scanl_cons : type_of% @_root_.List.scanl_cons := by
  intro β α b x xs f
  change (List.scanAuxM.go (m := Id) f xs (f b x) [b]).reverse = _
  exact (congrArg List.reverse (scanGoAppend f xs (f b x) [] [b])).trans (List.reverse_append ..)

public theorem List.scanr_eq_scanl_reverse : type_of% @_root_.List.scanr_eq_scanl_reverse := by
  intros
  exact (List.reverse_reverse _).symm

private theorem scanPureGo [Monad m] [LawfulMonad m] (f : β → α → β) (xs : List α)
    (b : β) (acc : List β) :
    List.scanAuxM.go (m := m) (fun a x => pure (f a x)) xs b acc =
      pure (List.scanAuxM.go (m := Id) f xs b acc) := by
  induction xs generalizing b acc with
  | nil => rfl
  | cons x xs ih =>
    change (pure (f b x) >>= _) = _
    rw [pure_bind]
    exact ih (f b x) (b :: acc)

public theorem List.scanlM_pure : type_of% @_root_.List.scanlM_pure := by
  intros
  unfold _root_.List.scanlM List.scanAuxM
  rw [scanPureGo, map_pure]
  rfl

public theorem List.scanrM_pure : type_of% @_root_.List.scanrM_pure := by
  intros
  exact scanPureGo _ _ _ _

public theorem List.length_scanl : type_of% @_root_.List.length_scanl := by
  intro β α b xs f
  induction xs generalizing b with
  | nil => rfl
  | cons x xs ih =>
    rw [List.scanl_cons]
    exact congrArg Nat.succ (ih (b := f b x))

public theorem List.scanl_eq_scanr_reverse : type_of% @_root_.List.scanl_eq_scanr_reverse := by
  intros
  rw [List.scanr_eq_scanl_reverse, List.reverse_reverse, List.reverse_reverse]
  rfl

public theorem List.getElem?_scanr : type_of% @_root_.List.getElem?_scanr := by
  intro α β b xs i f
  split
  next h =>
    have index : i < (xs.scanr f b).length := (List.length_scanr (f := f) (init := b) (as := xs)).symm ▸ h
    exact (List.getElem?_eq_getElem index).trans (congrArg some (List.getElem_scanr index))
  next h =>
    apply getElem?_neg
    exact fun index => h ((List.length_scanr (f := f) (init := b) (as := xs)) ▸ index)

private theorem scanGoMap [Monad m] (f : α → γ) (g : β → γ → m β) (xs : List α) :
    List.scanAuxM.go g (xs.map f) = List.scanAuxM.go (fun b x => g b (f x)) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change (fun b acc => g b (f x) >>= fun next => List.scanAuxM.go g (xs.map f) next (b :: acc)) = _
    rw [ih]
    rfl

public theorem List.scanlM_map : type_of% @_root_.List.scanlM_map := by
  intros
  unfold _root_.List.scanlM List.scanAuxM
  rw [scanGoMap]

public theorem List.scanrM_map : type_of% @_root_.List.scanrM_map := by
  intros
  unfold _root_.List.scanrM List.scanAuxM
  rw [← List.map_reverse, scanGoMap]
  rfl

public theorem List.head_scanl : type_of% @_root_.List.head_scanl := by
  intro β α b xs f h
  exact Option.some.inj ((List.head?_eq_some_head h).symm.trans List.head?_scanl)

public theorem List.getElem?_succ_scanl : type_of% @_root_.List.getElem?_succ_scanl := by
  intro β α b xs i f
  induction xs generalizing b i with
  | nil => cases i <;> rfl
  | cons x xs ih =>
    rw [List.scanl_cons]
    cases i with
    | zero => exact List.getElem?_scanl_zero
    | succ i => exact ih

end OmegaChecks.InitPort.Alternatives
