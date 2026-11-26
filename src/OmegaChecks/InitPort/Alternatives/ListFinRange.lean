module
public import Init.Data.List.FinRange

/-! Indexed enumeration and monadic traversal of finite ranges. -/
namespace OmegaChecks.InitPort.Alternatives

public theorem List.finRange_reverse : type_of% @_root_.List.finRange_reverse := by
  intro n
  apply List.ext_getElem
  · rw [List.length_reverse, List.length_map]
  · intro i hi hj
    rw [List.getElem_reverse hi, List.getElem_map, List.getElem_finRange, List.getElem_finRange]
    apply Fin.ext
    change (List.finRange n).length - 1 - i = n - (i + 1)
    rw [List.length_finRange, Nat.sub_sub]
    exact congrArg (n - ·) (Nat.add_comm 1 i)

private theorem foldlMMapFunction [Monad m] {α : Type _} {β γ : Type _}
    (g : β → γ) (step : α → γ → m α) (l : List β) :
    (fun a => (l.map g).foldlM step a) = fun a => l.foldlM (fun a b => step a (g b)) a := by
  induction l with
  | nil => rfl
  | cons b l ih => exact congrArg (fun cont => fun a => step a (g b) >>= cont) ih

public theorem Fin.foldlM_eq_foldlM_finRange : type_of% @_root_.Fin.foldlM_eq_foldlM_finRange := by
  intro m α n mon f x
  suffices lift : Fin.foldlM n f = fun a => (List.finRange n).foldlM f a from congrFun lift x
  induction n with
  | zero => rw [Fin.foldlM_zero, List.finRange_zero]; rfl
  | succ n ih =>
    rw [Fin.foldlM_succ, List.finRange_succ]
    exact congrArg (fun cont => fun a => f a 0 >>= cont)
      ((ih (fun a i => f a i.succ)).trans (foldlMMapFunction Fin.succ f (List.finRange n)).symm)

public theorem Fin.foldrM_eq_foldrM_finRange : type_of% @_root_.Fin.foldrM_eq_foldrM_finRange := by
  intro m n α mon laws f x
  suffices lift : Fin.foldrM n f = fun a => (List.finRange n).foldrM f a from congrFun lift x
  induction n with
  | zero => rw [Fin.foldrM_zero, List.finRange_zero]; rfl
  | succ n ih =>
    rw [Fin.foldrM_succ_last, List.finRange_succ_last]
    unfold List.foldrM
    rw [List.reverse_concat, ← List.map_reverse]
    exact congrArg (fun cont => fun a => f (Fin.last n) a >>= cont)
      ((ih (fun i a => f i.castSucc a)).trans
        (foldlMMapFunction Fin.castSucc (fun a i => f i a) (List.finRange n).reverse).symm)

end OmegaChecks.InitPort.Alternatives
