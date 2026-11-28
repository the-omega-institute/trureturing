module
public import OmegaChecks.InitPort.Alternatives.BoolSearch

public import Init.Data.List.Monadic
import all Init.Data.List.Control
import Init.Data.List.Attach
import all Init.Data.List.OfFn

/-! Monadic traversals, folds, and dependent elements of a list. -/

namespace OmegaChecks.InitPort.Alternatives

public theorem List.mapM_pure : type_of% @_root_.List.mapM_pure := by
  intro m α β mon law xs f
  have loop (xs : List α) (acc : List β) :
      _root_.List.mapM.loop (m := m) (fun x => pure (f x)) xs acc =
        pure (acc.reverse ++ xs.map f) := by
    induction xs generalizing acc with
    | nil => exact congrArg pure (List.append_nil acc.reverse).symm
    | cons a as ih =>
      rw [List.mapM.loop, pure_bind, ih, List.reverse_cons, List.append_assoc]
      rfl
  exact loop xs []

public theorem List.anyM_pure {m : Type → Type u} {α : Type v} [Monad m] [LawfulMonad m]
    {f : α → Bool} {xs : List α} : List.anyM (m := m) (fun a => pure (f a)) xs = pure (xs.any f) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    rw [List.anyM_cons, pure_bind, _root_.List.any_cons]
    cases tested : f a with
    | false => exact ih
    | true => exact rfl

public theorem List.allM_pure {m : Type → Type u} {α : Type v} [Monad m] [LawfulMonad m]
    {f : α → Bool} {xs : List α} : List.allM (m := m) (fun a => pure (f a)) xs = pure (xs.all f) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    rw [List.allM_cons, pure_bind, _root_.List.all_cons]
    cases tested : f a with
    | false => exact rfl
    | true => exact ih

public theorem List.forIn_pure_yield_eq_foldl : type_of% @_root_.List.forIn_pure_yield_eq_foldl := by
  intro m α β mon law l f init
  let body (a : α) (_ : a ∈ l) (b : β) : m (ForInStep β) := pure (.yield (f a b))
  have loop (xs : List α) (b : β) (h : ∃ ys, ys ++ xs = l) :
      List.forIn'.loop l body xs b h = pure (xs.foldl (fun b a => f a b) b) := by
    induction xs generalizing b with
    | nil => rfl
    | cons a xs ih =>
      rw [List.forIn'.loop]
      dsimp only [body]
      rw [pure_bind]
      exact ih _ _
  exact loop l init ⟨[], rfl⟩

public theorem List.forIn'_pure_yield_eq_foldl : type_of% @_root_.List.forIn'_pure_yield_eq_foldl := by
  intro m α β mon law l f init
  let body (a : α) (ha : a ∈ l) (b : β) : m (ForInStep β) := pure (.yield (f a ha b))
  have mem (xs : List α) (h : ∃ ys, ys ++ xs = l) (a : α) (ha : a ∈ xs) : a ∈ l := by
    obtain ⟨ys, rfl⟩ := h
    exact List.mem_append_right ys ha
  have loop (xs : List α) (b : β) (h : ∃ ys, ys ++ xs = l) :
      List.forIn'.loop l body xs b h =
        pure ((xs.attachWith (· ∈ l) (mem xs h)).foldl (fun b a => f a.1 a.2 b) b) := by
    induction xs generalizing b with
    | nil => rfl
    | cons a xs ih =>
      rw [List.forIn'.loop]
      dsimp only [body]
      rw [pure_bind, List.attachWith_cons]
      exact ih _ _
  exact loop l init ⟨[], rfl⟩


public theorem List.forM_map : type_of% @_root_.List.forM_map := by
  intro m α β mon law xs g f
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    exact congrArg (fun tail => f (g a) >>= fun _ => tail) ih

public theorem List.forM_append : type_of% @_root_.List.forM_append := by
  intro m α mon law xs ys f
  induction xs with
  | nil => rw [List.nil_append, List.forM_nil, pure_bind]
  | cons a xs ih =>
    rw [List.cons_append, List.forM_cons, List.forM_cons, bind_assoc]
    exact congrArg (fun tail => f a >>= fun _ => tail) ih

public theorem List.foldlM_map : type_of% @_root_.List.foldlM_map := by
  intro m β₁ β₂ α mon f g xs init
  have loop (xs : List β₁) :
      (fun b => (xs.map f).foldlM g b) = fun b => xs.foldlM (fun b a => g b (f a)) b := by
    induction xs with
    | nil => rfl
    | cons a xs ih => exact congrArg (fun tail b => g b (f a) >>= tail) ih
  exact congrFun (loop xs) init

public theorem List.foldrM_map : type_of% @_root_.List.foldrM_map := by
  intros
  rw [List.foldrM, ← List.map_reverse, List.foldlM_map]
  rfl

public theorem List.foldlM_attachWith : type_of% @_root_.List.foldlM_attachWith := by
  intros
  rw [List.attachWith_eq_map_attach, List.foldlM_map]

public theorem List.foldrM_attachWith : type_of% @_root_.List.foldrM_attachWith := by
  intros
  rw [List.attachWith_eq_map_attach, List.foldrM_map]

public theorem List.foldlM_unattach : type_of% @_root_.List.foldlM_unattach := by
  intros
  apply List.foldlM_map

public theorem List.foldrM_unattach : type_of% @_root_.List.foldrM_unattach := by
  intros
  apply List.foldrM_map

public theorem List.mapM_map : type_of% @_root_.List.mapM_map := by
  intro m α β γ mon law f g xs
  have loop (xs : List α) : List.mapM.loop g (xs.map f) = List.mapM.loop (g ∘ f) xs := by
    induction xs with
    | nil => rfl
    | cons a xs ih => exact congrArg (fun tail acc => g (f a) >>= fun b => tail (b :: acc)) ih
  exact congrFun (loop xs) []

public theorem List.mapM_subtype : type_of% @_root_.List.mapM_subtype := by
  intro m α β mon law p xs f g hf
  have loop (xs : List (Subtype p)) : List.mapM.loop f xs = List.mapM.loop g xs.unattach := by
    induction xs with
    | nil => rfl
    | cons a xs ih =>
      calc
        _ = (fun acc => f a >>= fun b => List.mapM.loop g xs.unattach (b :: acc)) :=
          congrArg (fun tail acc => f a >>= fun b => tail (b :: acc)) ih
        _ = _ := congrArg (fun v acc => v >>= fun b => List.mapM.loop g xs.unattach (b :: acc)) (hf a.1 a.2)
  exact congrFun (loop xs) []

public theorem List.filterMapM_subtype : type_of% @_root_.List.filterMapM_subtype := by
  intro m α β mon law p xs f g hf
  have loop (xs : List (Subtype p)) : List.filterMapM.loop f xs = List.filterMapM.loop g xs.unattach := by
    induction xs with
    | nil => rfl
    | cons a xs ih =>
      let step (v : m (Option β)) (tail : List β → m (List β)) (acc : List β) :=
        v >>= fun | none => tail acc | some b => tail (b :: acc)
      exact (congrArg (step (f a)) ih).trans
        (congrArg (fun v => step v (List.filterMapM.loop g xs.unattach)) (hf a.1 a.2))
  exact congrFun (loop xs) []

public theorem List.flatMapM_subtype : type_of% @_root_.List.flatMapM_subtype := by
  intro m α β mon law p xs f g hf
  have loop (xs : List (Subtype p)) : List.flatMapM.loop f xs = List.flatMapM.loop g xs.unattach := by
    induction xs with
    | nil => rfl
    | cons a xs ih =>
      let step (v : m (List β)) (tail : List (List β) → m (List β)) (acc : List (List β)) :=
        v >>= fun b => tail (b :: acc)
      exact (congrArg (step (f a)) ih).trans
        (congrArg (fun v => step v (List.flatMapM.loop g xs.unattach)) (hf a.1 a.2))
  exact congrFun (loop xs) []

public theorem List.findM?_pure : type_of% @_root_.List.findM?_pure := by
  intro α m _ _ p xs
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [_root_.List.findM?, pure_bind, List.find?_cons]
    cases p x <;> first | rfl | exact ih

public theorem List.ofFnM_zero : type_of% @_root_.List.ofFnM_zero := by
  intros
  unfold List.ofFnM
  rw [Fin.foldlM_zero, map_pure]
  rfl

private theorem foldPureCons [Monad m] [LawfulMonad m] (f : Fin n → α) (xs : List α) :
    Fin.foldlM n (m := m) (fun acc j => (· :: acc) <$> pure (f j)) xs =
      Fin.foldlM n (fun acc j => pure (f j :: acc)) xs := by
  induction n generalizing xs with
  | zero => rw [Fin.foldlM_zero, Fin.foldlM_zero]
  | succ n ih =>
    rw [Fin.foldlM_succ, Fin.foldlM_succ]
    dsimp only
    rw [map_pure, pure_bind, pure_bind]
    exact ih (fun j => f j.succ) _

public theorem List.ofFnM_pure_comp : type_of% @_root_.List.ofFnM_pure_comp := by
  intro m α _ _ n f
  unfold List.ofFnM
  change List.reverse <$> (Fin.foldlM n (m := m) (fun acc j => (· :: acc) <$> pure (f j)) []) = _
  rw [foldPureCons]
  rw [Fin.foldlM_pure, map_pure, Fin.foldl_cons_eq_append, List.append_nil, List.reverse_reverse]

public theorem List.idRun_ofFnM : type_of% @_root_.List.idRun_ofFnM := by
  intro α n f
  change (_root_.List.ofFnM (m := Id) (pure ∘ f)) = _
  exact _root_.List.ofFnM_pure_comp (m := Id)

public theorem List.flatMapM.loop.eq_def : type_of% @_root_.List.flatMapM.loop.eq_def := by
  intro m mon α β f xs acc
  cases xs <;> rfl


public theorem List.foldlM_filterMap : type_of% @_root_.List.foldlM_filterMap := by
  intro m α β γ mon law f g xs init
  let step (b : γ) (a : α) := match f a with | some x => g b x | none => pure b
  have loop (xs : List α) (acc : m γ) :
      (acc >>= (fun b => (xs.filterMap f).foldlM g b)) = acc >>= fun b => xs.foldlM step b := by
    induction xs generalizing acc with
    | nil => rfl
    | cons a xs ih =>
      rw [List.filterMap_cons]
      cases h : f a with
      | none =>
        have head : (fun b => step b a) = pure := by dsimp only [step]; rw [h]
        change (_ >>= _) = acc >>= fun b => step b a >>= fun c => xs.foldlM step c
        rw [← bind_assoc, head, bind_pure]
        exact ih acc
      | some x =>
        have head : (fun b => step b a) = fun b => g b x := by dsimp only [step]; rw [h]
        change (acc >>= fun b => g b x >>= fun c => (xs.filterMap f).foldlM g c) =
          acc >>= fun b => step b a >>= fun c => xs.foldlM step c
        rw [← bind_assoc, ← bind_assoc, head]
        exact ih _
  have result := loop xs (pure init)
  rw [pure_bind, pure_bind] at result
  exact result

public theorem List.foldlM_filter : type_of% @_root_.List.foldlM_filter := by
  intro m α β mon law p g xs init
  let step (b : β) (a : α) := if p a then g b a else pure b
  have loop (xs : List α) (acc : m β) :
      (acc >>= (fun b => (xs.filter p).foldlM g b)) = acc >>= fun b => xs.foldlM step b := by
    induction xs generalizing acc with
    | nil => rfl
    | cons a xs ih =>
      rw [List.filter_cons]
      cases h : p a with
      | false =>
        have head : (fun b => step b a) = pure := by dsimp only [step]; rw [h]; rfl
        change (_ >>= _) = acc >>= fun b => step b a >>= fun c => xs.foldlM step c
        rw [← bind_assoc, head, bind_pure]
        exact ih acc
      | true =>
        have head : (fun b => step b a) = fun b => g b a := by dsimp only [step]; rw [h]; rfl
        change (acc >>= fun b => g b a >>= fun c => (xs.filter p).foldlM g c) =
          acc >>= fun b => step b a >>= fun c => xs.foldlM step c
        rw [← bind_assoc, ← bind_assoc, head]
        exact ih _
  have result := loop xs (pure init)
  rw [pure_bind, pure_bind] at result
  exact result

public theorem List.foldrM_filter : type_of% @_root_.List.foldrM_filter := by
  intros
  rw [List.foldrM, ← List.filter_reverse, List.foldlM_filter]
  rfl

public theorem List.foldrM_filterMap : type_of% @_root_.List.foldrM_filterMap := by
  intros
  rw [List.foldrM, ← List.filterMap_reverse, List.foldlM_filterMap]
  rfl

end OmegaChecks.InitPort.Alternatives
