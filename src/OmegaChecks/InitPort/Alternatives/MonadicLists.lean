module
public import Init.Data.Array.Monadic
import all Init.Data.Array.Basic
public import Init.Data.List.Monadic
import all Init.Data.List.Control
import Init.Data.List.Attach

/-! Reduction of pure monadic list operations on arbitrary accumulators. -/
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

public theorem List.anyM_pure : type_of% @_root_.List.anyM_pure := by
  intro m α mon law f xs
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.anyM, pure_bind, List.any_cons]
    cases he : f x with
    | false => exact ih
    | true => rfl

public theorem List.allM_pure : type_of% @_root_.List.allM_pure := by
  intro m α mon law f xs
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.allM, pure_bind, List.all_cons]
    cases he : f x with
    | false => rfl
    | true => exact ih

private theorem fixInvariant {A : Sort u} {B : Sort v} (measure : A → Nat) (spec : A → B)
    (action : (x : A) → ((y : A) → measure y < measure x → B) → B)
    (step : ∀ x recur, (∀ y h, recur y h = spec y) → action x recur = spec x) (x : A) :
    WellFounded.Nat.fix measure action x = spec x := by
  have go (n : Nat) (x : A) (hn : measure x < n) :
      WellFounded.Nat.fix.go measure action n x hn = spec x := by
    induction n generalizing x with
    | zero => exact False.elim (Nat.not_lt_zero _ hn)
    | succ n ih => exact step x _ (fun y _ => ih y _)
  exact go _ x _

public theorem Array.mapM_pure : type_of% @_root_.Array.mapM_pure := by
  intro m α β mon law xs f
  let spec (p : (_ : Nat) ×' Array β) : m (Array β) :=
    pure (p.2.toList ++ (xs.toList.drop p.1).map f).toArray
  have run (i : Nat) (acc : Array β) :
      Array.mapM.map (m := m) (fun x => pure (f x)) xs i acc = spec ⟨i, acc⟩ := by
    delta Array.mapM.map Array.mapM.map._unary
    apply fixInvariant _ spec
    rintro ⟨j, bs⟩ recur ih
    dsimp only
    by_cases h : j < xs.size
    · rw [dite_eq_left h, pure_bind, ih]
      dsimp only [spec]
      rw [List.drop_eq_getElem_cons (l := xs.toList) (i := j) h, Array.toList_push,
        List.append_assoc]
      rfl
    · rw [dite_eq_right h]
      dsimp only [spec]
      rw [List.drop_of_length_le (Nat.le_of_not_gt h), List.map_nil, List.append_nil]
  change Array.mapM.map (m := m) (fun x => pure (f x)) xs 0 #[] = _
  rw [run]
  exact congrArg pure (Array.ext' _root_.Array.toList_map.symm)

public theorem Array.map_toList_inj : type_of% @_root_.Array.map_toList_inj := by
  intro m α mon law xs ys
  have cancel (as : m (Array α)) : List.toArray <$> (Array.toList <$> as) = as := by
    rw [Functor.map_map]
    exact id_map' as
  exact ⟨fun h => (cancel xs).symm.trans ((congrArg (fun as => List.toArray <$> as) h).trans (cancel ys)),
    congrArg (fun as => Array.toList <$> as)⟩

public theorem Array.foldlM_wfParam : type_of% @_root_.Array.foldlM_wfParam := by
  intros
  rw [Array.unattach_attach]
  rfl

public theorem Array.foldrM_wfParam : type_of% @_root_.Array.foldrM_wfParam := by
  intros
  rw [Array.unattach_attach]
  rfl

public theorem Array.filterMapM_wfParam : type_of% @_root_.Array.filterMapM_wfParam := by
  intros
  rw [Array.unattach_attach]
  rfl

public theorem Array.flatMapM_wfParam : type_of% @_root_.Array.flatMapM_wfParam := by
  intros
  rw [Array.unattach_attach]
  rfl


private theorem arrayAnyPure [Monad m] [LawfulMonad m] (xs : Array α)
    (q : α → m Bool) (p : α → Bool) (h : ∀ a, q a = pure (p a)) :
    xs.anyM q = pure (xs.toList.any p) := by
  let spec (i : Nat) : m Bool := pure ((xs.toList.drop i).any p)
  have run (i : Nat) : Array.anyM.loop q xs xs.size (Nat.le_refl _) i = spec i := by
    delta Array.anyM.loop
    apply fixInvariant _ spec
    intro j recur ih
    dsimp only
    by_cases hj : j < xs.size
    · rw [dite_eq_left hj, h, pure_bind]
      dsimp only [spec]
      rw [List.drop_eq_getElem_cons (l := xs.toList) (i := j) hj, List.any_cons]
      change (if p xs[j] = true then _ else _) = pure (p xs[j] || _)
      cases hp : p xs[j] with
      | false => exact ih _ _
      | true => rfl
    · rw [dite_eq_right hj]
      dsimp only [spec]
      rw [List.drop_of_length_le (Nat.le_of_not_gt hj)]
      rfl
  rw [Array.anyM, dite_eq_left (Nat.le_refl _)]
  exact run 0

public theorem Array.anyM_pure : type_of% @_root_.Array.anyM_pure := by
  intro m α mon law p xs
  exact (arrayAnyPure xs _ p (fun _ => rfl)).trans (congrArg pure Array.any_toList)

public theorem Array.allM_pure : type_of% @_root_.Array.allM_pure := by
  intro m α mon law p xs
  rw [Array.allM, arrayAnyPure xs (fun x => pure (f := m) (p x) >>= fun v => pure !v)
    (fun x => !p x) (fun _ => pure_bind ..), pure_bind]
  exact congrArg pure ((congrArg Bool.not Array.any_toList).trans Array.all_eq_not_any_not.symm)

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

end OmegaChecks.InitPort.Alternatives
