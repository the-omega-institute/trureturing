module
public import Init.Data.Array.Monadic
import all Init.Data.Array.Basic
public import Init.Data.List.Monadic
import all Init.Data.List.ToArray
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


private def forInNext [Monad m] (action : β → m (ForInStep β)) (tail : β → m β) (b : β) : m β :=
  action b >>= fun | .done v => pure v | .yield v => tail v

private theorem listForInReindex [Monad m] {as : List α} {bs : List γ} (map : α → γ)
    (f : (x : α) → x ∈ as → β → m (ForInStep β))
    (g : (x : γ) → x ∈ bs → β → m (ForInStep β))
    (same : ∀ a ha hb, f a ha = g (map a) hb) (xs : List α) (ys : List γ)
    (related : xs.map map = ys) (left : ∃ s, s ++ xs = as) (right : ∃ s, s ++ ys = bs) :
    (fun b => List.forIn'.loop as f xs b left) = fun b => List.forIn'.loop bs g ys b right := by
  subst ys
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    let leftMem : a ∈ as := by
      obtain ⟨s, rfl⟩ := left
      exact List.mem_append_right s List.mem_cons_self
    let rightMem : map a ∈ bs := by
      obtain ⟨s, rfl⟩ := right
      exact List.mem_append_right s List.mem_cons_self
    have leftTail : ∃ s, s ++ xs = as := by
      obtain ⟨s, rfl⟩ := left
      exact ⟨s ++ [a], (List.append_assoc ..)⟩
    have rightTail : ∃ s, s ++ xs.map map = bs := by
      obtain ⟨s, rfl⟩ := right
      exact ⟨s ++ [map a], (List.append_assoc ..)⟩
    exact (congrArg (forInNext (f a leftMem)) (ih leftTail rightTail)).trans
      (congrArg (fun head => forInNext head _) (same a leftMem rightMem))

public theorem List.forIn'_cons : type_of% @_root_.List.forIn'_cons := by
  intro m α β mon a xs f b
  let tail (x : α) (hx : x ∈ xs) := f x (List.mem_cons_of_mem a hx)
  have same := listForInReindex id f tail (fun _ _ _ => rfl) xs xs (List.map_id xs)
    (show ∃ s, s ++ xs = a :: xs from ⟨[a], rfl⟩) ⟨[], rfl⟩
  exact congrFun (congrArg (forInNext (f a List.mem_cons_self)) same) b

public theorem List.forIn_cons : type_of% @_root_.List.forIn_cons := by
  intro m α β mon f a xs b
  exact List.forIn'_cons (fun a _ => f a) b

public theorem List.forIn'_map : type_of% @_root_.List.forIn'_map := by
  intro m α β γ init mon law xs g f
  exact congrFun (listForInReindex g (fun a h => f (g a) (List.mem_map_of_mem h))
    f (fun _ _ _ => rfl) xs (xs.map g) rfl ⟨[], rfl⟩ ⟨[], rfl⟩).symm init

public theorem List.forIn_map : type_of% @_root_.List.forIn_map := by
  intro m α β γ init mon law xs g f
  exact List.forIn'_map _ (fun x _ => f x)


private theorem arrayListForIn [Monad m] (l : List α)
    (f : (a : α) → a ∈ l.toArray → β → m (ForInStep β)) (rest : List α)
    (k : Nat) (length : l.length = rest.length + k) (drop : l.drop k = rest)
    (suffix : ∃ s, s ++ rest = l) :
    Array.forIn'.loop l.toArray f rest.length (Nat.le.intro length.symm) =
      fun b => List.forIn'.loop l (fun a h => f a (List.mem_toArray.mpr h)) rest b suffix := by
  induction rest generalizing k with
  | nil => rfl
  | cons a rest ih =>
    have nextLength : l.length = rest.length + (k+1) := by
      rw [length, List.length_cons, Nat.succ_add]
      rfl
    have hk : k < l.length := by
      rw [nextLength]
      exact Nat.le_add_left _ _
    have pair := (List.drop_eq_getElem_cons hk).symm.trans drop
    have tail := (List.cons.inj pair).2
    have first := (List.cons.inj pair).1
    subst a
    have idx : l.toArray.size - 1 - rest.length = k := by
      rw [List.size_toArray, length, List.length_cons, Nat.succ_add, Nat.succ_sub_one, Nat.add_sub_cancel_left]
    have suff : ∃ s, s ++ rest = l := by
      obtain ⟨s, hs⟩ := suffix
      exact ⟨s ++ [l[k]], (List.append_assoc ..).trans hs⟩
    have bound : l.toArray.size - 1 - rest.length < l.toArray.size := idx ▸ hk
    have indexValue : l.toArray[l.toArray.size - 1 - rest.length] = l[k] := by
      simp only [List.getElem_toArray]
      exact idx ▸ rfl
    have head (x y : α) (hx : x ∈ l.toArray) (hy : y ∈ l.toArray) (e : x = y) : f x hx = f y hy := by
      subst y
      rfl
    exact (congrArg (forInNext _) (ih _ nextLength tail suff)).trans
      (congrArg (fun action => forInNext action _) (head _ _ _ _ indexValue))

public theorem List.forIn'_toArray : type_of% @_root_.List.forIn'_toArray := by
  intro m α β mon l b f
  exact congrFun (arrayListForIn l f l 0 rfl rfl ⟨[], rfl⟩) b

public theorem List.forIn_toArray : type_of% @_root_.List.forIn_toArray := by
  intro m α β mon l b f
  exact List.forIn'_toArray l b (fun a _ => f a)


public theorem List.forM_toArray' : type_of% @_root_.List.forM_toArray' := by
  intro m α stop mon l f h
  subst stop
  rw [Array.forM, _root_.List.foldlM_toArray]
  induction l with
  | nil => rfl
  | cons a xs ih =>
    have same : (fun b : PUnit => xs.foldlM (fun _ => f) b) = fun _ : PUnit => xs.forM f := by
      exact congrArg (fun val (_ : PUnit) => val) ih
    exact congrArg (fun tail => f a >>= tail) same

public theorem List.forIn'_loop_toArray._proof_1 :
    type_of% @_root_.List.forIn'_loop_toArray._proof_1 := by
  intro α l i a h
  apply List.mem_toArray.mpr
  exact List.take_append_drop (l.length - i) l ▸ List.mem_append_right (l.take (l.length - i)) h

public theorem List.forIn'_loop_toArray : type_of% @_root_.List.forIn'_loop_toArray := by
  intro m α β mon l f i h b
  let k := l.length - i
  let xs := l.drop k
  have len : xs.length = i := by
    rw [List.length_drop]
    exact Nat.sub_sub_self h
  have decomposition : l.length = xs.length + k := by
    rw [len, Nat.add_comm]
    exact (Nat.sub_add_cancel h).symm
  have suffix : ∃ s, s ++ xs = l := ⟨l.take k, List.take_append_drop ..⟩
  have first := arrayListForIn l f xs k decomposition rfl suffix
  have second := listForInReindex id (fun a (mem : a ∈ l) => f a (List.mem_toArray.mpr mem))
    (fun a (mem : a ∈ xs) => f a (List.forIn'_loop_toArray._proof_1 l i a mem))
    (fun _ _ _ => rfl) xs xs (List.map_id xs) suffix ⟨[], rfl⟩
  have result := congrFun (first.trans second) b
  have move (j i : Nat) (hj : j ≤ l.length) (hi : i ≤ l.length) (e : j = i) :
      Array.forIn'.loop l.toArray f i hi b = Array.forIn'.loop l.toArray f j hj b := by
    subst i
    rfl
  exact (move _ _ _ _ len).trans result


public theorem Array.findM?_pure : type_of% @_root_.Array.findM?_pure := by
  intro α m mon law p xs
  cases xs with
  | mk l =>
    rw [Array.findM?, List.forIn_toArray, _root_.List.find?_toArray]
    induction l with
    | nil => rw [List.forIn_nil, pure_bind]; rfl
    | cons a l ih =>
      rw [List.forIn_cons, pure_bind]
      cases hp : p a with
      | false =>
        rw [ite_eq_right Bool.false_ne_true, pure_bind, List.find?_cons, hp]
        exact ih
      | true => rw [ite_eq_left rfl, pure_bind, pure_bind, List.find?_cons, hp]

public theorem Array.findSomeM?_pure : type_of% @_root_.Array.findSomeM?_pure := by
  intro m α β mon law f xs
  cases xs with
  | mk l =>
    rw [Array.findSomeM?, List.forIn_toArray, _root_.List.findSome?_toArray]
    induction l with
    | nil => rw [List.forIn_nil, pure_bind]; rfl
    | cons a l ih =>
      rw [List.forIn_cons, pure_bind]
      cases hp : f a with
      | none =>
        rw [pure_bind, List.findSome?_cons, hp]
        exact ih
      | some b => rw [pure_bind, pure_bind, List.findSome?_cons, hp]


public theorem Array.idRun_forIn'_yield_eq_foldl : type_of% @_root_.Array.idRun_forIn'_yield_eq_foldl := by
  intros
  exact _root_.Array.forIn'_pure_yield_eq_foldl _ _

public theorem Array.idRun_forIn_yield_eq_foldl : type_of% @_root_.Array.idRun_forIn_yield_eq_foldl := by
  intros
  exact _root_.Array.forIn_pure_yield_eq_foldl _ _

public theorem Array.forM_append : type_of% @_root_.Array.forM_append := by
  intro m α mon law xs ys f
  cases xs with
  | mk xs =>
    cases ys with
    | mk ys =>
      rw [List.append_toArray, _root_.List.forM_toArray, _root_.List.forM_toArray, _root_.List.forM_toArray]
      exact List.forM_append

private theorem foldActions [Monad m] {f g : β → α → m β}
    (same : ∀ a, (fun b => f b a) = fun b => g b a) (xs : List α) :
    (fun b => xs.foldlM f b) = fun b => xs.foldlM g b := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    let step (head : β → m β) (tail : β → m β) (b : β) := head b >>= tail
    exact (congrArg (step (fun b => f b a)) ih).trans (congrArg (fun head => step head _) (same a))

public theorem Array.filterM_congr : type_of% @_root_.Array.filterM_congr := by
  intro α m mon xs ys e p q h
  subst ys
  rw [Array.filterM, Array.filterM, ← Array.foldlM_toList, ← Array.foldlM_toList]
  exact congrFun (foldActions (fun a => by rw [h a]) xs.toList) _

public theorem Array.filterRevM_congr : type_of% @_root_.Array.filterRevM_congr := by
  intro α m mon xs ys e p q h
  subst ys
  rw [Array.filterRevM, Array.filterRevM, Array.foldrM_eq_reverse_foldlM_toList, Array.foldrM_eq_reverse_foldlM_toList]
  exact congrArg (Functor.map Array.reverse) (congrFun (foldActions (fun a => by rw [h a]) xs.toList.reverse) _)

public theorem Array.filterMapM_congr : type_of% @_root_.Array.filterMapM_congr := by
  intro m α β mon xs ys e f g h
  subst ys
  rw [Array.filterMapM, Array.filterMapM, ← Array.foldlM_toList, ← Array.foldlM_toList]
  exact congrFun (foldActions (fun a => by rw [h a]) xs.toList) _

public theorem Array.flatMapM_congr : type_of% @_root_.Array.flatMapM_congr := by
  intro m α β mon xs ys e f g h
  subst ys
  rw [Array.flatMapM, Array.flatMapM, ← Array.foldlM_toList, ← Array.foldlM_toList]
  exact congrFun (foldActions (fun a => by rw [h a]) xs.toList) _


public theorem Array.foldlM_map : type_of% @_root_.Array.foldlM_map := by
  intro m β₁ β₂ α stop mon f g xs b w
  subst stop
  rw [← Array.foldlM_toList, ← Array.size_map (f := f) (xs := xs),
    ← Array.foldlM_toList, Array.toList_map]
  exact List.foldlM_map

public theorem Array.foldrM_map : type_of% @_root_.Array.foldrM_map := by
  intro m β₁ β₂ α start mon law f g xs b w
  subst start
  rw [← Array.foldrM_toList, ← Array.size_map (f := f) (xs := xs),
    ← Array.foldrM_toList, Array.toList_map]
  exact List.foldrM_map

public theorem Array.foldlM_attachWith : type_of% @_root_.Array.foldlM_attachWith := by
  intro m α β stop mon xs q h f b w
  subst stop
  rw [← Array.foldlM_toList, ← Array.size_attachWith (H := h), ← Array.foldlM_toList,
    Array.toList_attachWith, Array.toList_attach, List.foldlM_attachWith, List.foldlM_attachWith]

public theorem Array.foldrM_attachWith : type_of% @_root_.Array.foldrM_attachWith := by
  intro m α β start mon law xs q h f b w
  subst start
  rw [← Array.foldrM_toList, ← Array.size_attachWith (H := h), ← Array.foldrM_toList,
    Array.toList_attachWith, Array.toList_attach, List.foldrM_attachWith, List.foldrM_attachWith]

public theorem Array.foldlM_unattach : type_of% @_root_.Array.foldlM_unattach := by
  intros
  rw [← Array.foldlM_toList, ← Array.foldlM_toList, Array.toList_unattach]
  exact List.foldlM_unattach

public theorem Array.foldrM_unattach : type_of% @_root_.Array.foldrM_unattach := by
  intros
  rw [← Array.foldrM_toList, ← Array.foldrM_toList, Array.toList_unattach]
  exact List.foldrM_unattach

public theorem Array.filterMapM_subtype : type_of% @_root_.Array.filterMapM_subtype := by
  intro m α β stop mon law p xs f g h w
  subst stop
  rw [Array.filterMapM, Array.filterMapM, ← Array.foldlM_toList, ← Array.foldlM_toList, Array.toList_unattach]
  unfold List.unattach
  rw [List.foldlM_map]
  exact congrFun (foldActions (fun a => by rw [h a.1 a.2]) xs.toList) _

public theorem Array.flatMapM_subtype : type_of% @_root_.Array.flatMapM_subtype := by
  intro m α β mon law p xs f g h
  rw [Array.flatMapM, Array.flatMapM, ← Array.foldlM_toList, ← Array.foldlM_toList, Array.toList_unattach]
  unfold List.unattach
  rw [List.foldlM_map]
  exact congrFun (foldActions (fun a => by rw [h a.1 a.2]) xs.toList) _

end OmegaChecks.InitPort.Alternatives
