module

public import OmegaChecks.InitPort.Alternatives.MonadicLists.Equations
public import OmegaChecks.InitPort.Alternatives.MonadicLists.Folds
import Init.Data.Array.Zip
import all Init.Data.Array.OfFn
import all Init.Data.Vector.Basic
import all Init.Data.Vector.OfFn
import Init.Data.Vector.Monadic
public import Init.Data.Array.Monadic
import all Init.Data.Array.Basic
public import Init.Data.List.Monadic
import all Init.Data.List.ToArray
import all Init.Data.List.Control
import Init.Data.List.Attach
import all Init.Data.List.OfFn

/-! Reduction of pure monadic list operations on arbitrary accumulators. -/
namespace OmegaChecks.InitPort.Alternatives

private theorem fixInvariant {A : Sort u} {B : Sort v} (measure : A → Nat) (satisfies : A → B → Prop)
    (action : (x : A) → ((y : A) → measure y < measure x → B) → B)
    (step : ∀ x recur, (∀ y h, satisfies y (recur y h)) → satisfies x (action x recur)) (x : A) :
    satisfies x (WellFounded.Nat.fix measure action x) := by
  have go (n : Nat) (x : A) (hn : measure x < n) :
      satisfies x (WellFounded.Nat.fix.go measure action n x hn) := by
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
    apply fixInvariant _ (fun p out => out = spec p)
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
    apply fixInvariant _ (fun p out => out = spec p)
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

private theorem forInArrayList [Monad m] (xs : Array α) (b : β)
    (f : (a : α) → a ∈ xs → β → m (ForInStep β)) :
    forIn' xs b f = forIn' xs.toList b (fun a h => f a (Array.mem_def.mpr h)) := by
  cases xs with
  | mk l => exact List.forIn'_toArray l b f

public theorem Array.forIn'_map : type_of% @_root_.Array.forIn'_map := by
  intro m α β γ init mon law xs g f
  rw [forInArrayList, forInArrayList (xs := xs)]
  exact congrFun (listForInReindex g _ _ (fun _ _ _ => rfl)
    xs.toList (xs.map g).toList Array.toList_map.symm ⟨[], rfl⟩ ⟨[], rfl⟩).symm init

private def mapListInto [Monad m] (f : α → m β) : List α → Array β → m (Array β)
  | [], acc => pure acc
  | a :: xs, acc => f a >>= fun b => mapListInto f xs (acc.push b)

private theorem dependentBranch [d : Decidable p] (h : p) (yes : α → p → β) (no : α → ¬p → β) :
    (fun a => dite p (yes a) (no a)) = fun a => yes a h := by
  cases d with
  | isTrue => rfl
  | isFalse hn => exact False.elim (hn h)

private theorem dependentElse [d : Decidable p] (h : ¬p) (yes : α → p → β) (no : α → ¬p → β) :
    (fun a => dite p (yes a) (no a)) = fun a => no a h := by
  cases d with
  | isTrue hp => exact False.elim (h hp)
  | isFalse => rfl

private theorem mapArrayLoop [Monad m] (xs : Array α) (f : α → m β) (j : Nat) :
    (fun acc => _root_.Array.mapM.map f xs j acc) = mapListInto f (xs.toList.drop j) := by
  let measure (s : (_ : Nat) ×' Array β) : Nat := PSigma.casesOn s fun i _ => xs.size - i
  let act (s : (_ : Nat) ×' Array β) (recur : ∀ t, measure t < measure s → m (Array β)) :=
    PSigma.casesOn (motive := fun x => (∀ t, measure t < measure x → m (Array β)) → m (Array β))
      s (fun i acc recur =>
        if h : i < xs.size then
          f xs[i] >>= fun b => recur ⟨i+1, acc.push b⟩ (Nat.sub_succ_lt_self _ _ h)
        else pure acc) recur
  have same (fuel i : Nat) (h : xs.size - i < fuel) :
      (fun acc : Array β => WellFounded.Nat.fix.go measure act fuel ⟨i, acc⟩ h) =
      mapListInto f (xs.toList.drop i) := by
    induction fuel generalizing i with
    | zero => exact False.elim (Nat.not_lt_zero _ h)
    | succ fuel ih =>
      dsimp only [WellFounded.Nat.fix.go, act]
      by_cases bound : i < xs.size
      · rw [← List.getElem_cons_drop (as := xs.toList) (i := i) bound]
        apply (dependentBranch bound _ _).trans
        exact congrArg (fun tail (acc : Array β) => f xs[i] >>= fun b => tail (acc.push b))
          (ih (i+1) (Nat.lt_of_lt_of_le (Nat.sub_succ_lt_self _ _ bound) (Nat.le_of_lt_succ h)))
      · rw [List.drop_eq_nil_of_le (Nat.le_of_not_gt bound)]
        exact dependentElse bound _ _
  delta Array.mapM.map Array.mapM.map._unary WellFounded.Nat.fix
  have fuel : xs.size - j < WellFounded.Nat.eager (xs.size - j + 1) := by
    unfold WellFounded.Nat.eager
    split <;> exact Nat.lt_succ_self _
  exact same _ j fuel

private theorem mapArrayList [Monad m] (xs : Array α) (f : α → m β) :
    xs.mapM f = mapListInto f xs.toList #[] :=
  congrFun (mapArrayLoop xs f 0) #[]

public theorem Array.mapM.map.eq_def : type_of% @_root_.Array.mapM.map.eq_def := by
  intro α β m inst f xs i acc
  rw [congrFun (mapArrayLoop xs f i) acc]
  by_cases h : i < xs.size
  · rw [dite_eq_left h, ← List.getElem_cons_drop (as := xs.toList) (i := i) h]
    exact congrArg (fun tail => f xs[i] >>= fun b => tail (acc.push b)) (mapArrayLoop xs f (i+1)).symm
  · rw [dite_eq_right h, List.drop_eq_nil_of_le (Nat.le_of_not_gt h)]
    rfl

public theorem Array.toList_map : type_of% @_root_.Array.toList_map := by
  intro α β f xs
  have finish (l : List α) (acc : Array β) :
      mapListInto (m := Id) (pure ∘ f) l acc = (acc.toList ++ l.map f).toArray := by
    induction l generalizing acc with
    | nil => exact congrArg _root_.List.toArray (_root_.List.append_nil _).symm
    | cons a l ih =>
      refine (ih (acc.push (f a))).trans ?_
      apply _root_.Array.ext'
      change (acc.push (f a)).toList ++ l.map f = acc.toList ++ (f a :: l.map f)
      rw [_root_.Array.toList_push, _root_.List.append_assoc]
      rfl
  exact congrArg _root_.Array.toList ((mapArrayList (m := Id) xs (pure ∘ f)).trans (finish xs.toList #[]))

public theorem List.map_toArray : type_of% @_root_.List.map_toArray := by
  intros
  exact _root_.Array.ext' _root_.Array.toList_map

public theorem Array.size_map : type_of% @_root_.Array.size_map := by
  intro α β f xs
  exact (congrArg _root_.List.length (_root_.Array.toList_map (f := f) (xs := xs))).trans
    (_root_.List.length_map f)

public theorem Array.map_push : type_of% @_root_.Array.map_push := by
  intros
  apply _root_.Array.ext'
  rw [_root_.Array.toList_map, _root_.Array.toList_push, _root_.Array.toList_push,
    _root_.Array.toList_map, _root_.List.map_append]
  rfl

public theorem Array.map_id'' : type_of% @_root_.Array.map_id'' := by
  intro α f h xs
  exact _root_.Array.ext' (_root_.Array.toList_map.trans (_root_.List.map_id'' h _))

public theorem Array.map_eq_empty_iff : type_of% @_root_.Array.map_eq_empty_iff := by
  intro α β f xs
  exact ⟨fun h => _root_.Array.eq_empty_of_size_eq_zero
    (_root_.Array.size_map.symm.trans (congrArg _root_.Array.size h)),
    fun h => h ▸ _root_.Array.map_empty⟩

public theorem Array.mapM_map : type_of% @_root_.Array.mapM_map := by
  intro m α β γ mon law f g xs
  rw [mapArrayList, mapArrayList, Array.toList_map]
  have same (l : List α) : mapListInto g (l.map f) = mapListInto (g ∘ f) l := by
    induction l with
    | nil => rfl
    | cons a l ih => exact congrArg (fun tail (acc : Array γ) => g (f a) >>= fun b => tail (acc.push b)) ih
  exact congrFun (same xs.toList) #[]

public theorem Array.mapM_subtype : type_of% @_root_.Array.mapM_subtype := by
  intro m α β mon law p xs f g h
  rw [mapArrayList, mapArrayList, Array.toList_unattach]
  have same (l : List (Subtype p)) : mapListInto f l = mapListInto g l.unattach := by
    induction l with
    | nil => rfl
    | cons a l ih =>
      let step (val : m β) (tail : Array β → m (Array β)) (acc : Array β) :=
        val >>= fun b => tail (acc.push b)
      exact (congrArg (step (f a)) ih).trans (congrArg (fun val => step val _) (h a.1 a.2))
  exact congrFun (same xs.toList) #[]

public theorem Array.foldlM_filter : type_of% @_root_.Array.foldlM_filter := by
  intros
  subst_vars
  rw [← Array.foldlM_toList, ← Array.foldlM_toList, Array.toList_filter]
  exact List.foldlM_filter

public theorem Array.foldlM_filterMap : type_of% @_root_.Array.foldlM_filterMap := by
  intros
  subst_vars
  rw [← Array.foldlM_toList, ← Array.foldlM_toList, Array.toList_filterMap]
  exact List.foldlM_filterMap

public theorem Array.foldrM_filter : type_of% @_root_.Array.foldrM_filter := by
  intros
  subst_vars
  rw [← Array.foldrM_toList, ← Array.foldrM_toList, Array.toList_filter]
  exact List.foldrM_filter

public theorem Array.foldrM_filterMap : type_of% @_root_.Array.foldrM_filterMap := by
  intros
  subst_vars
  rw [← Array.foldrM_toList, ← Array.foldrM_toList, Array.toList_filterMap]
  exact List.foldrM_filterMap

public theorem List.push_toArray_fun : type_of% @_root_.List.push_toArray_fun := by
  intro α xs
  have concat (xs : List α) : List.concat xs = fun a => xs ++ [a] := by
    induction xs with
    | nil => rfl
    | cons a xs ih => exact congrArg (fun tail b => a :: tail b) ih
  exact congrArg (fun k a => List.toArray (k a)) (concat xs)

public theorem List.isPrefixOf_toArray : type_of% @_root_.List.isPrefixOf_toArray := by
  intro α beq xs ys
  rw [Array.isPrefixOf]
  by_cases fits : xs.length ≤ ys.length
  · rw [dite_eq_left (show xs.toArray.size ≤ ys.toArray.size from fits)]
    exact _root_.List.isPrefixOfAux_toArray_zero xs ys fits
  · rw [dite_eq_right (show ¬xs.toArray.size ≤ ys.toArray.size from fits)]
    induction xs generalizing ys with
    | nil => exact False.elim (fits (Nat.zero_le _))
    | cons a xs ih =>
      cases ys with
      | nil => rfl
      | cons b ys =>
        rw [List.isPrefixOf_cons_cons, ← ih (ys := ys) (fun small => fits (Nat.succ_le_succ small))]
        exact (Bool.and_false _).symm

private def zipListInto [Monad m] (f : α → β → m γ) : List α → List β → Array γ → m (Array γ)
  | a :: as, b :: bs, acc => f a b >>= fun c => zipListInto f as bs (acc.push c)
  | _, _, acc => pure acc

private theorem zipRightNil [Monad m] (f : α → β → m γ) (xs : List α) :
    zipListInto f xs [] = pure := by
  cases xs <;> rfl

private theorem zipArrayLists [Monad m] (as : Array α) (bs : Array β) (f : α → β → m γ) (i : Nat) :
    Array.zipWithMAux as bs f i = zipListInto f (as.toList.drop i) (bs.toList.drop i) := by
  let measure (s : (_ : Nat) ×' Array γ) : Nat := PSigma.casesOn s fun i _ => as.size - i
  let act (s : (_ : Nat) ×' Array γ) (recur : ∀ t, measure t < measure s → m (Array γ)) :=
    PSigma.casesOn (motive := fun x => (∀ t, measure t < measure x → m (Array γ)) → m (Array γ))
      s (fun j acc recur =>
        if ha : j < as.size then
          if hb : j < bs.size then
            f as[j] bs[j] >>= fun c => recur ⟨j+1, acc.push c⟩ (Nat.sub_succ_lt_self _ _ ha)
          else pure acc
        else pure acc) recur
  have same (fuel j : Nat) (h : as.size - j < fuel) :
      (fun acc : Array γ => WellFounded.Nat.fix.go measure act fuel ⟨j, acc⟩ h) =
      zipListInto f (as.toList.drop j) (bs.toList.drop j) := by
    induction fuel generalizing j with
    | zero => exact False.elim (Nat.not_lt_zero _ h)
    | succ fuel ih =>
      dsimp only [WellFounded.Nat.fix.go, act]
      by_cases ha : j < as.size
      · apply (dependentBranch ha _ _).trans
        rw [← List.getElem_cons_drop (as := as.toList) (i := j) ha]
        by_cases hb : j < bs.size
        · apply (dependentBranch hb _ _).trans
          rw [← List.getElem_cons_drop (as := bs.toList) (i := j) hb]
          exact congrArg (fun tail (acc : Array γ) => f as[j] bs[j] >>= fun c => tail (acc.push c))
            (ih (j+1) (Nat.lt_of_lt_of_le (Nat.sub_succ_lt_self _ _ ha) (Nat.le_of_lt_succ h)))
        · rw [List.drop_eq_nil_of_le (Nat.le_of_not_gt hb), zipRightNil]
          exact dependentElse hb _ _
      · rw [List.drop_eq_nil_of_le (Nat.le_of_not_gt ha)]
        exact dependentElse ha _ _
  delta Array.zipWithMAux Array.zipWithMAux._unary WellFounded.Nat.fix
  have fuel : as.size - i < WellFounded.Nat.eager (as.size - i + 1) := by
    unfold WellFounded.Nat.eager
    split <;> exact Nat.lt_succ_self _
  exact same _ i fuel

public theorem List.zipWithMAux_toArray_succ : type_of% @_root_.List.zipWithMAux_toArray_succ := by
  intro m α β γ mon as bs f i acc
  rw [zipArrayLists, zipArrayLists]
  change zipListInto f (as.drop (i+1)) (bs.drop (i+1)) acc =
    zipListInto f (as.tail.drop i) (bs.tail.drop i) acc
  rw [List.drop_tail, List.drop_tail]

public theorem List.zipWithMAux_toArray_succ._unary : type_of% @_root_.List.zipWithMAux_toArray_succ._unary := by
  intro α β γ m _ as bs f p
  exact List.zipWithMAux_toArray_succ as bs f p.1 p.2

public theorem List.zipWithMAux_toArray_succ' : type_of% @_root_.List.zipWithMAux_toArray_succ' := by
  intros
  rw [zipArrayLists, zipArrayLists]
  rfl

public theorem Array.zipWithMAux.eq_def : type_of% @_root_.Array.zipWithMAux.eq_def := by
  intro α β γ m mon as bs f i acc
  rw [zipArrayLists]
  by_cases ha : i < as.size
  · rw [dite_eq_left ha, ← List.getElem_cons_drop (as := as.toList) (i := i) ha]
    by_cases hb : i < bs.size
    · rw [dite_eq_left hb, ← List.getElem_cons_drop (as := bs.toList) (i := i) hb]
      exact congrArg (fun tail => f as[i] bs[i] >>= fun c => tail (acc.push c)) (zipArrayLists as bs f (i+1)).symm
    · rw [dite_eq_right hb, List.drop_eq_nil_of_le (Nat.le_of_not_gt hb), zipRightNil]
  · rw [dite_eq_right ha, List.drop_eq_nil_of_le (Nat.le_of_not_gt ha)]
    rfl

public theorem Array.zipWithMAux._unary.eq_def : type_of% @_root_.Array.zipWithMAux._unary.eq_def := by
  intro α β γ m mon as bs f p
  obtain ⟨i, acc⟩ := p
  with_unfolding_all exact Array.zipWithMAux.eq_def as bs f i acc

public theorem List.firstM_toArray : type_of% @_root_.List.firstM_toArray := by
  intro m α β alt xs f
  have loop (n j : Nat) (sum : j + n = xs.length) :
      Array.firstM.go f xs.toArray j = List.firstM f (xs.drop j) := by
    induction n generalizing j with
    | zero =>
      have e : j = xs.length := sum
      subst j
      have past : ¬ xs.length < xs.toArray.size := Nat.lt_irrefl _
      rw [Array.firstM.go, dite_eq_right past, List.drop_length]
      rfl
    | succ n ih =>
      have bound : j < xs.length := by omega
      have inside : j < xs.toArray.size := bound
      rw [Array.firstM.go, dite_eq_left inside, ← List.getElem_cons_drop bound, List.firstM]
      exact congrArg (fun x => f xs[j] <|> x) (ih (j+1) (by omega))
  exact loop xs.length 0 (Nat.zero_add _)

private theorem foldPurePush [Monad m] [LawfulMonad m] (f : Fin n → α) (xs : Array α) :
    Fin.foldlM n (m := m) (fun acc j => acc.push <$> pure (f j)) xs =
      pure (xs ++ Array.ofFn f) := by
  induction n generalizing xs with
  | zero => rw [Fin.foldlM_zero, Array.ofFn_zero, Array.append_empty]
  | succ n ih =>
    rw [Fin.foldlM_succ]
    dsimp only
    rw [map_pure, pure_bind, ih, Array.ofFn_succ' (f := f), Array.push_eq_append, Array.append_assoc]

public theorem List.ofFn_add : type_of% @_root_.List.ofFn_add := by
  intro α n m f
  unfold _root_.List.ofFn
  rw [_root_.Fin.foldr_add]
  exact _root_.Fin.foldr_cons_eq_append

public theorem Array.ofFn_add : type_of% @_root_.Array.ofFn_add := by
  intro α n m f
  apply _root_.Array.toList_inj.mp
  rw [_root_.Array.toList_append, _root_.Array.toList_ofFn, _root_.Array.toList_ofFn,
    _root_.Array.toList_ofFn, _root_.List.ofFn_add]

public theorem Array.ofFnM_pure_comp : type_of% @_root_.Array.ofFnM_pure_comp := by
  intro m α mon law n f
  unfold _root_.Array.ofFnM
  change Fin.foldlM n (m := m) (fun acc j => acc.push <$> pure (f j)) #[] = _
  rw [foldPurePush, _root_.Array.empty_append]

public theorem Array.idRun_ofFnM : type_of% @_root_.Array.idRun_ofFnM := by
  intro α n f
  exact _root_.Array.ofFnM_pure_comp (m := Id)

public theorem Vector.ofFnM_pure_comp : type_of% @_root_.Vector.ofFnM_pure_comp := by
  intro m α mon law n f
  let agrees (p : (i : Nat) ×' (_ : i ≤ n) ×' (xs : Array α) ×' xs.size = i) (out : m (Vector α n)) :=
    (∀ j (hj : j < p.2.2.1.size),
      p.2.2.1[j] = f ⟨j, Nat.lt_of_lt_of_le (p.2.2.2 ▸ hj) p.2.1⟩) →
      out = pure (Vector.ofFn f)
  delta _root_.Vector.ofFnM _root_.Vector.ofFnM.go _root_.Vector.ofFnM.go._unary
  apply fixInvariant _ agrees
  · rintro ⟨i, hi, xs, hx⟩ recur ih
    dsimp only [agrees, Function.comp_apply]
    intro prefixAgree
    by_cases h : i < n
    · rw [dite_eq_left h, pure_bind]
      apply ih
      intro j hj
      by_cases old : j < xs.size
      · exact (Array.getElem_push_lt old).trans (prefixAgree j old)
      · have last : j = xs.size := by
          rw [Array.size_push] at hj
          exact Nat.le_antisymm (Nat.le_of_lt_succ hj) (Nat.le_of_not_lt old)
        subst j
        rw [Array.getElem_push_eq]
        exact congrArg f (Fin.ext hx.symm)
    · rw [dite_eq_right h]
      apply congrArg pure
      apply Vector.ext
      intro j hj
      rw [Vector.getElem_ofFn]
      exact prefixAgree j _
  · intro j hj
    exact False.elim (Nat.not_lt_zero _ hj)

public theorem Vector.idRun_ofFnM : type_of% @_root_.Vector.idRun_ofFnM := by
  intro α n f
  exact _root_.Vector.ofFnM_pure_comp (m := Id)

public theorem Vector.mapM_pure : type_of% @_root_.Vector.mapM_pure := by
  intro m α n β mon law xs f
  let agrees (p : (k : Nat) ×' (_ : k ≤ n) ×' Vector β k) (out : m (Vector β n)) :=
    (∀ j (hj : j < p.1), p.2.2[j] = f (xs[j]'(Nat.lt_of_lt_of_le hj p.2.1))) →
      out = pure (xs.map f)
  delta _root_.Vector.mapM _root_.Vector.mapM.go _root_.Vector.mapM.go._unary
  apply fixInvariant _ agrees
  · rintro ⟨k, hk, acc⟩ recur ih
    dsimp only [agrees]
    intro prefixAgree
    by_cases h : k < n
    · rw [dite_eq_left h, pure_bind]
      apply ih
      intro j hj
      by_cases old : j < k
      · exact (Vector.getElem_push_lt old).trans (prefixAgree j old)
      · have last : j = k := Nat.le_antisymm (Nat.le_of_lt_succ hj) (Nat.le_of_not_lt old)
        subst j
        exact Vector.getElem_push_eq
    · rw [dite_eq_right h]
      apply congrArg pure
      apply Vector.ext
      intro j hj
      rw [Vector.getElem_cast, Vector.getElem_map]
      exact prefixAgree j _
  · intro j hj
    exact False.elim (Nat.not_lt_zero _ hj)

private theorem mapVectorEffects [Monad m] (xs : Vector α n) (ys : Vector β n)
    (f : α → m γ) (g : β → m γ) (same : ∀ i (hi : i < n), f xs[i] = g ys[i]) :
    xs.mapM f = ys.mapM g := by
  let State := (i : Nat) ×' (_ : i ≤ n) ×' Vector γ i
  let measure (s : State) : Nat := s.casesOn fun i t => t.casesOn fun _ _ => n - i
  let step (read : Fin n → m γ) (s : State) (next : ∀ t, measure t < measure s → m (Vector γ n)) :=
    s.casesOn (motive := fun s => (∀ t, measure t < measure s → m (Vector γ n)) → m (Vector γ n))
      (fun i t => t.casesOn (motive := fun t => (∀ s, measure s < measure ⟨i, t⟩ → m (Vector γ n)) → m (Vector γ n))
        fun hi acc next => if inside : i < n then read ⟨i, inside⟩ >>= fun val =>
          next ⟨i+1, inside, acc.push val⟩ (Nat.sub_succ_lt_self _ _ inside)
        else pure (acc.cast (Nat.le_antisymm hi (Nat.le_of_not_gt inside)))) next
  let left (i : Fin n) := f xs[i.val]
  let right (i : Fin n) := g ys[i.val]
  have eq (fuel i : Nat) (hi : i ≤ n) (enough : n - i < fuel) :
      (fun acc => WellFounded.Nat.fix.go measure (step left) fuel ⟨i, hi, acc⟩ enough) =
      (fun acc => WellFounded.Nat.fix.go measure (step right) fuel ⟨i, hi, acc⟩ enough) := by
    induction fuel generalizing i with
    | zero => exact (Nat.not_lt_zero _ enough).elim
    | succ fuel ih =>
      dsimp only [WellFounded.Nat.fix.go, step]
      by_cases inside : i < n
      · apply (dependentBranch inside _ _).trans
        apply Eq.trans _ (dependentBranch inside _ _).symm
        dsimp only [left, right]
        rw [same i inside]
        exact congrArg (fun cont acc => g ys[i] >>= fun val => cont (Vector.push acc val))
          (ih (i+1) inside (Nat.lt_of_lt_of_le (Nat.sub_succ_lt_self _ _ inside) (Nat.le_of_lt_succ enough)))
      · apply (dependentElse inside _ _).trans
        symm
        apply dependentElse inside
  delta _root_.Vector.mapM _root_.Vector.mapM.go _root_.Vector.mapM.go._unary WellFounded.Nat.fix
  exact congrFun (eq _ 0 (Nat.zero_le _) (by rw [WellFounded.Nat.eager_eq]; exact Nat.lt_succ_self _)) #v[]

public theorem Vector.mapM_map : type_of% @_root_.Vector.mapM_map := by
  intro m α β γ n mon law f g xs
  exact mapVectorEffects (xs.map f) xs g (g ∘ f) fun i hi => congrArg g (Vector.getElem_map f hi)

public theorem Array.zipWithM_eq_mapM_id_zipWith : type_of% @_root_.Array.zipWithM_eq_mapM_id_zipWith := by
  intro α β γ m mon law f as bs
  have same (xs : List α) (ys : List β) :
      zipListInto f xs ys = mapListInto id (xs.zipWith f ys) := by
    induction xs generalizing ys with
    | nil => rfl
    | cons x xs ih =>
      cases ys with
      | nil => rfl
      | cons y ys =>
        exact congrArg (fun tail (acc : Array γ) => f x y >>= fun z => tail (acc.push z)) (ih ys)
  rw [_root_.Array.zipWithM, zipArrayLists, mapArrayList, _root_.Array.toList_zipWith,
    List.drop_zero, List.drop_zero, same]

public theorem Array.allM_eq_not_anyM_not : type_of% @_root_.Array.allM_eq_not_anyM_not := by
  intro m α mon law p xs
  rw [_root_.Array.allM, bind_pure_comp]
  apply congrArg (Functor.map (! ·))
  exact Array.anyM_congr (xs := xs) rfl (fun a => bind_pure_comp ..) rfl rfl

public theorem Vector.allM_eq_not_anyM_not : type_of% @_root_.Vector.allM_eq_not_anyM_not := by
  intros
  exact _root_.Array.allM_eq_not_anyM_not

end OmegaChecks.InitPort.Alternatives
