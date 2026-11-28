module
public import OmegaChecks.InitPort.Alternatives.List.Implementations
public import OmegaChecks.InitPort.Alternatives.MonadicLists
public import OmegaChecks.InitPort.Alternatives.ListPairwise
public import OmegaChecks.InitPort.Alternatives.List.Replace
public import Init.Data.List.Lemmas
public import OmegaChecks.InitPort.Alternatives.ListAttach
public import OmegaChecks.InitPort.Alternatives.List.Endpoints
public import OmegaChecks.InitPort.Alternatives.List.Erase
public import OmegaChecks.InitPort.Alternatives.List.Find
public import OmegaChecks.InitPort.Alternatives.ListFilter
public import OmegaChecks.InitPort.Alternatives.ListCount
public import OmegaChecks.InitPort.Alternatives.ListLex
public import OmegaChecks.InitPort.Alternatives.ListMapIdx
public import OmegaChecks.InitPort.Alternatives.List.Scan
public import OmegaChecks.InitPort.Alternatives.List.Sort
public import OmegaChecks.InitPort.Alternatives.List.SplitOn
public import OmegaChecks.InitPort.Alternatives.ListSublist
public import OmegaChecks.InitPort.Alternatives.ListModify
public import OmegaChecks.InitPort.Alternatives.ListNat
public import OmegaChecks.InitPort.Alternatives.ListMinMax
import Init.Data.List.Impl
import all Init.Data.List.Control
import Init.Data.List.Monadic
import all Init.Data.List.MapIdx
import all Init.Data.Array.Basic
import Init.Data.Array.Find
import Init.Data.Array.Lemmas
import Init.Data.Array.Count
import all Init.Data.List.Find
import all Init.Data.List.ToArray

/-! Structural proofs for boolean predicates and folds over strict lists. -/

namespace OmegaChecks.InitPort.Alternatives

private theorem bindFoldAppend [Monad m] [LawfulMonad m] (f : β → α → m β)
    (xs ys : List α) (seed : m β) :
    (seed >>= fun b => (xs ++ ys).foldlM f b) =
      (seed >>= fun b => xs.foldlM f b) >>= fun b => ys.foldlM f b := by
  induction xs generalizing seed with
  | nil =>
    change (seed >>= fun b => ys.foldlM f b) = (seed >>= pure) >>= fun b => ys.foldlM f b
    rw [bind_pure]
  | cons a xs ih =>
    change (seed >>= fun b => f b a >>= fun c => (xs ++ ys).foldlM f c) =
      (seed >>= fun b => f b a >>= fun c => xs.foldlM f c) >>= fun b => ys.foldlM f b
    rw [← bind_assoc, ih, ← bind_assoc]
public theorem List.foldlM_append : type_of% @_root_.List.foldlM_append := by
  intro m α β _ _ f b xs ys
  have h := bindFoldAppend f xs ys (pure b)
  simpa only [pure_bind] using h
public theorem List.foldrM_append : type_of% @_root_.List.foldrM_append := by
  intro m α β _ _ f b xs ys
  unfold List.foldrM
  rw [List.reverse_append]
  exact _root_.List.foldlM_append

public theorem List.foldrM_cons : type_of% @_root_.List.foldrM_cons := by
  intro m α β _ _ a xs f b
  unfold _root_.List.foldrM
  rw [List.reverse_cons, _root_.List.foldlM_append]
  change (xs.reverse.foldlM (fun acc x => f x acc) b >>= fun acc => f a acc >>= pure) = _
  rw [← bind_assoc, bind_pure]

public theorem List.foldlM_pure : type_of% @_root_.List.foldlM_pure := by
  intro m β α monad lawful f b xs
  induction xs generalizing b with
  | nil => rfl
  | cons x xs ih =>
    rw [List.foldlM_cons, pure_bind]
    exact ih

public theorem List.map_const : type_of% @_root_.List.map_const := by
  intro α β xs b
  induction xs with
  | nil => rfl
  | cons a xs ih => exact (congrArg (b :: ·) ih).trans List.replicate_succ.symm

private theorem mapLoopId (f : α → Id β) (xs : List α) (acc : List β) :
    (List.mapM.loop f xs acc).run = acc.reverse ++ xs.map (fun x => (f x).run) := by
  induction xs generalizing acc with
  | nil => exact (List.append_nil _).symm
  | cons a xs ih =>
    change (List.mapM.loop f xs ((f a).run :: acc)).run = acc.reverse ++ ((f a).run :: xs.map (fun x => (f x).run))
    exact (ih _).trans ((congrArg (· ++ xs.map (fun x => (f x).run)) List.reverse_cons).trans (List.append_assoc ..))

public theorem List.idRun_mapM : type_of% @_root_.List.idRun_mapM :=
  fun {_ _ xs f} => mapLoopId f xs []

public theorem Option.eq_none_iff_forall_ne_some : type_of% @_root_.Option.eq_none_iff_forall_ne_some := by
  intro α o
  cases o with
  | none =>
    exact ⟨fun _ _ h => Option.some_ne_none _ h.symm, fun _ => rfl⟩
  | some a =>
    exact ⟨fun h => (Option.some_ne_none _ h).elim, fun denied => (denied a rfl).elim⟩

public theorem List.find?_append : type_of% @_root_.List.find?_append := by
  intro α p xs ys
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.cons_append, List.find?_cons, List.find?_cons, ih]
    cases p x <;> rfl

public theorem List.findSome?_append : type_of% @_root_.List.findSome?_append := by
  intro α β f xs ys
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.cons_append, List.findSome?_cons, List.findSome?_cons, ih]
    cases f x <;> rfl

public theorem List.any_eq_true {α : Type u} {p : α → Bool} {l : _root_.List α} :
    l.any p = true ↔ ∃ x, x ∈ l ∧ p x = true := by
  induction l with
  | nil =>
    exact ⟨fun h => False.elim (Bool.false_ne_true h),
      fun ⟨_, m, _⟩ => False.elim (List.not_mem_nil m)⟩
  | cons a xs ih =>
    change (p a || xs.any p) = true ↔ _
    constructor
    · intro h
      cases Bool.or_eq_true_iff.mp h with
      | inl pa => exact ⟨a, .head _, pa⟩
      | inr rest =>
        obtain ⟨x, m, px⟩ := ih.mp rest
        exact ⟨x, .tail _ m, px⟩
    · rintro ⟨x, m, px⟩
      cases List.mem_cons.mp m with
      | inl e => exact Bool.or_eq_true_iff.mpr (.inl (e ▸ px))
      | inr t => exact Bool.or_eq_true_iff.mpr (.inr (ih.mpr ⟨x, t, px⟩))

public theorem List.all_eq_true {α : Type u} {p : α → Bool} {l : _root_.List α} :
    l.all p = true ↔ ∀ x, x ∈ l → p x = true := by
  induction l with
  | nil => exact ⟨fun _ _ m => False.elim (List.not_mem_nil m), fun _ => rfl⟩
  | cons a xs ih =>
    change (p a && xs.all p) = true ↔ _
    constructor
    · intro h x m
      obtain ⟨pa, rest⟩ := Bool.and_eq_true_iff.mp h
      cases List.mem_cons.mp m with
      | inl e => exact e.symm ▸ pa
      | inr t => exact ih.mp rest x t
    · exact fun h => Bool.and_eq_true_iff.mpr ⟨h a (.head _), ih.mpr (fun x m => h x (.tail _ m))⟩

public theorem List.foldl_eq_foldlM {β : Type u} {α : Type v} {f : β → α → β}
    {b : β} {l : _root_.List α} :
    l.foldl f b = (l.foldlM (m := Id) (pure <| f · ·) b).run := by
  induction l generalizing b with
  | nil => rfl
  | cons a xs ih => exact ih (b := f b a)

public theorem List.foldl_reverse {α : Type u} {β : Type v} {l : _root_.List α} {f : β → α → β} {b : β} :
    l.reverse.foldl f b = l.foldr (fun x y => f y x) b := by
  induction l with
  | nil => rfl
  | cons a xs ih =>
    exact (congrArg (fun ys => ys.foldl f b) List.reverse_cons).trans
      ((List.foldl_append (f := f) (b := b) (l := xs.reverse) (l' := [a])).trans
        (congrArg (fun x => f x a) ih))

public theorem List.foldrM_pure : type_of% @_root_.List.foldrM_pure := by
  intro m α β monad lawful f b xs
  unfold _root_.List.foldrM
  rw [List.foldlM_pure, List.foldl_reverse]

public theorem List.foldr_eq_foldrM {α : Type u} {β : Type v} {f : α → β → β}
    {b : β} {l : _root_.List α} :
    l.foldr f b = (l.foldrM (m := Id) (pure <| f · ·) b).run :=
  List.foldl_reverse.symm.trans List.foldl_eq_foldlM

public theorem List.mem_filter : type_of% @_root_.List.mem_filter := by
  intro α p xs x
  induction xs with
  | nil => exact ⟨fun h => (List.not_mem_nil h).elim, fun h => (List.not_mem_nil h.1).elim⟩
  | cons a xs ih =>
    by_cases h : p a = true
    · rw [List.filter_cons_of_pos h]
      constructor
      · intro m
        cases List.mem_cons.mp m with
        | inl eq => exact ⟨List.mem_cons.mpr (.inl eq), eq.symm ▸ h⟩
        | inr rest => exact ⟨.tail _ (ih.mp rest).1, (ih.mp rest).2⟩
      · intro ⟨m, hit⟩
        cases List.mem_cons.mp m with
        | inl eq => exact List.mem_cons.mpr (.inl eq)
        | inr tail => exact .tail _ (ih.mpr ⟨tail, hit⟩)
    · rw [List.filter_cons_of_neg h]
      constructor
      · intro m
        exact ⟨.tail _ (ih.mp m).1, (ih.mp m).2⟩
      · intro ⟨m, hit⟩
        cases List.mem_cons.mp m with
        | inl eq => exact (h (eq ▸ hit)).elim
        | inr tail => exact ih.mpr ⟨tail, hit⟩

public theorem List.mem_filterMap : type_of% @_root_.List.mem_filterMap := by
  intro α β f xs b
  induction xs with
  | nil => exact ⟨fun m => (List.not_mem_nil m).elim, fun ⟨_, m, _⟩ => (List.not_mem_nil m).elim⟩
  | cons a xs ih =>
    cases h : f a with
    | none =>
      rw [List.filterMap_cons_none h]
      constructor
      · intro m
        obtain ⟨x, t, hit⟩ := ih.mp m
        exact ⟨x, .tail _ t, hit⟩
      · intro ⟨x, m, hit⟩
        cases List.mem_cons.mp m with
        | inl eq =>
          cases eq
          cases h.symm.trans hit
        | inr tail => exact ih.mpr ⟨x, tail, hit⟩
    | some v =>
      rw [List.filterMap_cons_some h]
      constructor
      · intro m
        cases List.mem_cons.mp m with
        | inl eq => exact ⟨a, .head _, eq.symm ▸ h⟩
        | inr tail =>
          obtain ⟨x, t, hit⟩ := ih.mp tail
          exact ⟨x, .tail _ t, hit⟩
      · intro ⟨x, m, hit⟩
        cases List.mem_cons.mp m with
        | inl eq =>
          cases eq
          exact List.mem_cons.mpr (.inl (Option.some.inj (hit.symm.trans h)))
        | inr tail => exact .tail _ (ih.mpr ⟨x, tail, hit⟩)

public theorem List.head_eq_iff_head?_eq_some : type_of% @_root_.List.head_eq_iff_head?_eq_some := by
  intro α a xs h
  cases xs with
  | nil => exact (h rfl).elim
  | cons _ _ => exact ⟨congrArg some, Option.some.inj⟩

public theorem List.filter_reverse : type_of% @_root_.List.filter_reverse := by
  intro α p xs
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    rw [List.reverse_cons, List.filter_append, ih]
    by_cases h : p a = true
    · rw [List.filter_cons_of_pos h, List.filter_cons_of_pos h, List.reverse_cons]
      rfl
    · rw [List.filter_cons_of_neg h, List.filter_cons_of_neg h]
      exact List.append_nil _

public theorem List.filterMap_filterMap : type_of% @_root_.List.filterMap_filterMap := by
  intro α β γ f g xs
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    cases fa : f a with
    | none =>
      have rhs : (f a).bind g = none := (congrArg (Option.bind · g) fa)
      rw [List.filterMap_cons_none fa, List.filterMap_cons_none (f := fun x => (f x).bind g) rhs]
      exact ih
    | some b =>
      have bind : (f a).bind g = g b := congrArg (Option.bind · g) fa
      cases gb : g b with
      | none =>
        rw [List.filterMap_cons_some fa, List.filterMap_cons_none gb, List.filterMap_cons_none (f := fun x => (f x).bind g) (bind.trans gb)]
        exact ih
      | some c =>
        rw [List.filterMap_cons_some fa, List.filterMap_cons_some gb, List.filterMap_cons_some (f := fun x => (f x).bind g) (bind.trans gb)]
        exact congrArg (c :: ·) ih

public theorem List.getElem_mapFinIdx_go : type_of% @_root_.List.getElem_mapFinIdx_go := by
  intro α β bs acc as f i h w
  induction bs generalizing acc with
  | nil =>
    have small : i < acc.size := w
    rw [dite_eq_left small]
    rfl
  | cons a bs ih =>
    have hacc : acc.size < as.length :=
      Nat.lt_of_lt_of_eq (Nat.lt_add_of_pos_left (Nat.zero_lt_succ bs.length)) h
    let next := acc.push (f acc.size a hacc)
    have len : next.size = acc.size + 1 := Array.size_push _
    have inv : bs.length + next.size = as.length :=
      (congrArg (bs.length + ·) len).trans ((Nat.succ_add bs.length acc.size).symm.trans h)
    have stepEq := ih (acc := next) (h := inv) (w := w)
    apply stepEq.trans
    by_cases small : i < acc.size
    · rw [dite_eq_left small, dite_eq_left (Nat.lt_of_lt_of_eq (Nat.lt_succ_of_lt small) len.symm)]
      exact Array.getElem_push_lt small
    · rw [dite_eq_right small]
      by_cases eq : i = acc.size
      · subst i
        rw [dite_eq_left (Nat.lt_of_lt_of_eq (Nat.lt_succ_self _) len.symm)]
        apply (Array.getElem_push_eq).trans
        congr 1
        exact (getElem_congr_idx (c := a :: bs) (w := by exact Nat.zero_lt_succ _) (Nat.sub_self _).symm)
      · have lt := Nat.lt_of_le_of_ne (Nat.le_of_not_lt small) (Ne.symm eq)
        have large : ¬i < next.size := Nat.not_lt_of_ge (len.symm ▸ lt)
        rw [dite_eq_right large]
        congr 1
        have ds : i - acc.size = (i - next.size).succ := by
          rw [len, Nat.sub_succ, Nat.succ_pred_eq_of_pos (Nat.sub_pos_of_lt lt)]
        have inBounds := Nat.sub_lt_right_of_lt_add (Nat.le_of_lt lt)
          (Nat.lt_of_lt_of_eq w (_root_.List.length_mapFinIdx_go.trans h.symm))
        exact (getElem_congr_idx (c := a :: bs) (w := inBounds) ds).symm


private theorem mapIndexLoop {α : Type u} {β : Type v} (as : List α) (f : Nat → α → β)
    (rest : List α) (acc : Array β) (h : rest.length + acc.size = as.length) :
    List.mapIdx.go f rest acc = List.mapFinIdx.go as (fun i a _ => f i a) rest acc h := by
  induction rest generalizing acc with
  | nil => rfl
  | cons a rest ih => exact ih (acc.push (f acc.size a)) _

public theorem List.mapIdx_eq_mapFinIdx : type_of% @_root_.List.mapIdx_eq_mapFinIdx :=
  fun {_ _ l f} => mapIndexLoop l f l #[] _

public theorem List.getElem_mapIdx : type_of% @_root_.List.getElem_mapIdx := by
  intro α β l f i h
  exact (getElem_congr_coll (c := List.mapIdx f l) (i := i) (w := h) (List.mapIdx_eq_mapFinIdx (l := l) (f := f))).trans
    _root_.List.getElem_mapFinIdx


public theorem List.instLawfulBEq : type_of% @_root_.List.instLawfulBEq := by
  intro α inst lawful
  refine @LawfulBEq.mk _ _ (@_root_.List.instReflBEq α inst (@LawfulBEq.toReflBEq α inst lawful)) ?_
  intro a
  induction a with
  | nil =>
    intro b h
    cases b with
    | nil => rfl
    | cons => exact nomatch h
  | cons x xs ih =>
    intro b h
    cases b with
    | nil => exact nomatch h
    | cons y ys =>
      change ((x == y) && (xs == ys)) = true at h
      cases hx : (x == y) with
      | false => rw [hx] at h; cases h
      | true =>
        rw [hx] at h
        cases eq_of_beq hx
        exact congrArg (_root_.List.cons x) (ih h)

public theorem List.of_concat_eq_concat : type_of% @_root_.List.of_concat_eq_concat := by
  intro α as bs a b
  induction as generalizing bs with
  | nil =>
    cases bs with
    | nil => exact fun h => ⟨rfl, (List.cons.inj h).1⟩
    | cons y ys => cases ys <;> intro h <;> cases h
  | cons x xs ih =>
    cases bs with
    | nil => cases xs <;> intro h <;> cases h
    | cons y ys =>
      intro h
      obtain ⟨rfl, tail⟩ := List.cons.inj h
      obtain ⟨rfl, last⟩ := ih tail
      exact ⟨rfl, last⟩

public theorem List.of_concat_eq_concat._f :
    type_of% @_root_.List.of_concat_eq_concat._f := by
  intro α a b as _ bs eq
  exact List.of_concat_eq_concat eq

public theorem List.mem_replicate : type_of% @_root_.List.mem_replicate := by
  intro α a b n
  induction n with
  | zero => exact ⟨fun h => (List.not_mem_nil h).elim, fun h => (h.1 rfl).elim⟩
  | succ n ih =>
    rw [List.replicate_succ]
    exact ⟨fun h => ⟨Nat.succ_ne_zero _, (List.mem_cons.mp h).elim id (fun t => (ih.mp t).2)⟩,
      fun h => List.mem_cons.mpr (.inl h.2)⟩

public theorem List.findSomeM?_pure : type_of% @_root_.List.findSomeM?_pure := by
  intro m α β monad lawful f xs
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    rw [List.findSomeM?_cons, pure_bind, List.findSome?_cons]
    cases f a with
    | none => exact ih
    | some b => rfl

public theorem List.countP_toArray : type_of% @_root_.List.countP_toArray := by
  intro α p xs
  rw [Array.countP, List.foldr_toArray]
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    rw [List.foldr_cons, List.countP_cons]
    cases h : p a with
    | false => exact ih
    | true => exact congrArg Nat.succ ih

private def findStep (f : α → Option β) (a : α) : ForInStep (Option (Option β) × Unit) :=
  match f a with
  | some b => .done (some (some b), ())
  | none => .yield (none, ())

set_option backward.isDefEq.respectTransparency false in
private theorem findSuffix (f : α → Option β) (l : List α)
    (step : (a : α) → a ∈ l.toArray → Option (Option β) × Unit → Id (ForInStep (Option (Option β) × Unit)))
    (compute : ∀ a m state, step a m state = findStep f a) (i : Nat) (bound : i ≤ l.length) :
    (Array.forIn'.loop (m := Id) l.toArray step i bound (none, ())).run.fst.join =
      (l.drop (l.length - i)).findSome? f := by
  induction i with
  | zero =>
    rw [Nat.sub_zero, List.drop_length]
    rfl
  | succ i ih =>
    have index : l.length - 1 - i < l.length := by omega
    have next : l.length - 1 - i + 1 = l.length - i := by omega
    have current : l.length - (i+1) = l.length - 1 - i := by omega
    rw [current, List.drop_eq_getElem_cons index, next, List.findSome?_cons, Array.forIn'.loop.eq_2]
    simp only [compute, List.size_toArray, List.getElem_toArray, Bind.bind, Pure.pure, Id.instMonad]
    cases h : f l[l.length-1-i] with
    | none =>
      simp only [findStep, h]
      exact ih (Nat.le_of_succ_le bound)
    | some b => simp only [findStep, h]; rfl

private theorem findArray (f : α → Option β) (l : List α)
    (step : (a : α) → a ∈ l.toArray → Option (Option β) × Unit → Id (ForInStep (Option (Option β) × Unit)))
    (compute : ∀ a m state, step a m state = findStep f a) :
    (Array.forIn'.loop (m := Id) l.toArray step l.length (Nat.le_refl _) (none, ())).fst.join = l.findSome? f := by
  have found := findSuffix f l step compute l.length (Nat.le_refl _)
  rw [Nat.sub_self, List.drop_zero] at found
  exact found

set_option backward.isDefEq.respectTransparency false in
public theorem List.findSome?_toArray : type_of% @_root_.List.findSome?_toArray := by
  intro α β f l
  unfold Array.findSome? Array.findSomeM?
  dsimp only [ForIn.forIn, instForInOfForIn', ForIn'.forIn', Array.forIn', Bind.bind, Pure.pure, Id.instMonad, Id.run]
  simp only [List.size_toArray]
  generalize hx : Prod.fst (Array.forIn'.loop (m := Id) (β := Option (Option β) × Unit)
    l.toArray _ l.length _ (none, ())) = v
  have result : v.join = l.findSome? f := by
    rw [← hx]
    apply findArray
    intro a _ state
    unfold findStep
    cases f a <;> rfl
  cases v <;> exact result

set_option backward.isDefEq.respectTransparency false in
public theorem List.find?_toArray : type_of% @_root_.List.find?_toArray := by
  intro α p l
  rw [← _root_.List.findSome?_guard]
  unfold Array.find?
  dsimp only [ForIn.forIn, instForInOfForIn', ForIn'.forIn', Array.forIn', Bind.bind, Pure.pure, Id.instMonad, Id.run]
  simp only [List.size_toArray]
  generalize hx : Prod.fst (Array.forIn'.loop (m := Id) (β := Option (Option α) × Unit)
    l.toArray _ l.length _ (none, ())) = v
  have result : v.join = l.findSome? (Option.guard p) := by
    rw [← hx]
    apply findArray
    intro a _ state
    unfold findStep Option.guard
    cases p a <;> rfl
  cases v <;> exact result

public theorem List.findIdx?_go_eq : type_of% (private_decl% @_root_.List.findIdx?_go_eq) := by
  intro α p xs i
  induction i with
  | zero => exact private_decl% _root_.List.findIdx?_go_succ
  | succ i ih =>
    have step : List.findIdx?.go p xs (i+1+1) = (List.findIdx?.go p xs (i+1)).map (· + 1) :=
      private_decl% _root_.List.findIdx?_go_succ
    rw [step, ih]
    cases List.findIdx?.go p xs 0 <;> rfl

public theorem List.findIdx?_cons : type_of% @_root_.List.findIdx?_cons := by
  intro α x xs p
  change (if p x then some 0 else List.findIdx?.go p xs 1) = _
  cases p x with
  | true => rfl
  | false => exact private_decl% _root_.List.findIdx?_go_eq

public theorem List.idxOf?_cons : type_of% @_root_.List.idxOf?_cons := by
  intro α inst a xs b
  exact List.findIdx?_cons

public theorem List.findIdx_eq_getD_findIdx? : type_of% @_root_.List.findIdx_eq_getD_findIdx? := by
  intro α xs p
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    rw [List.findIdx_cons, List.findIdx?_cons, ih]
    cases p a with
    | true => rfl
    | false => cases xs.findIdx? p <;> rfl

public theorem List.findIdx?_eq_some_iff_findIdx_eq :
    type_of% @_root_.List.findIdx?_eq_some_iff_findIdx_eq := by
  intro α xs p i
  induction xs generalizing i with
  | nil =>
    exact ⟨(fun h => by cases h), fun h => (Nat.not_lt_zero _ h.1).elim⟩
  | cons x xs ih =>
    rw [List.findIdx?_cons, List.findIdx_cons]
    cases h : p x with
    | true =>
      change some 0 = some i ↔ i < xs.length + 1 ∧ 0 = i
      exact ⟨fun hit => ⟨Option.some.inj hit ▸ Nat.zero_lt_succ _, Option.some.inj hit⟩,
        fun hit => congrArg some hit.2⟩
    | false =>
      change (xs.findIdx? p).map (· + 1) = some i ↔ i < xs.length + 1 ∧ xs.findIdx p + 1 = i
      constructor
      · intro hit
        obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.mp hit
        obtain ⟨lt, found⟩ := ih.mp hj
        exact ⟨Nat.succ_lt_succ lt, congrArg Nat.succ found⟩
      · rintro ⟨lt, rfl⟩
        rw [ih.mpr ⟨Nat.lt_of_succ_lt_succ lt, rfl⟩]
        rfl

public theorem List.findIdx?_eq_some_iff_getElem :
    type_of% @_root_.List.findIdx?_eq_some_iff_getElem := by
  intro α xs p i
  constructor
  · intro hit
    obtain ⟨bound, found⟩ := List.findIdx?_eq_some_iff_findIdx_eq.mp hit
    obtain ⟨here, before⟩ := (_root_.List.findIdx_eq bound).mp found
    exact ⟨bound, here, fun j hj => Bool.eq_false_iff.mp (before j hj)⟩
  · rintro ⟨bound, here, before⟩
    apply List.findIdx?_eq_some_iff_findIdx_eq.mpr
    exact ⟨bound, (_root_.List.findIdx_eq bound).mpr
      ⟨here, fun j hj => Bool.eq_false_iff.mpr (before j hj)⟩⟩

public theorem List.findIdx?_eq_none_iff : type_of% @_root_.List.findIdx?_eq_none_iff := by
  intro α xs p
  induction xs with
  | nil => exact ⟨fun _ x hx => (List.not_mem_nil hx).elim, fun _ => rfl⟩
  | cons a xs ih =>
    rw [List.findIdx?_cons]
    cases h : p a with
    | true =>
      constructor
      · intro bad
        change some 0 = (none : Option Nat) at bad
        cases bad
      · intro every
        exact (Bool.noConfusion (h.symm.trans (every a List.mem_cons_self)) : False).elim
    | false =>
      change (xs.findIdx? p).map (· + 1) = none ↔ _
      rw [Option.map_eq_none_iff]
      constructor
      · intro miss x hx
        obtain same | tail := List.mem_cons.mp hx
        · exact same ▸ h
        · exact ih.mp miss x tail
      · exact fun every => ih.mpr (fun x hx => every x (List.mem_cons_of_mem _ hx))

private theorem recoverFinIndex {n : Nat} (o : Option (Fin n)) (indices : Option Nat)
    (values : indices = o.map Fin.val) (bound : ∀ i, indices = some i → i < n) :
    o = indices.pmap (fun i hi => ⟨i, bound i hi⟩) (fun _ hi => hi) := by
  subst indices
  cases o <;> rfl

-- In the pinned list and array statements, the proof argument to Fin.mk
-- uses propext. The constructive bound below gives the same whole proposition
-- by proof irrelevance in the public kernels.
public theorem List.findFinIdx?_eq_pmap_findIdx? {α : Type u} {xs : List α} {p : α → Bool} :
    xs.findFinIdx? p = (xs.findIdx? p).pmap
      (fun i hit => ⟨i, (_root_.List.findIdx?_eq_some_iff_findIdx_eq.mp hit).1⟩) (fun _ h => h) := by
  exact recoverFinIndex _ _ _root_.List.findIdx?_eq_map_findFinIdx?_val
    (fun _ hit => (List.findIdx?_eq_some_iff_findIdx_eq.mp hit).1)

public theorem Array.findFinIdx?_eq_pmap_findIdx? {α : Type u} {xs : Array α} {p : α → Bool} :
    xs.findFinIdx? p = (xs.findIdx? p).pmap
      (fun i hit => ⟨i, (_root_.Array.findIdx?_eq_some_iff_findIdx_eq.mp hit).1⟩) (fun _ h => h) := by
  exact recoverFinIndex _ _ _root_.Array.findIdx?_eq_map_findFinIdx?_val
    (fun _ hit => (_root_.Array.findIdx?_eq_some_iff_findIdx_eq.mp hit).1)

public theorem List.findFinIdx?_cons : type_of% @_root_.List.findFinIdx?_cons := by
  intro α p x xs
  apply (Option.map_inj_right (f := Fin.val) (fun _ _ => Fin.eq_of_val_eq)).mp
  rw [← _root_.List.findIdx?_eq_map_findFinIdx?_val, List.findIdx?_cons]
  cases h : p x with
  | true => rfl
  | false =>
    rw [_root_.List.findIdx?_eq_map_findFinIdx?_val]
    cases xs.findFinIdx? p <;> rfl

public theorem List.findFinIdx?_eq_some_iff : type_of% @_root_.List.findFinIdx?_eq_some_iff := by
  intro α xs p i
  have atIndex : xs.findFinIdx? p = some i ↔ xs.findIdx? p = some i.val := by
    rw [_root_.List.findIdx?_eq_map_findFinIdx?_val]
    exact (Option.map_inj_right (o' := some i) (f := Fin.val) (fun _ _ => Fin.eq_of_val_eq)).symm
  constructor
  · intro hit
    obtain ⟨_, here, before⟩ := List.findIdx?_eq_some_iff_getElem.mp (atIndex.mp hit)
    exact ⟨here, fun j hj => before j.val hj⟩
  · rintro ⟨here, before⟩
    exact atIndex.mpr (List.findIdx?_eq_some_iff_getElem.mpr
      ⟨i.isLt, here, fun j hj => before ⟨j, Nat.lt_trans hj i.isLt⟩ hj⟩)

public theorem List.findFinIdx?_eq_none_iff : type_of% @_root_.List.findFinIdx?_eq_none_iff := by
  intro α xs p
  have missing : xs.findFinIdx? p = none ↔ xs.findIdx? p = none := by
    rw [_root_.List.findIdx?_eq_map_findFinIdx?_val]
    exact Option.map_eq_none_iff.symm
  exact ⟨fun h x hx => Bool.eq_false_iff.mp (List.findIdx?_eq_none_iff.mp (missing.mp h) x hx),
    fun h => missing.mpr (List.findIdx?_eq_none_iff.mpr (fun x hx => Bool.eq_false_iff.mpr (h x hx)))⟩

public theorem List.findIdx?_isSome : type_of% @_root_.List.findIdx?_isSome := by
  intro α xs p
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.findIdx?_cons, List.any_cons]
    cases p x with
    | true => rfl
    | false => rw [← ih]; cases xs.findIdx? p <;> rfl

public theorem List.findIdx?_isNone : type_of% @_root_.List.findIdx?_isNone := by
  intro α xs p
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.findIdx?_cons, List.all_cons]
    cases h : p x with
    | true => rfl
    | false => rw [← ih]; cases xs.findIdx? p <;> rfl

private theorem insertAtSplit (xs : List α) (i : Nat) (a : α) (h : i ≤ xs.length) :
    xs.take i ++ a :: xs.drop i = xs.insertIdx i a := by
  induction i generalizing xs with
  | zero => rfl
  | succ i ih =>
    cases xs with
    | nil => exact (Nat.not_succ_le_zero _ h).elim
    | cons x xs => exact congrArg (x :: ·) (ih xs (Nat.le_of_succ_le_succ h))

private theorem insertLoopCongr (i j : Nat) {s t : Array α} (same : s = t) (hs : j < s.size) (ht : j < t.size) :
    Array.insertIdx.loop i s ⟨j, hs⟩ = Array.insertIdx.loop i t ⟨j, ht⟩ := by
  cases same
  rfl

public theorem List.insertIdx_toArray : type_of% @_root_.List.insertIdx_toArray := by
  intro α l i a h
  have hi : i ≤ l.length := h
  have hj : l.length < (l ++ [a]).toArray.size := by
    rw [List.size_toArray, List.length_append]
    exact Nat.lt_succ_self _
  have loop := (private_decl% @List.insertIdx_loop_toArray) i (l ++ [a]) l.length hj hi
  have dropEnd : (l ++ [a]).drop (l.length + 1) = [] := by
    apply List.drop_eq_nil_of_le
    rw [List.length_append]
    exact Nat.le_refl _
  rw [List.take_append_of_le_length hi, List.take_left, List.getElem_concat_length rfl, dropEnd, List.append_nil,
    insertAtSplit l i a hi] at loop
  unfold Array.insertIdx
  exact (insertLoopCongr i l.length (List.push_toArray l a) (by rw [Array.size_push, List.size_toArray]; exact Nat.lt_succ_self _) hj).trans loop

private theorem readAfterInsert (xs : List α) (a : α) (i k : Nat) (order : i ≤ k)
    (has : k + 1 < (xs.insertIdx i a).length) (old : k < xs.length) :
    (xs.insertIdx i a)[k+1] = xs[k] := by
  induction i generalizing xs k with
  | zero => rfl
  | succ i ih =>
    cases xs with
    | nil => exact (Nat.not_succ_le_zero _ old).elim
    | cons x xs =>
      cases k with
      | zero => exact (Nat.not_succ_le_zero _ order).elim
      | succ k => exact ih xs k (Nat.le_of_succ_le_succ order) (Nat.lt_of_succ_lt_succ has) (Nat.lt_of_succ_lt_succ old)

public theorem List.getElem_insertIdx_of_gt : type_of% @_root_.List.getElem_insertIdx_of_gt := by
  intro α l a i j less bound
  cases j with
  | zero => exact (Nat.not_succ_le_zero _ less).elim
  | succ k =>
    apply readAfterInsert l a i k (Nat.le_of_lt_succ less) bound

public theorem List.getElem_insertIdx_self : type_of% @_root_.List.getElem_insertIdx_self := by
  intro α l a i bound
  induction i generalizing l with
  | zero => rfl
  | succ i ih =>
    cases l with
    | nil => exact (Nat.not_succ_le_zero _ bound).elim
    | cons x xs => exact ih (Nat.lt_of_succ_lt_succ bound)

public theorem List.getElem_insertIdx_of_lt : type_of% @_root_.List.getElem_insertIdx_of_lt := by
  intro α l a i j before bound
  induction i generalizing l j with
  | zero => exact (Nat.not_succ_le_zero _ before).elim
  | succ i ih =>
    cases l with
    | nil => exact (Nat.not_succ_le_zero _ bound).elim
    | cons x xs =>
      cases j with
      | zero => rfl
      | succ j => exact ih (Nat.lt_of_succ_lt_succ before) (Nat.lt_of_succ_lt_succ bound)

public theorem List.append_eq_append_iff : type_of% @_root_.List.append_eq_append_iff := by
  intro α ws xs ys zs
  constructor
  · induction ws generalizing ys with
    | nil => intro eq; exact .inl ⟨ys, rfl, eq⟩
    | cons w ws ih =>
      intro eq
      cases ys with
      | nil => exact .inr ⟨w :: ws, rfl, eq.symm⟩
      | cons y ys =>
        obtain ⟨rfl, rest⟩ := _root_.List.cons.inj eq
        obtain (⟨as, rfl, right⟩ | ⟨cs, rfl, right⟩) := ih rest
        · exact .inl ⟨as, rfl, right⟩
        · exact .inr ⟨cs, rfl, right⟩
  · rintro (⟨as, rfl, rfl⟩ | ⟨cs, rfl, rfl⟩)
    · exact (_root_.List.append_assoc ..).symm
    · exact _root_.List.append_assoc ..


public theorem List.getLast?_flatMap : type_of% @_root_.List.getLast?_flatMap := by
  intro α β xs f
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [_root_.List.flatMap_cons, _root_.List.getLast?_append, ih,
      _root_.List.reverse_cons, _root_.List.findSome?_append, _root_.List.findSome?_cons]
    cases (f x).getLast? <;> rfl

end OmegaChecks.InitPort.Alternatives
