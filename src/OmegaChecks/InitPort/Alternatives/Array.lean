module
import all Init.Data.Array.Lemmas
public import OmegaChecks.InitPort.Alternatives.ArrayAppend
public import OmegaChecks.InitPort.Alternatives.ArrayAttachments
public import OmegaChecks.InitPort.Alternatives.ArrayErase
public import OmegaChecks.InitPort.Alternatives.ArrayLex
public import OmegaChecks.InitPort.Alternatives.ArrayFind
public import OmegaChecks.InitPort.Alternatives.ArrayMapIdx
public import OmegaChecks.InitPort.Alternatives.Vector

public import Init.Data.RArray
import all Init.Data.RArray
public import Init.Data.Array.DecidableEq
public import Init.Data.Array.Basic
import all Init.Data.Array.Basic
public import Init.Data.Nat.Basic
import all Init.Data.Array.Basic
import all Init.Data.List.ToArray
import Init.Data.Array.Lemmas
import all Init.Data.Array.MapIdx
import Init.Data.Slice.Array.Iterator
import Init.Data.Array.InsertIdx
import all Init.Data.Vector.Basic

/-! List-backed implementations and induction proofs for the pinned array interfaces. -/

namespace OmegaChecks.InitPort.Alternatives

@[expose] public noncomputable def Lean.RArray.getImpl : type_of% @_root_.Lean.RArray.getImpl :=
  @_root_.Lean.RArray.get

public theorem Lean.RArray.get_eq_getImpl : @_root_.Lean.RArray.get = @Lean.RArray.getImpl := rfl

private theorem getBranch {α : Type u} (p : Nat) (l r : _root_.Lean.RArray α) (i : Nat) :
    Lean.RArray.getImpl (.branch p l r) i =
      if i < p then Lean.RArray.getImpl l i else Lean.RArray.getImpl r i := by
  by_cases h : i < p
  · rw [ite_eq_left h]
    change (Nat.ble p i).rec (l.get i) (r.get i) = l.get i
    cases e : Nat.ble p i with
    | false => rfl
    | true => exact (Nat.not_le_of_lt h (Nat.ble_eq.mp e)).elim
  · rw [ite_eq_right h]
    change (Nat.ble p i).rec (l.get i) (r.get i) = r.get i
    rw [show Nat.ble p i = true from Nat.ble_eq.mpr (Nat.le_of_not_lt h)]

public theorem _root_.OmegaChecks.InitPort.AlternativeEquations.Lean.RArray.getImpl.eq_2 {α : Type u}
    (i p : Nat) (l r : _root_.Lean.RArray α) :
    Lean.RArray.getImpl (.branch p l r) i =
      if i < p then Lean.RArray.getImpl l i else Lean.RArray.getImpl r i := getBranch p l r i

public theorem _root_.OmegaChecks.InitPort.AlternativeEquations.Lean.RArray.getImpl.eq_def {α : Type u}
    (a : _root_.Lean.RArray α) (i : Nat) :
    Lean.RArray.getImpl a i = _root_.Lean.RArray.getImpl.match_1 (fun _ => α) a id
      (fun p l r => if i < p then Lean.RArray.getImpl l i else Lean.RArray.getImpl r i) := by
  cases a with
  | leaf x => rfl
  | branch p l r => exact getBranch p l r i

@[expose] public def Array.instDecidableEq : type_of% @_root_.Array.instDecidableEq :=
  @_root_.Array.instDecidableEqImpl

public theorem Array.instDecidableEq_csimp : @Array.instDecidableEq = @_root_.Array.instDecidableEqImpl := rfl

@[expose] public def Array.instDecidableEqEmpImpl : type_of% @_root_.Array.instDecidableEqEmpImpl :=
  @_root_.Array.instDecidableEqEmp

public theorem Array.instDecidableEqEmp_csimp : @_root_.Array.instDecidableEqEmp = @Array.instDecidableEqEmpImpl := rfl

@[expose] public def Array.instDecidableEmpEqImpl : type_of% @_root_.Array.instDecidableEmpEqImpl :=
  @_root_.Array.instDecidableEmpEq

public theorem Array.instDecidableEmpEq_csimp : @_root_.Array.instDecidableEmpEq = @Array.instDecidableEmpEqImpl := rfl

public theorem Array.mem_dite_empty_left : type_of% @_root_.Array.mem_dite_empty_left := by
  intro α p x _ xs
  by_cases h : p
  · rw [dite_eq_left h]
    exact ⟨fun m => (_root_.Array.not_mem_empty x m).elim, fun ⟨hn, _⟩ => (hn h).elim⟩
  · rw [dite_eq_right h]
    exact ⟨fun m => ⟨h, m⟩, fun ⟨_, m⟩ => m⟩

public theorem Array.mem_ite_empty_left : type_of% @_root_.Array.mem_ite_empty_left := by
  intro α p x _ xs
  by_cases h : p
  · rw [ite_eq_left h]
    exact ⟨fun m => (_root_.Array.not_mem_empty x m).elim, fun m => (m.1 h).elim⟩
  · rw [ite_eq_right h]
    exact ⟨fun m => ⟨h, m⟩, And.right⟩

public theorem Array.map_inj : type_of% @_root_.Array.map_inj := by
  intro α β f g
  constructor
  · intro eq
    with_unfolding_all exact congrArg (fun k x => (k #[x]).toList.headD (f x)) eq
  · rintro rfl
    rfl

public theorem Array.replicate_beq_replicate : type_of% @_root_.Array.replicate_beq_replicate := by
  intros
  rw [← _root_.Array.beq_toList, _root_.Array.toList_replicate, _root_.Array.toList_replicate]
  exact _root_.List.replicate_beq_replicate

public theorem Array.filter_eq_append_iff : type_of% @_root_.Array.filter_eq_append_iff := by
  intro α xs ys zs p
  constructor
  · intro eq
    have split := _root_.Array.toList_filter.symm.trans ((congrArg Array.toList eq).trans _root_.Array.toList_append)
    obtain ⟨a, b, hab, ha, hb⟩ := _root_.List.filter_eq_append_iff.mp split
    exact ⟨a.toArray, b.toArray, _root_.Array.ext' (hab.trans _root_.Array.toList_append.symm),
      _root_.Array.ext' (_root_.Array.toList_filter.trans ha),
      _root_.Array.ext' (_root_.Array.toList_filter.trans hb)⟩
  · rintro ⟨a, b, rfl, rfl, rfl⟩
    exact _root_.Array.filter_append _root_.Array.size_append

public theorem Array.map_const : type_of% @_root_.Array.map_const := by
  intro α β xs b
  apply Array.ext'
  exact Array.toList_map.trans (_root_.List.map_const.trans Array.toList_replicate.symm)

private theorem mapFinIdxSize (xs : Array α) (f : (i : Nat) → α → i < xs.size → β)
    (i j : Nat) (inv : i + j = xs.size) (acc : Array β) :
    (Array.mapFinIdxM.map (m := Id) xs (fun k x h => f k x h) i j inv acc).size = acc.size + i := by
  induction i generalizing j acc with
  | zero => rfl
  | succ i ih =>
    rw [Array.mapFinIdxM.map.eq_def]
    dsimp only [Bind.bind, Id.instMonad]
    exact (ih ..).trans ((congrArg (· + i) (Array.size_push _)).trans (Nat.succ_add _ i))


public theorem Array.mapFinIdx_induction : type_of% @_root_.Array.mapFinIdx_induction := by
  intro α β xs f motive h0 p hs
  have loop (i j : Nat) (inv : i + j = xs.size) (acc : Array β)
      (len : acc.size = j) (hm : motive j)
      (valid : ∀ k (hk : k < acc.size) (h : k < xs.size), p k acc[k] h) :
      let out : Array β := _root_.Array.mapFinIdxM.map (m := Id) xs (fun k x h => f k x h) i j inv acc
      motive xs.size ∧ ∃ eq : out.size = xs.size, ∀ k h, p k (out[k]'(Nat.lt_of_lt_of_eq h eq.symm)) h := by
    induction i generalizing acc j with
    | zero =>
      have ej := (Nat.zero_add j).symm.trans inv
      exact ⟨ej ▸ hm, len.trans ej, fun _ _ => valid ..⟩
    | succ i ih =>
      rw [Array.mapFinIdxM.map.eq_def]
      have hj : j < xs.size := Nat.lt_of_lt_of_eq (Nat.lt_add_of_pos_left (Nat.zero_lt_succ i)) inv
      have hi : i + (j+1) = xs.size := (Nat.succ_add i j).symm.trans inv
      have pair := hs j hj hm
      apply ih (j+1) hi (acc.push (f j xs[j] hj)) ((_root_.Array.size_push _).trans (congrArg Nat.succ len)) pair.2
      intro k hk h
      by_cases hacc : k < acc.size
      · rw [Array.getElem_push_lt hacc]
        exact valid k hacc h
      · have kEq : k = acc.size := Nat.le_antisymm
          (Nat.le_of_lt_succ (Nat.lt_of_lt_of_eq hk (_root_.Array.size_push _))) (Nat.le_of_not_lt hacc)
        subst k
        rw [Array.getElem_push_eq]
        cases len
        exact pair.1
  exact loop xs.size 0 rfl (Array.emptyWithCapacity xs.size) rfl h0
    (fun k hk _ => (Nat.not_succ_le_zero k hk).elim)

public theorem Array.size_mapFinIdx : type_of% @_root_.Array.size_mapFinIdx := by
  intro α β xs f
  exact (mapFinIdxSize xs f xs.size 0 rfl (Array.emptyWithCapacity xs.size)).trans (Nat.zero_add _)

public theorem Array.size_mapIdx : type_of% @_root_.Array.size_mapIdx :=
  fun {_ _ f xs} => Array.size_mapFinIdx (xs := xs) (f := fun i x _ => f i x)

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

public theorem Array.toList_append : type_of% @_root_.Array.toList_append := by
  intro α xs ys
  change (_root_.Array.foldl _root_.Array.push xs ys).toList = _
  rw [← _root_.Array.foldl_toList]
  induction ys.toList generalizing xs with
  | nil => exact (_root_.List.append_nil _).symm
  | cons a l ih =>
    refine (ih (xs := xs.push a)).trans ?_
    rw [_root_.Array.toList_push, _root_.List.append_assoc]
    rfl

private theorem liftTrueBranch {p : Prop} [d : Decidable p] (h : p)
    (yes : p → β → γ) (no : ¬p → β → γ) :
    (fun b => if hp : p then yes hp b else no hp b) = yes h := by
  cases d with
  | isTrue => rfl
  | isFalse reject => exact (reject h).elim

private theorem constantBranches {p : Prop} [d : Decidable p] (f : β → γ) :
    (fun b => if p then f b else f b) = f := by cases d <;> rfl

private theorem foldLoopZero [Monad m] (f : β → α → m β) (xs : _root_.Array α) (limit j : Nat)
    (bound : limit ≤ xs.size) :
    _root_.Array.foldlM.loop f xs limit bound 0 j = pure := by
  exact constantBranches (p := j < limit) _

private theorem foldLoopSucc [Monad m] (f : β → α → m β) (xs : _root_.Array α) (limit i j : Nat)
    (bound : limit ≤ xs.size) (inside : j < limit) :
    _root_.Array.foldlM.loop f xs limit bound (i+1) j =
      fun b => f b (xs[j]'(Nat.lt_of_lt_of_le inside bound)) >>=
        _root_.Array.foldlM.loop f xs limit bound i (j+1) := by
  apply liftTrueBranch (p := j < limit) inside

private theorem liftFalseBranch {p : Prop} [d : Decidable p] (h : ¬p)
    (yes : p → β → γ) (no : ¬p → β → γ) :
    (fun b => if hp : p then yes hp b else no hp b) = no h := by
  cases d with
  | isTrue hp => exact (h hp).elim
  | isFalse => rfl

private theorem foldListTail [Monad m] (f : β → α → m β) (xs : _root_.Array α)
    (i j : Nat) (room : xs.size ≤ i+j) :
    _root_.Array.foldlM.loop f xs xs.size (Nat.le_refl _) i j =
      fun b => (xs.toList.drop j).foldlM f b := by
  induction i generalizing j with
  | zero =>
    rw [foldLoopZero, List.drop_eq_nil_of_le ((Nat.zero_add j) ▸ room)]
    rfl
  | succ i ih =>
    by_cases bound : j < xs.size
    · rw [foldLoopSucc f xs _ _ _ _ bound, ih (j+1) (Eq.subst (motive := (xs.size ≤ ·)) (Nat.succ_add i j) room)]
      exact congrArg (fun l => fun b => l.foldlM f b) (List.getElem_cons_drop (as := xs.toList) bound)
    · rw [List.drop_eq_nil_of_le (Nat.le_of_not_gt bound)]
      apply liftFalseBranch (p := j < xs.size) bound

public theorem Array.foldlM_toList.aux : type_of% @_root_.Array.foldlM_toList.aux := by
  intro m β α monad f xs i j room b
  exact congrFun (foldListTail f xs i j room) b

public theorem Array.foldlM_toList.aux._unary : type_of% @_root_.Array.foldlM_toList.aux._unary := by
  intro α xs packed
  obtain ⟨m, β, inst, f, i, j, h, b⟩ := packed
  exact @Array.foldlM_toList.aux m β α inst f xs i j h b

public theorem Array.foldlM_toList : type_of% @_root_.Array.foldlM_toList := by
  intro m β α monad f b xs
  unfold _root_.Array.foldlM
  rw [dite_eq_left (Nat.le_refl _)]
  exact (congrFun (foldListTail f xs xs.size 0 (Nat.le_refl _)) b).symm

private theorem foldExtractLoop [Monad m] (f : β → α → m β) (xs : _root_.Array α)
    (start stop : Nat) (i k : Nat) (w : i + k = (xs.extract start stop).size) :
    _root_.Array.foldlM.loop f xs (min stop xs.size) (Nat.min_le_right ..) i (start + k) =
      _root_.Array.foldlM.loop f (xs.extract start stop) _ (Nat.le_refl _) i k := by
  induction i generalizing k with
  | zero => rw [foldLoopZero, foldLoopZero]
  | succ i ih =>
    have room : k < (xs.extract start stop).size := by omega
    have lt : start + k < min stop xs.size := by
      rw [Array.size_extract] at room
      omega
    rw [foldLoopSucc _ _ _ _ _ _ lt, foldLoopSucc _ _ _ _ _ _ room,
      Array.getElem_extract, Nat.add_assoc, ih (k+1) ((Nat.succ_add ..).symm.trans w)]

public theorem Array.foldlM_start_stop : type_of% @_root_.Array.foldlM_start_stop := by
  intro α β m monad xs f b start stop
  have aligned := foldExtractLoop f xs start stop (xs.extract start stop).size 0 rfl
  have point := congrFun aligned b
  unfold _root_.Array.foldlM
  rw [dite_eq_left (Nat.le_refl (xs.extract start stop).size)]
  dsimp only
  split
  · rename_i within
    simpa only [Nat.sub_zero, Array.size_extract, Nat.min_eq_left within, Nat.add_zero] using point
  · rename_i past
    simpa only [Nat.sub_zero, Array.size_extract, Nat.min_eq_right (Nat.le_of_not_ge past), Nat.add_zero] using point

private theorem conditionalFunctions {p : Prop} [d : Decidable p] (yes no : β → γ) :
    (fun b => if p then yes b else no b) = (if p then yes else no) := by cases d <;> rfl

private theorem foldAtStop [Monad m] (f : α → β → m β) (xs : _root_.Array α)
    (j : Nat) (bound : j ≤ xs.size) : _root_.Array.foldrM.fold f xs j j bound = pure := by
  cases j with
  | zero => rfl
  | succ j =>
    apply (conditionalFunctions ..).trans
    exact ite_eq_left (Nat.beq_refl _)

private theorem foldBefore [Monad m] (f : α → β → m β) (xs : _root_.Array α)
    (stop j : Nat) (bound : j+1 ≤ xs.size) (advance : stop < j+1) :
    _root_.Array.foldrM.fold f xs stop (j+1) bound =
      fun b => f xs[j] b >>= _root_.Array.foldrM.fold f xs stop j (Nat.le_of_lt bound) := by
  apply (conditionalFunctions ..).trans
  exact ite_eq_right (fun h => (Nat.ne_of_gt advance) (Nat.eq_of_beq_eq_true h))

private theorem foldRightExtract [Monad m] (f : α → β → m β) (xs : _root_.Array α)
    (stop start i : Nat) (h : i ≤ (xs.extract stop start).size) (source : stop + i ≤ xs.size) :
    _root_.Array.foldrM.fold f xs stop (stop + i) source =
      _root_.Array.foldrM.fold f (xs.extract stop start) 0 i h := by
  induction i with
  | zero => exact (foldAtStop ..).trans (foldAtStop ..).symm
  | succ i ih =>
    simp only [Nat.add_succ] at source ⊢
    rw [foldBefore f xs stop (stop + i) source (Nat.lt_succ_of_le (Nat.le_add_right ..)),
      foldBefore _ _ _ _ _ (Nat.zero_lt_succ _), Array.getElem_extract,
      ih (Nat.le_of_lt h) (Nat.le_of_lt source)]

private theorem foldRightUntil [Monad m] (f : α → β → m β) (xs : _root_.Array α)
    (start stop bound : Nat) (effective : min start xs.size = bound) (b : β) (hb : bound ≤ xs.size) :
    (if stop < bound then _root_.Array.foldrM.fold f xs stop bound hb b else pure b) =
      (xs.extract stop start).foldrM f b := by
  let ys := xs.extract stop start
  have size : ys.size = bound - stop := Array.size_extract.trans (congrArg (· - stop) effective)
  unfold _root_.Array.foldrM
  rw [dite_eq_left (Nat.le_refl ys.size)]
  by_cases inside : stop < bound
  · have pos : 0 < ys.size := size.symm ▸ Nat.sub_pos_of_lt inside
    rw [ite_eq_left inside, ite_eq_left pos]
    have endPos : stop + ys.size = bound := by rw [size]; omega
    have point := congrFun (foldRightExtract f xs stop start ys.size (Nat.le_refl _)
      (endPos ▸ hb)) b
    simpa only [endPos] using point
  · have zero : ys.size = 0 := size.trans (Nat.sub_eq_zero_of_le (Nat.le_of_not_gt inside))
    rw [ite_eq_right inside, ite_eq_right (show ¬ 0 < ys.size from zero ▸ Nat.lt_irrefl 0)]

public theorem Array.foldrM_start_stop : type_of% @_root_.Array.foldrM_start_stop := by
  intro α β m monad xs f b start stop
  conv => lhs; unfold _root_.Array.foldrM
  split
  · rename_i h
    exact foldRightUntil f xs start stop start (Nat.min_eq_left h) b h
  · rename_i h
    exact foldRightUntil f xs start stop xs.size (Nat.min_eq_right (Nat.le_of_not_ge h)) b (Nat.le_refl _)

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

private theorem foldReversePrefix [Monad m] (f : α → β → m β) (xs : _root_.Array α)
    (i : Nat) (bound : i ≤ xs.size) :
    _root_.Array.foldrM.fold f xs 0 i bound =
      fun b => (xs.toList.take i).reverse.foldlM (fun acc a => f a acc) b := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [foldBefore _ _ _ _ _ (Nat.zero_lt_succ _), ih (Nat.le_of_lt bound),
      ← takeNext xs.toList i bound, List.reverse_concat]
    rfl

private theorem foldrAsList [Monad m] (f : α → β → m β) (xs : _root_.Array α) :
    (fun b => xs.foldrM f b) = fun b => xs.toList.reverse.foldlM (fun acc a => f a acc) b := by
  unfold _root_.Array.foldrM
  apply (liftTrueBranch (p := xs.size ≤ xs.size) (Nat.le_refl _) _ _).trans
  apply (conditionalFunctions ..).trans
  by_cases h : 0 < xs.size
  · rw [ite_eq_left h, foldReversePrefix]
    exact congrArg (fun l : List α => fun b => l.reverse.foldlM (fun acc a => f a acc) b) (takeAll xs.toList)
  · rw [ite_eq_right h]
    obtain ⟨l⟩ := xs
    cases l with
    | nil => rfl
    | cons a as => exact (h (Nat.zero_lt_succ _)).elim

private theorem foldlAsList [Monad m] (f : β → α → m β) (xs : _root_.Array α) :
    (fun b => xs.foldlM f b) = fun b => xs.toList.foldlM f b := by
  unfold _root_.Array.foldlM
  apply (liftTrueBranch (p := xs.size ≤ xs.size) (Nat.le_refl _) _ _).trans
  exact foldListTail f xs xs.size 0 (Nat.le_refl _)

public theorem Array.foldlM_append : type_of% @_root_.Array.foldlM_append := by
  intro m α β _ _ f b xs ys
  rw [← _root_.Array.foldlM_toList, _root_.Array.toList_append, _root_.List.foldlM_append,
    ← _root_.Array.foldlM_toList]
  exact congrArg (fun k => xs.toList.foldlM f b >>= k) (foldlAsList f ys).symm

public theorem Array.foldlM_append' : type_of% @_root_.Array.foldlM_append' := by
  intro m α β _ _ f b xs ys stop h
  subst stop
  rw [← _root_.Array.size_append]
  exact _root_.Array.foldlM_append

public theorem Array.foldrM_append : type_of% @_root_.Array.foldrM_append := by
  intro m α β _ _ f b xs ys
  rw [_root_.Array.foldrM_eq_reverse_foldlM_toList, _root_.Array.toList_append,
    List.reverse_append, _root_.List.foldlM_append, _root_.Array.foldrM_eq_reverse_foldlM_toList]
  exact congrArg (fun k => ys.toList.reverse.foldlM (fun acc a => f a acc) b >>= k) (foldrAsList f xs).symm

public theorem Array.foldrM_append' : type_of% @_root_.Array.foldrM_append' := by
  intro m α β _ _ f b xs ys start h
  subst start
  rw [← _root_.Array.size_append]
  exact _root_.Array.foldrM_append

public theorem Array.foldlM_push : type_of% @_root_.Array.foldlM_push := by
  intro m α β _ _ xs a f b
  rw [← _root_.Array.foldlM_toList, _root_.Array.toList_push, _root_.List.foldlM_append,
    ← _root_.Array.foldlM_toList]
  change (xs.toList.foldlM f b >>= fun acc => f acc a >>= pure) = _
  rw [← bind_assoc, bind_pure]

public theorem Array.foldlM_push' : type_of% @_root_.Array.foldlM_push' := by
  intro m α β _ _ xs a f b stop h
  subst stop
  rw [← _root_.Array.size_push (xs := xs) a]
  exact _root_.Array.foldlM_push

public theorem Array.foldrM_push : type_of% @_root_.Array.foldrM_push := by
  intro m α β mon f b xs a
  rw [_root_.Array.foldrM_eq_reverse_foldlM_toList, _root_.Array.toList_push, List.reverse_concat]
  exact congrArg (fun cont => f a b >>= cont) (foldrAsList f xs).symm

public theorem Array.foldrM_push' : type_of% @_root_.Array.foldrM_push' := by
  intro m α β mon f b xs a start h
  subst start
  exact (congrArg (fun k => (xs.push a).foldrM f b k 0) (_root_.Array.size_push a).symm).trans
    (_root_.Array.foldrM_push (xs := xs))

public theorem Array.foldrM_eq_reverse_foldlM_toList.aux :
    type_of% @_root_.Array.foldrM_eq_reverse_foldlM_toList.aux := by
  intro m α β monad f xs b i h
  exact (congrFun (foldReversePrefix f xs i h) b).symm

public theorem Array.foldrM_eq_reverse_foldlM_toList.aux._f :
    type_of% @_root_.Array.foldrM_eq_reverse_foldlM_toList.aux._f := by
  intro m α β inst f xs i _ init h
  exact @Array.foldrM_eq_reverse_foldlM_toList.aux m α β inst f xs init i h

public theorem Array.foldrM_eq_reverse_foldlM_toList :
    type_of% @_root_.Array.foldrM_eq_reverse_foldlM_toList := by
  intro m α β monad f b xs
  unfold _root_.Array.foldrM
  rw [dite_eq_left (Nat.le_refl _)]
  by_cases nonempty : 0 < xs.size
  · rw [ite_eq_left nonempty, foldReversePrefix]
    exact congrArg (fun l : List α => l.reverse.foldlM (fun acc a => f a acc) b) (takeAll xs.toList)
  · obtain ⟨l⟩ := xs
    cases l with
    | nil => rfl
    | cons a as => exact (nonempty (Nat.zero_lt_succ _)).elim

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

public theorem Array.foldr_induction.go : type_of% (private_decl% @_root_.Array.foldr_induction.go) := by
  intro α β xs motive f step i b h inv
  induction i generalizing b with
  | zero => exact inv
  | succ i ih =>
    rw [foldBefore (m := Id) f xs 0 i h (Nat.zero_lt_succ i)]
    exact ih (Nat.le_of_lt h) (step ⟨i, h⟩ b inv)

public theorem Array.foldr_induction.go._unary :
    type_of% (private_decl% @_root_.Array.foldr_induction.go._unary) := by
  intro α β xs motive f step state
  obtain ⟨i, b, bound, inv⟩ := state
  exact Array.foldr_induction.go motive step bound inv

public theorem Array.foldr_induction : type_of% @_root_.Array.foldr_induction := by
  intro α β xs motive init initial f step
  unfold _root_.Array.foldr _root_.Array.foldrM
  rw [dite_eq_left (Nat.le_refl _)]
  by_cases pos : 0 < xs.size
  · rw [ite_eq_left pos]
    exact (private_decl% _root_.Array.foldr_induction.go) motive step (Nat.le_refl _) initial
  · rw [ite_eq_right pos]
    exact Nat.eq_zero_of_not_pos pos ▸ initial

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

private theorem listRoundtrip {α : Type u} (xss : List (List α)) :
    (xss.map List.toArray).map _root_.Array.toList = xss := by
  induction xss with
  | nil => rfl
  | cons xs xss ih => exact congrArg (xs :: ·) ih

public theorem Array.flatten_toArray_map_toArray : type_of% @_root_.Array.flatten_toArray_map_toArray := by
  intro α xss
  exact _root_.Array.ext' (_root_.Array.toList_flatten.trans (congrArg List.flatten (listRoundtrip xss)))

public theorem Array.flatten_map_toArray_toArray : type_of% @_root_.Array.flatten_map_toArray_toArray := by
  intro α xss
  exact (congrArg _root_.Array.flatten (_root_.Array.ext' _root_.Array.toList_map)).trans Array.flatten_toArray_map_toArray

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

private theorem insertLoopSize (i : Nat) (xs : Array α) (j : Fin xs.size) :
    (Array.insertIdx.loop i xs j).size = xs.size := by
  apply Array.insertIdx.loop.induct i (fun ys k => (Array.insertIdx.loop i ys k).size = ys.size) _ _ xs j
  · intro ys k hk
    dsimp only
    intro ih
    rw [Array.insertIdx.loop.eq_def, ite_eq_left hk]
    exact ih.trans Array.size_swap
  · intro ys k hk
    rw [Array.insertIdx.loop.eq_def, ite_eq_right hk]
public theorem Array.size_insertIdx : type_of% @_root_.Array.size_insertIdx := by
  intro α a i xs h
  exact (insertLoopSize i (xs.push a) _).trans (_root_.Array.size_push a)
public theorem Vector.insertIdx._proof_1 : type_of% @_root_.Vector.insertIdx._proof_1 := by
  intro α n xs i x h
  exact (Array.size_insertIdx (xs.size_toArray.symm ▸ h)).trans (congrArg (· + 1) xs.size_toArray)


private theorem fixInvariant {σ : Sort u} {β : σ → Sort v} (measure : σ → Nat)
    (step : (x : σ) → ((y : σ) → measure y < measure x → β y) → β x)
    (P : (x : σ) → β x → Prop)
    (preserves : ∀ x cont, (∀ y hy, P y (cont y hy)) → P x (step x cont)) (x : σ) :
    P x (WellFounded.Nat.fix measure step x) := by
  have loop (fuel : Nat) (y : σ) (h : measure y < fuel) :
      P y (WellFounded.Nat.fix.go measure step fuel y h) := by
    induction fuel generalizing y with
    | zero => exact (Nat.not_succ_le_zero _ h).elim
    | succ k ih => exact preserves y _ fun z hz => ih z _
  exact loop _ x _

private theorem zipWithAllStep (f : Option α → Option β → γ) (xs : List α) (ys : List β)
    (i : Nat) (h : i < max xs.length ys.length) :
    List.zipWithAll f (xs.drop i) (ys.drop i) =
      f xs[i]? ys[i]? :: List.zipWithAll f (xs.drop (i+1)) (ys.drop (i+1)) := by
  by_cases hx : i < xs.length
  · rw [List.drop_eq_getElem_cons hx, List.getElem?_eq_getElem hx]
    by_cases hy : i < ys.length
    · rw [List.drop_eq_getElem_cons hy, List.getElem?_eq_getElem hy]
      rfl
    · have over := Nat.le_of_not_lt hy
      rw [List.drop_eq_nil_of_le over, List.drop_eq_nil_of_le (Nat.le_succ_of_le over),
        List.getElem?_eq_none over, List.zipWithAll_nil, List.zipWithAll_nil]
      rfl
  · have over := Nat.le_of_not_lt hx
    have hy : i < ys.length := by
      apply Nat.lt_of_not_ge
      intro le
      exact (Nat.not_le_of_lt h) (Nat.max_le.mpr ⟨over, le⟩)
    rw [List.drop_eq_nil_of_le over, List.drop_eq_nil_of_le (Nat.le_succ_of_le over),
      List.getElem?_eq_none over, List.drop_eq_getElem_cons hy, List.getElem?_eq_getElem hy]
    rfl

private theorem zipWithAllList (f : Option α → Option β → γ) (xs : Array α) (ys : Array β)
    (i : Nat) (acc : Array γ) :
    (Array.zipWithAll.go f xs ys i acc).toList =
      acc.toList ++ List.zipWithAll f (xs.toList.drop i) (ys.toList.drop i) := by
  delta Array.zipWithAll.go Array.zipWithAll.go._unary
  let P (p : (_ : Nat) ×' Array γ) (out : Array γ) :=
    out.toList = p.2.toList ++ List.zipWithAll f (xs.toList.drop p.1) (ys.toList.drop p.1)
  apply fixInvariant (P := P)
  rintro ⟨i, acc⟩ cont ih
  dsimp only [P]
  by_cases h : i < max xs.size ys.size
  · rw [dite_eq_left h]
    apply (ih ⟨i+1, acc.push (f xs[i]? ys[i]?)⟩ (Nat.sub_succ_lt_self _ _ h)).trans
    rw [zipWithAllStep f xs.toList ys.toList i h, Array.getElem?_toList, Array.getElem?_toList]
    exact (congrArg (· ++ _) Array.toList_push).trans (List.append_assoc ..)
  · have over := Nat.le_of_not_lt h
    rw [dite_eq_right h, List.drop_eq_nil_of_le (Nat.le_trans (Nat.le_max_left ..) over : xs.toList.length ≤ i),
      List.drop_eq_nil_of_le (Nat.le_trans (Nat.le_max_right ..) over : ys.toList.length ≤ i)]
    exact (List.append_nil _).symm

public theorem Array.toList_zipWithAll : type_of% @_root_.Array.toList_zipWithAll := by
  intro α β γ f xs ys
  exact zipWithAllList f xs ys 0 #[]

public theorem List.zipWithAll_go_toArray :
    type_of% (private_decl% @_root_.List.zipWithAll_go_toArray) := by
  intro α β γ xs ys f i acc
  apply _root_.Array.ext'
  rw [_root_.Array.toList_append]
  exact zipWithAllList f xs.toArray ys.toArray i acc

public theorem List.zipWithAll_go_toArray._unary :
    type_of% (private_decl% @_root_.List.zipWithAll_go_toArray._unary) := by
  intro α β γ xs ys f state
  exact List.zipWithAll_go_toArray xs ys f state.1 state.2

public theorem List.zipWithAll_toArray : type_of% @_root_.List.zipWithAll_toArray := by
  intro α β γ f xs ys
  exact _root_.Array.ext' (zipWithAllList f xs.toArray ys.toArray 0 #[])

private theorem zipWithList {α : Type u} {β : Type v} {γ : Type w}
    (as : Array α) (bs : Array β) (f : α → β → γ) (i : Nat) (acc : Array γ) :
    (Array.zipWithMAux (m := Id) as bs (fun a b => pure (f a b)) i acc).run.toList =
      acc.toList ++ List.zipWith f (as.toList.drop i) (bs.toList.drop i) := by
  delta Array.zipWithMAux Array.zipWithMAux._unary
  let P (p : (_ : Nat) ×' Array γ) (out : Array γ) :=
    out.toList = p.2.toList ++ List.zipWith f (as.toList.drop p.1) (bs.toList.drop p.1)
  apply fixInvariant (P := P)
  rintro ⟨i, acc⟩ cont ih
  dsimp only [P]
  by_cases ha : i < as.size
  · rw [dite_eq_left ha]
    by_cases hb : i < bs.size
    · rw [dite_eq_left hb]
      have h := ih ⟨i+1, acc.push (f as[i] bs[i])⟩ (by exact Nat.sub_succ_lt_self as.size i ha)
      apply h.trans
      rw [List.drop_eq_getElem_cons (show i < as.toList.length from ha),
        List.drop_eq_getElem_cons (show i < bs.toList.length from hb)]
      exact (congrArg (· ++ _) Array.toList_push).trans (List.append_assoc ..)
    · rw [dite_eq_right hb, List.drop_eq_nil_of_le (Nat.le_of_not_lt hb), List.zipWith_nil_right, List.append_nil]
      rfl
  · rw [dite_eq_right ha, List.drop_eq_nil_of_le (Nat.le_of_not_lt ha), List.zipWith_nil_left, List.append_nil]
    rfl

public theorem Array.toList_zipWith : type_of% @_root_.Array.toList_zipWith := by
  intro α β γ f as bs
  exact zipWithList as bs f 0 #[]

public theorem List.zipWith_toArray : type_of% @_root_.List.zipWith_toArray := by
  intro α β γ xs ys f
  exact _root_.Array.ext' (zipWithList xs.toArray ys.toArray f 0 #[])

public theorem List.zip_toArray : type_of% @_root_.List.zip_toArray := by
  intro α β xs ys
  exact _root_.Array.ext' (zipWithList xs.toArray ys.toArray Prod.mk 0 #[])

public theorem Array.size_zipWith : type_of% @_root_.Array.size_zipWith := by
  intro α β γ as bs f
  exact (congrArg List.length (Array.toList_zipWith (xs := as) (ys := bs) (f := f))).trans List.length_zipWith

public theorem Vector.zip._proof_1 : type_of% @_root_.Vector.zip._proof_1 := by
  intro α n β as bs
  rw [_root_.Array.size_zip, as.size_toArray, bs.size_toArray, Nat.min_self]

public theorem Vector.zipWith._proof_1 : type_of% @_root_.Vector.zipWith._proof_1 := by
  intro α β γ n f as bs
  rw [Array.size_zipWith, as.size_toArray, bs.size_toArray, Nat.min_self]

public theorem Array.toList_mapIdx : type_of% @_root_.Array.toList_mapIdx := by
  intro β γ f xs
  apply List.ext_getElem
  · exact _root_.Array.size_mapIdx.trans _root_.List.length_mapIdx.symm
  · intro i hi hj
    exact (_root_.Array.getElem_mapIdx hi).trans (List.getElem_mapIdx (h := hj)).symm

public theorem List.mapIdx_toArray : type_of% @_root_.List.mapIdx_toArray := by
  intro α β f l
  exact Array.ext' Array.toList_mapIdx

public theorem List.mapFinIdx_toArray : type_of% @_root_.List.mapFinIdx_toArray := by
  intro α β l f
  exact Array.ext' _root_.Array.toList_mapFinIdx


public theorem Array.toList_modify : type_of% @_root_.Array.toList_modify := by
  intro α xs f i
  apply _root_.List.ext_getElem
  · rw [_root_.List.length_modify]
    exact _root_.Array.size_modify
  · intro j left right
    rw [_root_.Array.getElem_toList, _root_.Array.getElem_modify, _root_.List.getElem_modify]
    rfl

private theorem flatMapPointwise (xs : _root_.List α) {f g : α → _root_.List β}
    (h : ∀ x, f x = g x) : xs.flatMap f = xs.flatMap g := by
  induction xs with
  | nil => rfl
  | cons x xs ih => rw [_root_.List.flatMap_cons, _root_.List.flatMap_cons, h x, ih]

public theorem Array.flatMap_assoc : type_of% @_root_.Array.flatMap_assoc := by
  intro α β γ xs f g
  apply _root_.Array.ext'
  rw [_root_.Array.toList_flatMap, _root_.Array.toList_flatMap, _root_.Array.toList_flatMap,
    _root_.List.flatMap_assoc]
  exact flatMapPointwise _ (fun _ => _root_.Array.toList_flatMap.symm)

public theorem Array.map_flatMap : type_of% @_root_.Array.map_flatMap := by
  intro α β γ f g xs
  apply _root_.Array.ext'
  rw [_root_.Array.toList_map, _root_.Array.toList_flatMap, _root_.Array.toList_flatMap,
    _root_.List.map_flatMap]
  exact flatMapPointwise _ (fun _ => _root_.Array.toList_map.symm)

public theorem Array.map_eq_flatMap : type_of% @_root_.Array.map_eq_flatMap := by
  intro α β f xs
  apply _root_.Array.ext'
  rw [_root_.Array.toList_map, _root_.Array.toList_flatMap]
  exact _root_.List.map_eq_flatMap

public theorem Array.filterMap_flatMap : type_of% @_root_.Array.filterMap_flatMap := by
  intro α β γ xs g f
  apply _root_.Array.ext'
  rw [_root_.Array.toList_filterMap, _root_.Array.toList_flatMap, _root_.Array.toList_flatMap,
    _root_.List.filterMap_flatMap]
  exact flatMapPointwise _ (fun _ => _root_.Array.toList_filterMap.symm)

public theorem Array.filter_flatMap : type_of% @_root_.Array.filter_flatMap := by
  intro α β xs g f
  apply _root_.Array.ext'
  rw [_root_.Array.toList_filter, _root_.Array.toList_flatMap, _root_.Array.toList_flatMap,
    _root_.List.filter_flatMap]
  exact flatMapPointwise _ (fun _ => _root_.Array.toList_filter.symm)

public theorem Array.reverse_flatMap : type_of% @_root_.Array.reverse_flatMap := by
  intro α β xs f
  apply _root_.Array.ext'
  rw [_root_.Array.toList_reverse, _root_.Array.toList_flatMap, _root_.Array.toList_flatMap,
    _root_.List.reverse_flatMap, _root_.Array.toList_reverse]
  exact flatMapPointwise _ (fun _ => _root_.Array.toList_reverse.symm)

public theorem Array.flatMap_reverse : type_of% @_root_.Array.flatMap_reverse := by
  intro α β xs f
  apply _root_.Array.ext'
  rw [_root_.Array.toList_flatMap, _root_.Array.toList_reverse, _root_.Array.toList_reverse,
    _root_.Array.toList_flatMap, _root_.List.flatMap_reverse]
  exact congrArg _root_.List.reverse (flatMapPointwise _ (fun _ => _root_.Array.toList_reverse.symm))

public theorem Array.reverse_flatten : type_of% @_root_.Array.reverse_flatten := by
  intro α xss
  rw [_root_.Array.flatten_eq_flatMap, _root_.Array.reverse_flatMap, _root_.Array.flatten_eq_flatMap,
    ← _root_.Array.map_reverse, _root_.Array.flatMap_map]
  rfl

public theorem Array.flatten_reverse : type_of% @_root_.Array.flatten_reverse := by
  intro α xss
  rw [_root_.Array.flatten_eq_flatMap, _root_.Array.flatMap_reverse, _root_.Array.flatten_eq_flatMap,
    _root_.Array.flatMap_map]
  rfl

public theorem Array.set_append_left : type_of% @_root_.Array.set_append_left := by
  intro α xs ys i x bound
  apply _root_.Array.ext'
  rw [_root_.Array.toList_set, _root_.Array.toList_append, _root_.Array.toList_append,
    _root_.Array.toList_set]
  exact _root_.List.set_append_left i x bound

public theorem Array.set_append_right : type_of% @_root_.Array.set_append_right := by
  intro α xs ys i x valid bound
  apply _root_.Array.ext'
  rw [_root_.Array.toList_set, _root_.Array.toList_append, _root_.Array.toList_append,
    _root_.Array.toList_set]
  exact _root_.List.set_append_right i x bound

public theorem Array.set_append : type_of% @_root_.Array.set_append := by
  intro α xs ys i x valid
  by_cases left : i < xs.size
  · rw [dite_eq_left left]
    exact _root_.Array.set_append_left left
  · rw [dite_eq_right left]
    exact _root_.Array.set_append_right valid (Nat.le_of_not_lt left)

public theorem Array.set_push : type_of% @_root_.Array.set_push := by
  intro α i xs x y valid
  apply _root_.Array.ext'
  by_cases left : i < xs.size
  · rw [dite_eq_left left, _root_.Array.toList_set, _root_.Array.toList_push,
      _root_.Array.toList_push, _root_.Array.toList_set]
    exact _root_.List.set_append_left i y left
  · rw [dite_eq_right left, _root_.Array.toList_set, _root_.Array.toList_push,
      _root_.Array.toList_push, _root_.List.set_append_right i y (Nat.le_of_not_lt left)]
    have atEnd := Nat.le_antisymm (Nat.le_of_lt_succ (Nat.lt_of_lt_of_eq valid (_root_.Array.size_push _)))
      (Nat.le_of_not_lt left)
    rw [show xs.toList.length = xs.size from rfl, atEnd, Nat.sub_self]
    rfl

public theorem Array.none_eq_getElem?_iff : type_of% @_root_.Array.none_eq_getElem?_iff := by
  intro α xs i
  exact ⟨fun h => _root_.Array.getElem?_eq_none_iff.mp h.symm,
    fun h => (_root_.Array.getElem?_eq_none_iff.mpr h).symm⟩

public theorem Array.map_inj_right : type_of% @_root_.Array.map_inj_right := by
  intro α β xs ys f injective
  constructor
  · intro h
    apply _root_.Array.ext'
    apply (_root_.List.map_inj_right injective).mp
    exact _root_.Array.toList_map.symm.trans ((congrArg _root_.Array.toList h).trans _root_.Array.toList_map)
  · intro h
    cases h
    rfl

public theorem Array.flatten_ne_empty_iff : type_of% @_root_.Array.flatten_ne_empty_iff := by
  intro α xss
  constructor
  · intro ne
    obtain ⟨x, inside⟩ := _root_.Array.exists_mem_of_ne_empty _ ne
    obtain ⟨row, mem, inner⟩ := _root_.Array.mem_flatten.mp inside
    exact ⟨row, mem, _root_.Array.ne_empty_of_mem inner⟩
  · intro ⟨row, mem, ne⟩
    obtain ⟨x, inner⟩ := _root_.Array.exists_mem_of_ne_empty _ ne
    exact _root_.Array.ne_empty_of_mem (_root_.Array.mem_flatten.mpr ⟨row, mem, inner⟩)

public theorem Array.map_filterMap_of_inv : type_of% @_root_.Array.map_filterMap_of_inv := by
  intro α β f g inv xs
  apply _root_.Array.ext'
  rw [_root_.Array.toList_map, _root_.Array.toList_filterMap]
  exact _root_.List.map_filterMap_of_inv inv

private theorem getZipWith (f : α → β → γ) (xs : _root_.List α) (ys : _root_.List β)
    (i : Nat) (valid : i < (xs.zipWith f ys).length)
    (left : i < xs.length) (right : i < ys.length) :
    (xs.zipWith f ys)[i] = f xs[i] ys[i] := by
  induction xs generalizing i ys with
  | nil => exact (Nat.not_lt_zero _ left).elim
  | cons x xs ih =>
    cases ys with
    | nil => exact (Nat.not_lt_zero _ right).elim
    | cons y ys =>
      cases i with
      | zero => rfl
      | succ i =>
        exact ih ys i (Nat.lt_of_succ_lt_succ valid)
          (Nat.lt_of_succ_lt_succ left) (Nat.lt_of_succ_lt_succ right)

public theorem Array.getElem_zipWith : type_of% @_root_.Array.getElem_zipWith := by
  intro α β γ xs ys f i hi
  have bound : i < min xs.size ys.size := _root_.Array.size_zipWith (f := f) ▸ hi
  have lists := _root_.Array.toList_zipWith (f := f) (xs := xs) (ys := ys)
  refine (_root_.Array.getElem_toList _).symm.trans ((_root_.List.getElem_of_eq lists _).trans ?_)
  exact getZipWith f xs.toList ys.toList i _ (Nat.lt_of_lt_of_le bound (Nat.min_le_left ..))
    (Nat.lt_of_lt_of_le bound (Nat.min_le_right ..))

public theorem Array.getElem_replace : type_of% @_root_.Array.getElem_replace := by
  intro α _ _ a b xs i hi
  letI : DecidableEq α := _root_.instDecidableEqOfLawfulBEq
  apply Option.some.inj
  rw [← _root_.Array.getElem?_eq_getElem (show i < (xs.replace a b).size from
    (_root_.Array.size_replace (xs := xs) (a := a) (b := b)).symm ▸ hi),
    _root_.Array.getElem?_replace, _root_.Array.getElem?_eq_getElem hi]
  by_cases hit : xs[i] = a
  · rw [ite_eq_left (beq_iff_eq.mpr (congrArg some hit)), ite_eq_left (beq_iff_eq.mpr hit)]
    by_cases old : a ∈ xs.take i
    · rw [ite_eq_left old, ite_eq_left old]
    · rw [ite_eq_right old, ite_eq_right old]
  · rw [ite_eq_right (fun h => hit (Option.some.inj (eq_of_beq h))),
      ite_eq_right (fun h => hit (eq_of_beq h))]

public theorem Array.getElem_replace_of_ne : type_of% @_root_.Array.getElem_replace_of_ne := by
  intro α _ _ a b xs i hi ne
  exact (_root_.Array.getElem_replace hi).trans (ite_eq_right (fun hit => ne (eq_of_beq hit)))

end OmegaChecks.InitPort.Alternatives
