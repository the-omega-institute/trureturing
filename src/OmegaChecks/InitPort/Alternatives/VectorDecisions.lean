module
import all Init.Data.Vector.Lemmas
import all Init.Data.Vector.Basic
import all Init.Data.Array.Lemmas
import all Init.Data.Array.Basic
import all Init.WF

/-! Decisions and lookups for vectors retain their size witnesses. -/
namespace OmegaChecks.InitPort.Alternatives

public def Vector.instDecidableExistsVectorZero {α : Type u} (p : _root_.Vector α 0 → Prop)
    [d : Decidable (p #v[])] : Decidable (∃ xs, p xs) :=
  decidable_of_iff (¬ ∀ xs, ¬ p xs) <| by
    constructor
    · intro h
      cases d with
      | isTrue yes => exact ⟨#v[], yes⟩
      | isFalse no => exact (h fun xs hp => no (_root_.Vector.eq_empty (xs := xs) ▸ hp)).elim
    · rintro ⟨xs, yes⟩ no
      exact no xs yes

public theorem Vector.mem_dite_empty_left : type_of% @_root_.Vector.mem_dite_empty_left := by
  intro α p x _ xs
  by_cases h : p
  · rw [dite_eq_left h]
    exact ⟨fun m => (_root_.Vector.not_mem_empty x m).elim, fun ⟨hn, _⟩ => (hn h).elim⟩
  · rw [dite_eq_right h]
    exact ⟨fun m => ⟨h, m⟩, fun ⟨_, m⟩ => m⟩

public theorem Vector.mem_ite_empty_left : type_of% @_root_.Vector.mem_ite_empty_left := by
  intro α p x _ xs
  by_cases h : p
  · rw [ite_eq_left h]
    exact ⟨fun m => (_root_.Vector.not_mem_empty x m).elim, fun m => (m.1 h).elim⟩
  · rw [ite_eq_right h]
    exact ⟨fun m => ⟨h, m⟩, And.right⟩

public theorem Vector.replicate_beq_replicate : type_of% @_root_.Vector.replicate_beq_replicate := by
  intros
  rw [← _root_.Vector.toArray_beq_toArray, _root_.Vector.toArray_replicate, _root_.Vector.toArray_replicate]
  exact _root_.Array.replicate_beq_replicate

public theorem Vector.getElem?_replace : type_of% @_root_.Vector.getElem?_replace := by
  intro α _ _ n a b xs i
  obtain ⟨data, rfl⟩ := xs
  rw [_root_.Vector.replace_mk, _root_.Vector.getElem?_mk, _root_.Vector.getElem?_mk,
    _root_.Array.getElem?_replace, _root_.Vector.take_mk]
  by_cases h : a ∈ data.take i
  · rw [ite_eq_left h, ite_eq_left (_root_.Vector.mem_mk.mpr h)]
  · rw [ite_eq_right h, ite_eq_right (fun v => h (_root_.Vector.mem_mk.mp v))]

public theorem Vector.getElem?_replace_of_ne : type_of% @_root_.Vector.getElem?_replace_of_ne := by
  intro α _ _ n a b xs i miss
  rw [_root_.Vector.getElem?_replace]
  exact ite_eq_right (fun h => miss (eq_of_beq h))

public theorem Vector.getElem_replace : type_of% @_root_.Vector.getElem_replace := by
  intro α _ _ n a b xs i hi
  obtain ⟨data, rfl⟩ := xs
  rw [_root_.Vector.getElem_mk, _root_.Vector.take_mk]
  change (data.replace a b)[i]'((_root_.Array.size_replace (xs := data) (a := a) (b := b)).symm ▸ hi) = _
  rw [_root_.Array.getElem_replace hi]
  by_cases h : a ∈ data.take i
  · rw [ite_eq_left h, ite_eq_left (_root_.Vector.mem_mk.mpr h)]
    rfl
  · rw [ite_eq_right h, ite_eq_right (fun v => h (_root_.Vector.mem_mk.mp v))]
    rfl

public theorem Vector.replace_push : type_of% @_root_.Vector.replace_push := by
  intro α _ _ n xs a b c
  obtain ⟨data, rfl⟩ := xs
  apply _root_.Vector.toArray_inj.mp
  by_cases h : b ∈ _root_.Vector.mk data rfl
  · rw [ite_eq_left h]
    exact _root_.Array.replace_push.trans (ite_eq_left (_root_.Vector.mem_mk.mp h))
  · rw [ite_eq_right h]
    exact _root_.Array.replace_push.trans (ite_eq_right (fun m => h (_root_.Vector.mem_mk.mpr m)))

public theorem Vector.reflBEq_iff : type_of% @_root_.Vector.reflBEq_iff := by
  intro α n _ nz
  cases n with
  | zero => exact (nz.out rfl).elim
  | succ n =>
    constructor
    · intro h
      constructor
      intro a
      exact (_root_.Vector.replicate_beq_replicate (n := n+1) (a := a) (b := a)).symm.trans
        (@ReflBEq.rfl _ _ h _)
    · intro h
      constructor
      intro xs
      exact (_root_.Vector.toArray_beq_toArray (xs := xs) (ys := xs)).symm.trans
        (@ReflBEq.rfl _ _ inferInstance _)

public theorem Vector.lawfulBEq_iff : type_of% @_root_.Vector.lawfulBEq_iff := by
  intro α n _ nz
  cases n with
  | zero => exact (nz.out rfl).elim
  | succ n =>
    constructor
    · intro h
      haveI : ReflBEq α := (_root_.Vector.reflBEq_iff (n := n+1)).mp h.toReflBEq
      constructor
      intro a b hab
      have eq := @LawfulBEq.eq_of_beq _ _ h _ _
        ((_root_.Vector.replicate_beq_replicate (n := n+1) (a := a) (b := b)).trans hab)
      exact (_root_.Vector.replicate_inj.mp eq).resolve_left (Nat.succ_ne_zero n)
    · intro h
      haveI : ReflBEq (_root_.Vector α (n+1)) := _root_.Vector.reflBEq_iff.mpr h.toReflBEq
      constructor
      intro xs ys eq
      exact _root_.Vector.toArray_inj.mp (eq_of_beq (_root_.Vector.toArray_beq_toArray.trans eq))

private def mapMeasure (n : Nat) (s : (_ : Nat) ×' Array β) := n - s.1

private def mapStep (n : Nat) (read : (i : Nat) → i < n → β) (s : (_ : Nat) ×' Array β)
    (recur : ∀ (t : (_ : Nat) ×' Array β), mapMeasure n t < mapMeasure n s → Array β) : Array β :=
  PSigma.casesOn (motive := fun s => (∀ (t : (_ : Nat) ×' Array β), mapMeasure n t < mapMeasure n s → Array β) → Array β)
    s (fun i acc recur => if h : i < n then
      recur ⟨i+1, acc.push (read i h)⟩ (Nat.sub_succ_lt_self _ _ h) else acc) recur

private def runMap (n : Nat) (read : (i : Nat) → i < n → β) : Array β :=
  WellFounded.Nat.fix (mapMeasure n) (mapStep n read) ⟨0, #[]⟩

private theorem yesUnder {p : Prop} [d : Decidable p] (h : p) (obs : α → β → γ)
    (yes : p → α → β) (no : ¬p → α → β) :
    (fun x => obs x (dite p (fun hp => yes hp x) (fun hn => no hn x))) = fun x => obs x (yes h x) := by
  cases d with
  | isTrue => rfl
  | isFalse hn => exact (hn h).elim

private theorem noUnder {p : Prop} [d : Decidable p] (h : ¬p) (obs : α → β → γ)
    (yes : p → α → β) (no : ¬p → α → β) :
    (fun x => obs x (dite p (fun hp => yes hp x) (fun hn => no hn x))) = fun x => obs x (no h x) := by
  cases d with
  | isTrue hp => exact (h hp).elim
  | isFalse => rfl

/-- After the first push, every recursive map step preserves the head for the whole input function. -/
private theorem nonemptyHead (n : Nat) (read : α → (i : Nat) → i < n+1 → β) (dflt : α → β) :
    (fun x => (runMap (n+1) (read x)).toList.headD (dflt x)) = fun x => read x 0 (Nat.zero_lt_succ n) := by
  let head (x : α) := read x 0 (Nat.zero_lt_succ n)
  let obs (x : α) (xs : Array β) := xs.toList.headD (dflt x)
  have keep (fuel i : Nat) (h : n+1-i < fuel) (tail : α → List β) :
      (fun x => obs x (WellFounded.Nat.fix.go (mapMeasure (n+1)) (mapStep (n+1) (read x))
        fuel ⟨i, ⟨head x :: tail x⟩⟩ h)) = head := by
    induction fuel generalizing i tail with
    | zero => exact (Nat.not_lt_zero _ h).elim
    | succ fuel ih =>
      dsimp only [WellFounded.Nat.fix.go, mapStep]
      by_cases inside : i < n+1
      · apply (yesUnder inside obs _ _).trans
        exact ih (i+1) (Nat.lt_of_lt_of_le (Nat.sub_succ_lt_self _ _ inside) (Nat.le_of_lt_succ h)) _
      · exact noUnder inside obs _ _
  let fuel := WellFounded.Nat.eager (n+1+1)
  have h : n+1 < fuel := by
    dsimp only [fuel]
    rw [WellFounded.Nat.eager_eq]
    exact Nat.lt_succ_self _
  change (fun x => obs x (WellFounded.Nat.fix.go (mapMeasure (n+1)) (mapStep (n+1) (read x)) fuel ⟨0, #[]⟩ h)) = head
  generalize hf : fuel = fuel' at h ⊢
  cases fuel' with
  | zero => exact (Nat.not_lt_zero _ h).elim
  | succ fuel =>
    dsimp only [WellFounded.Nat.fix.go, mapStep]
    apply (yesUnder (Nat.zero_lt_succ n) obs _ _).trans
    exact keep fuel 1 (Nat.lt_of_lt_of_le (Nat.sub_succ_lt_self _ _ (Nat.zero_lt_succ n)) (Nat.le_of_lt_succ h)) (fun _ => [])

private theorem familyHead (n : Nat) (size : α → Nat) (same : size = fun _ => n+1)
    (read : (x : α) → (i : Nat) → i < size x → β) (dflt answer : α → β)
    (first : ∀ h : ∀ x, 0 < size x, (fun x => read x 0 (h x)) = answer) :
    (fun x => (runMap (size x) (read x)).toList.headD (dflt x)) = answer := by
  cases same
  exact (nonemptyHead n read dflt).trans (first _)

private theorem sizeRepeat {α : Type u} (n : Nat) :
    (fun x : α => (List.replicate n x).length) = fun _ => n := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (fun (k : α → Nat) x => (k x).succ) ih

public theorem Vector.map_inj : type_of% @_root_.Vector.map_inj := by
  intro n α β f g nz
  constructor
  · intro eq
    cases n with
    | zero => exact (nz.out rfl).elim
    | succ n =>
      let pack (x : α) : _root_.Vector α (n+1) :=
        ⟨⟨x :: List.replicate n x⟩, congrArg Nat.succ List.length_replicate⟩
      let obs (k : _root_.Vector α (n+1) → _root_.Vector β (n+1)) x :=
        (k (pack x)).toArray.toList.headD (f x)
      have reads (q : α → β) : obs (_root_.Vector.map q) = q := by
        with_unfolding_all exact (familyHead n (fun x => (pack x).toArray.size)
          (congrArg (fun (k : α → Nat) x => (k x).succ) (sizeRepeat n))
          (fun x i h => q ((pack x).toArray[i])) f q (fun _ => rfl))
      exact (reads f).symm.trans ((congrArg obs eq).trans (reads g))
  · rintro rfl
    rfl

public theorem Vector.map_id'' : type_of% @_root_.Vector.map_id'' := by
  intro α n f h xs
  exact (_root_.Vector.map_congr_left (g := id) (fun x _ => h x)).trans (_root_.Vector.map_id xs)

public theorem Vector.append_eq_append_iff : type_of% @_root_.Vector.append_eq_append_iff := by
  intro α n m k l ws xs ys zs sizes
  obtain ⟨ws, rfl⟩ := ws
  obtain ⟨xs, rfl⟩ := xs
  obtain ⟨ys, rfl⟩ := ys
  obtain ⟨zs, rfl⟩ := zs
  constructor
  · intro eq
    have arrays := congrArg _root_.Vector.toArray eq
    change ws ++ xs = ys ++ zs at arrays
    rcases _root_.Array.append_eq_append_iff.mp arrays with ⟨as, rfl, rfl⟩ | ⟨cs, rfl, rfl⟩
    · have le : ws.size ≤ (ws ++ as).size := _root_.Array.size_append ▸ Nat.le_add_right ..
      rw [dite_eq_left le]
      exact ⟨⟨as, by rw [_root_.Array.size_append]; omega⟩, rfl, rfl⟩
    · by_cases le : (ys ++ cs).size ≤ ys.size
      · have empty := _root_.Array.eq_empty_of_size_eq_zero (xs := cs) (by
          rw [_root_.Array.size_append] at le
          omega)
        subst cs
        rw [dite_eq_left le]
        refine ⟨⟨#[], by rw [_root_.Array.size_append]; change 0 = _; omega⟩, ?_, ?_⟩
        · apply _root_.Vector.toArray_inj.mp
          change ys = (ys ++ #[]) ++ #[]
          rw [_root_.Array.append_empty, _root_.Array.append_empty]
        · apply _root_.Vector.toArray_inj.mp
          change xs = #[] ++ (#[] ++ xs)
          rw [_root_.Array.empty_append, _root_.Array.empty_append]
      · rw [dite_eq_right le]
        exact ⟨⟨cs, by rw [_root_.Array.size_append]; omega⟩, rfl, rfl⟩
  · intro h
    apply _root_.Vector.toArray_inj.mp
    change ws ++ xs = ys ++ zs
    apply _root_.Array.append_eq_append_iff.mpr
    split at h
    · obtain ⟨as, hys, hxs⟩ := h
      exact .inl ⟨as.toArray, congrArg _root_.Vector.toArray hys, congrArg _root_.Vector.toArray hxs⟩
    · obtain ⟨cs, hws, hzs⟩ := h
      exact .inr ⟨cs.toArray, congrArg _root_.Vector.toArray hws, congrArg _root_.Vector.toArray hzs⟩

end OmegaChecks.InitPort.Alternatives
