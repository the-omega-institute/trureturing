module

public import Init.Data.Range.Lemmas
import all Init.Data.Range.Lemmas
import all Init.Data.Range.Basic
import all Init.Data.List.Control
import all OmegaChecks.InitPort.Alternatives.MonadicLists

/-! Legacy natural-number ranges visit the same entries, in the same order, as `List.range'`. -/

namespace OmegaChecks.InitPort.Alternatives

open _root_.Std.Legacy

public theorem Std.Legacy.Range.size_eq {i : Nat} (r : Range) (hi : i < r.stop) :
    (r.stop - i + r.step - 1) / r.step = (r.stop - (i + r.step) + r.step - 1) / r.step + 1 := by
  cases gap : r.stop - i with
  | zero => exact (Nat.not_le_of_gt hi (Nat.le_of_sub_eq_zero gap)).elim
  | succ t =>
    have next : r.stop - (i + r.step) = t + 1 - r.step := by rw [← Nat.sub_sub, gap]
    rw [next, Nat.succ_add, Nat.succ_sub_one, Nat.add_div_right _ r.step_pos]
    apply congrArg Nat.succ
    by_cases h : r.step ≤ t + 1
    · rw [Nat.sub_add_cancel h, Nat.succ_sub_one]
    · have ht := Nat.lt_of_not_ge h
      rw [Nat.sub_eq_zero_of_le (Nat.le_of_lt ht), Nat.zero_add,
        Nat.div_eq_of_lt (Nat.sub_lt r.step_pos Nat.zero_lt_one),
        Nat.div_eq_of_lt (Nat.lt_trans (Nat.lt_succ_self t) ht)]

private theorem rangeStopped (r : Range) (i : Nat) (h : ¬i < r.stop) :
    (r.stop - i + r.step - 1) / r.step = 0 := by
  rw [Nat.div_eq_zero_iff_lt r.step_pos, Nat.sub_eq_zero_of_le (Nat.le_of_not_gt h), Nat.zero_add]
  exact Nat.sub_lt r.step_pos Nat.zero_lt_one

private theorem forMRange [Monad m] (r : Range) (f : Nat → m PUnit) (i : Nat) :
    Range.forM.loop r f i = forM (List.range' i ((r.stop - i + r.step - 1) / r.step) r.step) f := by
  delta Range.forM.loop
  apply fixInvariant _ (fun i out => out = forM (List.range' i ((r.stop - i + r.step - 1) / r.step) r.step) f)
  intro i recur ih
  dsimp only
  by_cases h : i < r.stop
  · rw [dite_eq_left h, Range.size_eq r h, List.range'_succ]
    change (f i >>= fun _ => _) = f i >>= fun _ => _
    exact congrArg (fun tail => f i >>= fun _ => tail) (ih (i + r.step) _)
  · rw [dite_eq_right h, rangeStopped r i h]
    rfl

public theorem Std.Legacy.Range.forM_eq_forM_range' :
    type_of% @_root_.Std.Legacy.Range.forM_eq_forM_range' := by
  intros
  apply forMRange

/-- Induction on the fuel with the complete continuation function as the induction invariant. -/
private theorem fuelInvariant {A : Sort u} {B : Sort v} (measure : A → Nat)
    (action : (x : A) → ((y : A) → measure y < measure x → B) → B)
    (P : (n : Nat) → ((x : A) → measure x < n → B) → Prop)
    (zero : P 0 (fun _ h => (Nat.not_lt_zero _ h).elim))
    (succ : ∀ n cont, P n cont → P (n + 1)
      (fun x hx => action x (fun y hy => cont y (Nat.lt_of_lt_of_le hy (Nat.le_of_lt_succ hx)))))
    (n : Nat) : P n (WellFounded.Nat.fix.go measure action n) := by
  induction n with
  | zero => exact zero
  | succ k ih => exact succ k _ ih

private abbrev RangeState (r : Range) (β : Type u) :=
  (_ : β) ×' (i : Nat) ×' (_ : (i - r.start) % r.step = 0) ×' r.start ≤ i

private def remaining (r : Range) (p : RangeState r β) : Nat :=
  PSigma.casesOn p fun _ q => PSigma.casesOn q fun i s => PSigma.casesOn s fun _ _ => r.stop - i

private def rangeAction [Monad m] (r : Range) (f : (i : Nat) → i ∈ r → β → m (ForInStep β))
    (p : RangeState r β) : ((q : RangeState r β) → remaining r q < remaining r p → m β) → m β := by
  obtain ⟨b, i, hs, hl⟩ := p
  intro rec
  exact if h : i < r.stop then
    have aligned : (i + r.step - r.start) % r.step = 0 := by
      rw [Nat.add_comm i, Nat.add_sub_assoc hl, Nat.add_mod_left, hs]
    forInNext (f i ⟨hl, h, hs⟩)
      (fun b => rec ⟨b, i + r.step, aligned, Nat.le_trans hl (Nat.le_add_right ..)⟩
        (Nat.sub_lt_sub_left h (Nat.lt_add_of_pos_right r.step_pos))) b
  else pure b

private abbrev rangeFuel [Monad m] (r : Range) (f : (i : Nat) → i ∈ r → β → m (ForInStep β))
    (n i : Nat) (hs : (i - r.start) % r.step = 0) (hl : r.start ≤ i) (hn : r.stop - i < n) (b : β) :=
  WellFounded.Nat.fix.go (remaining r) (rangeAction r f) n ⟨b, i, hs, hl⟩ hn

/-- The entire function of the accumulator agrees for any two sufficient bounds. -/
private theorem rangeBounds [Monad m] (r : Range) (f : (i : Nat) → i ∈ r → β → m (ForInStep β))
    (n k i : Nat) (hs : (i - r.start) % r.step = 0) (hl : r.start ≤ i)
    (hn : r.stop - i < n) (hk : r.stop - i < k) :
    rangeFuel r f n i hs hl hn = rangeFuel r f k i hs hl hk := by
  induction n generalizing k i with
  | zero => exact (Nat.not_lt_zero _ hn).elim
  | succ n ih =>
    cases k with
    | zero => exact (Nat.not_lt_zero _ hk).elim
    | succ k =>
      delta rangeFuel WellFounded.Nat.fix.go
      dsimp only [rangeAction]
      by_cases h : i < r.stop
      · refine (dependentBranch h _ _).trans (Eq.trans ?_ (dependentBranch h _ _).symm)
        have aligned : (i + r.step - r.start) % r.step = 0 := by
          rw [Nat.add_comm i, Nat.add_sub_assoc hl, Nat.add_mod_left, hs]
        have smaller := Nat.sub_lt_sub_left h (Nat.lt_add_of_pos_right r.step_pos)
        exact congrArg (forInNext (f i ⟨hl, h, hs⟩))
          (ih k (i + r.step) aligned (Nat.le_trans hl (Nat.le_add_right ..))
            (Nat.lt_of_lt_of_le smaller (Nat.le_of_lt_succ hn))
            (Nat.lt_of_lt_of_le smaller (Nat.le_of_lt_succ hk)))
      · apply Eq.trans (b := fun b : β => pure (f := m) b)
        · apply dependentElse h
        · symm
          apply dependentElse h

private theorem rangeAtFuel [Monad m] (r : Range) (f : (i : Nat) → i ∈ r → β → m (ForInStep β))
    (i n : Nat) (hs : (i - r.start) % r.step = 0) (hl : r.start ≤ i) (hn : r.stop - i < n) :
    (fun b => Range.forIn'.loop r f b i hs hl) = rangeFuel r f n i hs hl hn := by
  delta Range.forIn'.loop Range.forIn'.loop._unary WellFounded.Nat.fix
  exact rangeBounds r f (WellFounded.Nat.eager (r.stop - i + 1)) n i hs hl
    (WellFounded.Nat.eager_eq _ ▸ Nat.lt_add_one _) hn

public theorem Std.Legacy.Range.forIn'.loop._unary.eq_def :
    type_of% (private_decl% @_root_.Std.Legacy.Range.forIn'.loop._unary.eq_def) := by
  intro m β inst r f p
  obtain ⟨b, i, hs, hl⟩ := p
  dsimp only
  have start := congrFun (rangeAtFuel r f i (Nat.succ (r.stop - i)) hs hl (Nat.lt_succ_self _)) b
  with_unfolding_all refine start.trans ?_
  delta rangeFuel WellFounded.Nat.fix.go
  dsimp only [rangeAction]
  by_cases h : i < r.stop
  · rw [dite_eq_left h, dite_eq_left h]
    have aligned : (i + r.step - r.start) % r.step = 0 := by
      rw [Nat.add_comm i, Nat.add_sub_assoc hl, Nat.add_mod_left, hs]
    have smaller := Nat.sub_lt_sub_left h (Nat.lt_add_of_pos_right r.step_pos)
    with_unfolding_all exact congrFun (congrArg (forInNext (f i ⟨hl,h,hs⟩))
      (rangeAtFuel r f (i + r.step) (r.stop - i) aligned (Nat.le_trans hl (Nat.le_add_right ..)) smaller).symm) b
  · rw [dite_eq_right h, dite_eq_right h]

private theorem forInRange [Monad m] (r : Range) (f : (i : Nat) → i ∈ r → β → m (ForInStep β))
    (xs : List Nat) (inside : ∀ a, a ∈ xs → a ∈ r) (i : Nat)
    (hs : (i - r.start) % r.step = 0) (hl : r.start ≤ i) (rest : List Nat)
    (reach : ∃ p, p ++ rest = xs) (entries : List.range' i ((r.stop - i + r.step - 1) / r.step) r.step = rest) :
    (fun b => Range.forIn'.loop r f b i hs hl) =
      fun b => List.forIn'.loop xs (fun a ha => f a (inside a ha)) rest b reach := by
  let body (a : Nat) (ha : a ∈ xs) := f a (inside a ha)
  let State := (_ : β) ×' (i : Nat) ×' (_ : (i - r.start) % r.step = 0) ×' r.start ≤ i
  let measure : State → Nat := fun p =>
    PSigma.casesOn p fun _ q => PSigma.casesOn q fun i s => PSigma.casesOn s fun _ _ => r.stop - i
  let P (n : Nat) (cont : (p : State) → measure p < n → m β) :=
    ∀ i hs hl (bound : r.stop - i < n) (rest : List Nat) (reach : ∃ p, p ++ rest = xs),
      List.range' i ((r.stop - i + r.step - 1) / r.step) r.step = rest →
        (fun b => cont ⟨b, i, hs, hl⟩ bound) = fun b => List.forIn'.loop xs body rest b reach
  delta Range.forIn'.loop Range.forIn'.loop._unary WellFounded.Nat.fix
  refine fuelInvariant measure _ P ?_ ?_ (WellFounded.Nat.eager (r.stop - i + 1))
    i hs hl (WellFounded.Nat.eager_eq _ ▸ Nat.lt_add_one _) rest reach entries
  · intro i hs hl bound
    exact (Nat.not_lt_zero _ bound).elim
  · intro n cont ih i hs hl bound rest reach entries
    dsimp only
    by_cases h : i < r.stop
    · rw [Range.size_eq r h, List.range'_succ] at entries
      subst rest
      obtain ⟨pref, hp⟩ := reach
      have tailReach : ∃ p, p ++ List.range' (i + r.step)
          ((r.stop - (i + r.step) + r.step - 1) / r.step) r.step = xs :=
        ⟨pref ++ [i], (List.append_assoc ..).trans hp⟩
      have member : i ∈ xs := hp ▸ List.mem_append_right _ List.mem_cons_self
      refine (dependentBranch h _ _).trans ?_
      have aligned : (i + r.step - r.start) % r.step = 0 := by
        rw [Nat.add_comm i, Nat.add_sub_assoc hl, Nat.add_mod_left, hs]
      have above := Nat.le_trans hl (Nat.le_add_right i r.step)
      have smaller : r.stop - (i + r.step) < r.stop - i := by
        exact Nat.sub_lt_sub_left h (Nat.lt_add_of_pos_right r.step_pos)
      have bound' := Nat.lt_of_lt_of_le smaller (Nat.le_of_lt_succ bound)
      exact congrArg (forInNext (body i member))
        (ih (i + r.step) aligned above bound' _ tailReach rfl)
    · rw [rangeStopped r i h] at entries
      change [] = rest at entries
      subst rest
      apply dependentElse h

public theorem Std.Legacy.Range.forIn'_eq_forIn'_range' :
    type_of% @_root_.Std.Legacy.Range.forIn'_eq_forIn'_range' := by
  intro m β _ r init f
  exact congrFun (forInRange r f _ (fun _ h => Range.mem_of_mem_range' h) r.start _ _ _ ⟨[], rfl⟩ rfl) init

public theorem Std.Legacy.Range.forIn_eq_forIn_range' :
    type_of% @_root_.Std.Legacy.Range.forIn_eq_forIn_range' := by
  intro m β _ r init f
  exact Std.Legacy.Range.forIn'_eq_forIn'_range' r init (fun a _ => f a)

end OmegaChecks.InitPort.Alternatives
