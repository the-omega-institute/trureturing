module
public import OmegaChecks.InitPort.Alternatives.Range.LoopEndpoints
public import Init.Data.Range.Polymorphic.Lemmas
import all Init.Data.Range.Polymorphic.Lemmas
import Init.Data.Iterators.Lemmas.Basic
import Init.Data.Iterators.Lemmas.Consumers.Loop
import all Init.Data.Array.Basic
import all Init.Data.Range.Polymorphic.Basic
import all Init.Data.Range.Polymorphic.RangeIterator
import all Init.Data.Range.Polymorphic.Iterators
public import Init.Data.Range.Polymorphic.NatLemmas
public import Init.Data.Range.Polymorphic.IntLemmas
public import OmegaChecks.InitPort.Alternatives.Range.ListLookup
import all OmegaChecks.InitPort.Alternatives.Range.ListLookup

/-! Membership, ordered enumeration and mapped range lists. -/

open Std Std.PRange

namespace OmegaChecks.InitPort.Alternatives

private theorem rangeFilterEqSome {o : Option α} {a : α} (p : α → Bool) :
    o.filter p = some a ↔ o = some a ∧ p a := by
  constructor
  · intro eq
    cases o with
    | none => cases eq
    | some x =>
      by_cases pass : p x = true
      · rw [Option.filter_some_pos pass] at eq
        cases eq
        exact ⟨rfl, pass⟩
      · rw [Option.filter_some, ite_eq_right pass] at eq
        cases eq
  · rintro ⟨rfl, pass⟩
    exact Option.filter_some_pos pass

private theorem indexedRangeMem {xs : List α} {f : Nat → Option α} {a : α} (p : α → Bool)
    (lookup : ∀ i, xs[i]? = (f i).filter p) : a ∈ xs ↔ (∃ i, f i = some a) ∧ p a := by
  constructor
  · intro mem
    obtain ⟨i, h⟩ := List.mem_iff_getElem?.mp mem
    obtain ⟨someAt, pass⟩ := (rangeFilterEqSome p).mp ((lookup i).symm.trans h)
    exact ⟨⟨i, someAt⟩, pass⟩
  · rintro ⟨⟨i, hit⟩, pass⟩
    exact List.mem_iff_getElem?.mpr ⟨i, (lookup i).trans ((rangeFilterEqSome p).mpr ⟨hit, pass⟩)⟩

public theorem Std.Rcc.mem_toList_iff_mem : type_of% @_root_.Std.Rcc.mem_toList_iff_mem := by
  intro α r _ _ _ _ _ _ a
  exact (indexedRangeMem (f := fun i => UpwardEnumerable.succMany? i r.lower)
    (fun x => decide (x ≤ r.upper)) (fun _ => _root_.Std.Rcc.getElem?_toList_eq)).trans
      ⟨fun ⟨reach, above⟩ => ⟨UpwardEnumerable.le_iff.mpr reach, of_decide_eq_true above⟩,
       fun h => ⟨UpwardEnumerable.le_iff.mp h.1, decide_eq_true h.2⟩⟩

public theorem Std.Rco.mem_toList_iff_mem : type_of% @_root_.Std.Rco.mem_toList_iff_mem := by
  intro α r _ _ _ _ _ _ _ _ a
  exact (indexedRangeMem (f := fun i => UpwardEnumerable.succMany? i r.lower)
    (fun x => decide (x < r.upper)) (fun _ => _root_.Std.Rco.getElem?_toList_eq)).trans
      ⟨fun ⟨reach, above⟩ => ⟨UpwardEnumerable.le_iff.mpr reach, of_decide_eq_true above⟩,
       fun h => ⟨UpwardEnumerable.le_iff.mp h.1, decide_eq_true h.2⟩⟩

public theorem Std.Roc.mem_toList_iff_mem : type_of% @_root_.Std.Roc.mem_toList_iff_mem := by
  intro α r _ _ _ _ _ _ _ _ a
  exact (indexedRangeMem (f := fun i => UpwardEnumerable.succMany? (i + 1) r.lower)
    (fun x => decide (x ≤ r.upper)) (fun _ => _root_.Std.Roc.getElem?_toList_eq)).trans
      ⟨fun ⟨reach, above⟩ => ⟨UpwardEnumerable.lt_iff.mpr reach, of_decide_eq_true above⟩,
       fun h => ⟨UpwardEnumerable.lt_iff.mp h.1, decide_eq_true h.2⟩⟩

public theorem Std.Roo.mem_toList_iff_mem : type_of% @_root_.Std.Roo.mem_toList_iff_mem := by
  intro α r _ _ _ _ _ _ a
  exact (indexedRangeMem (f := fun i => UpwardEnumerable.succMany? (i + 1) r.lower)
    (fun x => decide (x < r.upper)) (fun _ => _root_.Std.Roo.getElem?_toList_eq)).trans
      ⟨fun ⟨reach, above⟩ => ⟨UpwardEnumerable.lt_iff.mpr reach, of_decide_eq_true above⟩,
       fun h => ⟨UpwardEnumerable.lt_iff.mp h.1, decide_eq_true h.2⟩⟩

public theorem Std.Rci.mem_toList_iff_mem : type_of% @_root_.Std.Rci.mem_toList_iff_mem := by
  intro α r _ _ _ _ _ a
  constructor
  · intro h
    obtain ⟨i, hit⟩ := List.mem_iff_getElem?.mp h
    exact UpwardEnumerable.le_iff.mpr ⟨i, _root_.Std.Rci.getElem?_toList_eq.symm.trans hit⟩
  · intro h
    obtain ⟨i, hit⟩ := UpwardEnumerable.le_iff.mp h
    exact List.mem_iff_getElem?.mpr ⟨i, _root_.Std.Rci.getElem?_toList_eq.trans hit⟩

public theorem Std.Roi.mem_toList_iff_mem : type_of% @_root_.Std.Roi.mem_toList_iff_mem := by
  intro α r _ _ _ _ _ a
  rw [_root_.Std.Roi.toList_eq_match_rci]
  cases hs : UpwardEnumerable.succ? r.lower with
  | none =>
    constructor
    · intro h
      cases h
    · intro h
      obtain ⟨i, hit⟩ := UpwardEnumerable.lt_iff.mp h
      rw [UpwardEnumerable.succMany?_add_one_eq_succ?_bind_succMany?, hs] at hit
      cases hit
  | some next =>
    constructor
    · intro h
      obtain ⟨i, hit⟩ := List.mem_iff_getElem?.mp h
      apply UpwardEnumerable.lt_iff.mpr
      refine ⟨i, ?_⟩
      rw [UpwardEnumerable.succMany?_add_one_eq_succ?_bind_succMany?, hs]
      exact _root_.Std.Rci.getElem?_toList_eq.symm.trans hit
    · intro h
      obtain ⟨i, hit⟩ := UpwardEnumerable.lt_iff.mp h
      rw [UpwardEnumerable.succMany?_add_one_eq_succ?_bind_succMany?, hs] at hit
      exact List.mem_iff_getElem?.mpr ⟨i, _root_.Std.Rci.getElem?_toList_eq.trans hit⟩

public theorem Std.Ric.mem_toList_iff_mem : type_of% @_root_.Std.Ric.mem_toList_iff_mem := by
  intro α r _ _ _ _ _ _ _ _ a
  letI : Nonempty α := ⟨r.upper⟩
  have mem := indexedRangeMem (a := a) (f := fun i => UpwardEnumerable.succMany? i UpwardEnumerable.least)
    (fun x => decide (x ≤ r.upper)) (fun _ => _root_.Std.Ric.getElem?_toList_eq (r := r))
  exact ⟨fun h => of_decide_eq_true (mem.mp h).2,
    fun h => mem.mpr ⟨UpwardEnumerable.least_le, decide_eq_true h⟩⟩

public theorem Std.Rio.mem_toList_iff_mem : type_of% @_root_.Std.Rio.mem_toList_iff_mem := by
  intro α r _ _ _ _ _ _ _ _ a
  letI : Nonempty α := ⟨r.upper⟩
  have mem := indexedRangeMem (a := a) (f := fun i => UpwardEnumerable.succMany? i UpwardEnumerable.least)
    (fun x => decide (x < r.upper)) (fun _ => _root_.Std.Rio.getElem?_toList_eq (r := r))
  exact ⟨fun h => of_decide_eq_true (mem.mp h).2,
    fun h => mem.mpr ⟨UpwardEnumerable.least_le, decide_eq_true h⟩⟩

public theorem Std.Rii.mem_toList : type_of% @_root_.Std.Rii.mem_toList := by
  intro α r _ _ _ _ _ a
  letI : Nonempty α := ⟨a⟩
  obtain ⟨i, hit⟩ := UpwardEnumerable.least_le (a := a)
  apply List.mem_iff_getElem?.mpr
  refine ⟨i, _root_.Std.Rii.getElem?_toList_eq.trans ?_⟩
  rw [UpwardEnumerable.least?_eq_some]
  exact hit

public theorem Std.Rcc.mem_toArray_iff_mem : type_of% @_root_.Std.Rcc.mem_toArray_iff_mem := by
  intro α r _ _ _ _ _ _ a
  rw [Array.mem_def, _root_.Std.Rcc.toList_toArray]
  exact _root_.Std.Rcc.mem_toList_iff_mem

public theorem Std.Rco.mem_toArray_iff_mem : type_of% @_root_.Std.Rco.mem_toArray_iff_mem := by
  intro α r _ _ _ _ _ _ _ _ a
  rw [Array.mem_def, _root_.Std.Rco.toList_toArray]
  exact _root_.Std.Rco.mem_toList_iff_mem

public theorem Std.Roc.mem_toArray_iff_mem : type_of% @_root_.Std.Roc.mem_toArray_iff_mem := by
  intro α r _ _ _ _ _ _ _ _ a
  rw [Array.mem_def, _root_.Std.Roc.toList_toArray]
  exact _root_.Std.Roc.mem_toList_iff_mem

public theorem Std.Roo.mem_toArray_iff_mem : type_of% @_root_.Std.Roo.mem_toArray_iff_mem := by
  intro α r _ _ _ _ _ _ a
  rw [Array.mem_def, _root_.Std.Roo.toList_toArray]
  exact _root_.Std.Roo.mem_toList_iff_mem

public theorem Std.Rci.mem_toArray_iff_mem : type_of% @_root_.Std.Rci.mem_toArray_iff_mem := by
  intro α r _ _ _ _ _ a
  rw [Array.mem_def, _root_.Std.Rci.toList_toArray]
  exact _root_.Std.Rci.mem_toList_iff_mem

public theorem Std.Roi.mem_toArray_iff_mem : type_of% @_root_.Std.Roi.mem_toArray_iff_mem := by
  intro α r _ _ _ _ _ a
  rw [Array.mem_def, _root_.Std.Roi.toList_toArray]
  exact _root_.Std.Roi.mem_toList_iff_mem

public theorem Std.Ric.mem_toArray_iff_mem : type_of% @_root_.Std.Ric.mem_toArray_iff_mem := by
  intro α r _ _ _ _ _ _ _ _ a
  rw [Array.mem_def, _root_.Std.Ric.toList_toArray]
  exact _root_.Std.Ric.mem_toList_iff_mem

public theorem Std.Rio.mem_toArray_iff_mem : type_of% @_root_.Std.Rio.mem_toArray_iff_mem := by
  intro α r _ _ _ _ _ _ _ _ a
  rw [Array.mem_def, _root_.Std.Rio.toList_toArray]
  exact _root_.Std.Rio.mem_toList_iff_mem

public theorem Std.Rii.mem_toArray : type_of% @_root_.Std.Rii.mem_toArray := by
  intro α r _ _ _ _ _ a
  rw [Array.mem_def, _root_.Std.Rii.toList_toArray]
  exact _root_.Std.Rii.mem_toList

public theorem Std.Rxc.Iterator.pairwise_toList_upwardEnumerableLt :
    type_of% @_root_.Std.Rxc.Iterator.pairwise_toList_upwardEnumerableLt := by
  intro α _ _ _ _ _ _ it
  induction it using _root_.Std.Iter.inductSteps with
  | step it ihy ihs =>
    rw [_root_.Std.Rxc.Iterator.toList_eq_match]
    cases hn : it.internalState.next with
    | none => exact .nil
    | some a =>
      dsimp only
      by_cases bound : a ≤ it.internalState.upperBound
      · rw [ite_eq_left bound]
        apply List.Pairwise.cons
        · intro b member
          obtain ⟨c, step, le⟩ := _root_.Std.Rxc.Iterator.upwardEnumerableLe_of_isPlausibleIndirectOutput
            (_root_.Std.Iter.mem_toList_iff_isPlausibleIndirectOutput.mp member)
          exact UpwardEnumerable.lt_of_lt_of_le (UpwardEnumerable.lt_succ? step) le
        · apply ihy (out := a)
          apply _root_.Std.Rxc.Iterator.isPlausibleStep_iff.mpr
          unfold _root_.Std.Rxc.Iterator.step
          rw [hn]
          dsimp only
          rw [ite_eq_left bound]
      · rw [ite_eq_right bound]
        exact .nil

public theorem Std.Rxo.Iterator.pairwise_toList_upwardEnumerableLt :
    type_of% @_root_.Std.Rxo.Iterator.pairwise_toList_upwardEnumerableLt := by
  intro α _ _ _ _ _ _ it
  induction it using _root_.Std.Iter.inductSteps with
  | step it ihy ihs =>
    rw [_root_.Std.Rxo.Iterator.toList_eq_match]
    cases hn : it.internalState.next with
    | none => exact .nil
    | some a =>
      dsimp only
      by_cases bound : a < it.internalState.upperBound
      · rw [ite_eq_left bound]
        apply List.Pairwise.cons
        · intro b member
          obtain ⟨c, step, le⟩ := _root_.Std.Rxo.Iterator.upwardEnumerableLe_of_isPlausibleIndirectOutput
            (_root_.Std.Iter.mem_toList_iff_isPlausibleIndirectOutput.mp member)
          exact UpwardEnumerable.lt_of_lt_of_le (UpwardEnumerable.lt_succ? step) le
        · apply ihy (out := a)
          apply _root_.Std.Rxo.Iterator.isPlausibleStep_iff.mpr
          unfold _root_.Std.Rxo.Iterator.step
          rw [hn]
          dsimp only
          rw [ite_eq_left bound]
      · rw [ite_eq_right bound]
        exact .nil

public theorem Std.Rxi.Iterator.pairwise_toList_upwardEnumerableLt :
    type_of% @_root_.Std.Rxi.Iterator.pairwise_toList_upwardEnumerableLt := by
  intro α _ _ _ it
  induction it using _root_.Std.Iter.inductSteps with
  | step it ihy ihs =>
    rw [_root_.Std.Rxi.Iterator.toList_eq_match]
    cases hn : it.internalState.next with
    | none => exact .nil
    | some a =>
      apply List.Pairwise.cons
      · intro b member
        obtain ⟨c, step, le⟩ := _root_.Std.Rxi.Iterator.upwardEnumerableLe_of_isPlausibleIndirectOutput
          (_root_.Std.Iter.mem_toList_iff_isPlausibleIndirectOutput.mp member)
        exact UpwardEnumerable.lt_of_lt_of_le (UpwardEnumerable.lt_succ? step) le
      · apply ihy (out := a)
        apply _root_.Std.Rxi.Iterator.isPlausibleStep_iff.mpr
        unfold _root_.Std.Rxi.Iterator.step
        rw [hn]

private theorem orderedHeadAbsent {R : α → α → Prop} [Std.Asymm R] {x : α} {xs : List α}
    (ordered : (x :: xs).Pairwise R) (mem : x ∈ xs) : False :=
  let loop := List.rel_of_pairwise_cons ordered mem
  Std.Asymm.asymm x x loop loop

public theorem Std.eq_of_pairwise_lt_of_mem_iff_mem :
    type_of% (private_decl% @_root_.Std.eq_of_pairwise_lt_of_mem_iff_mem) := by
  intro α rel asymm l l' sorted sorted' same
  induction l generalizing l' with
  | nil =>
    cases l' with
    | nil => rfl
    | cons y ys => cases (same y).mpr List.mem_cons_self
  | cons x xs ih =>
    cases l' with
    | nil => cases (same x).mp List.mem_cons_self
    | cons y ys =>
      have heads : x = y := by
        rcases List.mem_cons.mp ((same x).mp List.mem_cons_self) with eq | right
        · exact eq
        · rcases List.mem_cons.mp ((same y).mpr List.mem_cons_self) with eq | left
          · exact eq.symm
          · exact (Std.Asymm.asymm x y (List.rel_of_pairwise_cons sorted left)
              (List.rel_of_pairwise_cons sorted' right)).elim
      cases heads
      apply congrArg (List.cons x)
      apply ih sorted.tail sorted'.tail
      intro a
      constructor
      · intro mem
        rcases List.mem_cons.mp ((same a).mp (.tail x mem)) with rfl | found
        · exact (orderedHeadAbsent sorted mem).elim
        · exact found
      · intro mem
        rcases List.mem_cons.mp ((same a).mpr (.tail x mem)) with rfl | found
        · exact (orderedHeadAbsent sorted' mem).elim
        · exact found

private theorem sortedRangeImage [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    [LinearlyUpwardEnumerable α] [InfinitelyUpwardEnumerable α]
    (ys xs : List α) (left : ys.Pairwise UpwardEnumerable.LT) (right : xs.Pairwise UpwardEnumerable.LT)
    (preimage : ∀ y, y ∈ ys ↔ ∃ x, y = succ x ∧ x ∈ xs) : ys = xs.map succ := by
  apply (private_decl% _root_.Std.eq_of_pairwise_lt_of_mem_iff_mem) left
    (right.map succ fun _ _ => UpwardEnumerable.succ_lt_succ_iff.mpr)
  intro y
  constructor
  · intro hy
    obtain ⟨x, eq, mem⟩ := (preimage y).mp hy
    exact List.mem_map.mpr ⟨x, mem, eq.symm⟩
  · intro hy
    obtain ⟨x, mem, eq⟩ := List.mem_map.mp hy
    exact (preimage y).mpr ⟨x, eq.symm, mem⟩

public theorem Std.Rcc.toList_succ_succ_eq_map : type_of% @_root_.Std.Rcc.toList_succ_succ_eq_map := by
  intro α _ _ _ _ _ _ _ _ lo hi
  apply sortedRangeImage _ _ _root_.Std.Rcc.pairwise_toList_upwardEnumerableLt _root_.Std.Rcc.pairwise_toList_upwardEnumerableLt
  intro y
  constructor
  · intro hy
    obtain ⟨x, eq, mem⟩ := _root_.Std.Rcc.mem_succ_succ_iff.mp (_root_.Std.Rcc.mem_toList_iff_mem.mp hy)
    exact ⟨x, eq, _root_.Std.Rcc.mem_toList_iff_mem.mpr mem⟩
  · rintro ⟨x, eq, mem⟩
    exact _root_.Std.Rcc.mem_toList_iff_mem.mpr (_root_.Std.Rcc.mem_succ_succ_iff.mpr
      ⟨x, eq, _root_.Std.Rcc.mem_toList_iff_mem.mp mem⟩)

public theorem Std.Rco.toList_succ_succ_eq_map : type_of% @_root_.Std.Rco.toList_succ_succ_eq_map := by
  intro α _ _ _ _ _ _ _ _ _ _ _ lo hi
  apply sortedRangeImage _ _ _root_.Std.Rco.pairwise_toList_upwardEnumerableLt _root_.Std.Rco.pairwise_toList_upwardEnumerableLt
  intro y
  constructor
  · intro hy
    obtain ⟨x, eq, mem⟩ := _root_.Std.Rco.mem_succ_succ_iff.mp (_root_.Std.Rco.mem_toList_iff_mem.mp hy)
    exact ⟨x, eq, _root_.Std.Rco.mem_toList_iff_mem.mpr mem⟩
  · rintro ⟨x, eq, mem⟩
    exact _root_.Std.Rco.mem_toList_iff_mem.mpr (_root_.Std.Rco.mem_succ_succ_iff.mpr
      ⟨x, eq, _root_.Std.Rco.mem_toList_iff_mem.mp mem⟩)

public theorem Std.Rci.toList_succ_succ_eq_map : type_of% @_root_.Std.Rci.toList_succ_succ_eq_map := by
  intro α _ _ _ _ _ _ _ _ lo
  apply sortedRangeImage _ _ _root_.Std.Rci.pairwise_toList_upwardEnumerableLt _root_.Std.Rci.pairwise_toList_upwardEnumerableLt
  intro y
  constructor
  · intro hy
    obtain ⟨x, eq, mem⟩ := _root_.Std.Rci.mem_succ_iff.mp (_root_.Std.Rci.mem_toList_iff_mem.mp hy)
    exact ⟨x, eq, _root_.Std.Rci.mem_toList_iff_mem.mpr mem⟩
  · rintro ⟨x, eq, mem⟩
    exact _root_.Std.Rci.mem_toList_iff_mem.mpr (_root_.Std.Rci.mem_succ_iff.mpr
      ⟨x, eq, _root_.Std.Rci.mem_toList_iff_mem.mp mem⟩)

public theorem Std.Roc.toList_succ_succ_eq_map : type_of% @_root_.Std.Roc.toList_succ_succ_eq_map := by
  intro α _ _ _ _ _ _ _ _ _ _ _ lo hi
  apply sortedRangeImage _ _ _root_.Std.Roc.pairwise_toList_upwardEnumerableLt _root_.Std.Roc.pairwise_toList_upwardEnumerableLt
  intro y
  constructor
  · intro hy
    obtain ⟨x, eq, mem⟩ := _root_.Std.Roc.mem_succ_succ_iff.mp (_root_.Std.Roc.mem_toList_iff_mem.mp hy)
    exact ⟨x, eq, _root_.Std.Roc.mem_toList_iff_mem.mpr mem⟩
  · rintro ⟨x, eq, mem⟩
    exact _root_.Std.Roc.mem_toList_iff_mem.mpr (_root_.Std.Roc.mem_succ_succ_iff.mpr
      ⟨x, eq, _root_.Std.Roc.mem_toList_iff_mem.mp mem⟩)

public theorem Std.Roo.toList_succ_succ_eq_map : type_of% @_root_.Std.Roo.toList_succ_succ_eq_map := by
  intro α _ _ _ _ _ _ _ _ lo hi
  apply sortedRangeImage _ _ _root_.Std.Roo.pairwise_toList_upwardEnumerableLt _root_.Std.Roo.pairwise_toList_upwardEnumerableLt
  intro y
  constructor
  · intro hy
    obtain ⟨x, eq, mem⟩ := _root_.Std.Roo.mem_succ_succ_iff.mp (_root_.Std.Roo.mem_toList_iff_mem.mp hy)
    exact ⟨x, eq, _root_.Std.Roo.mem_toList_iff_mem.mpr mem⟩
  · rintro ⟨x, eq, mem⟩
    exact _root_.Std.Roo.mem_toList_iff_mem.mpr (_root_.Std.Roo.mem_succ_succ_iff.mpr
      ⟨x, eq, _root_.Std.Roo.mem_toList_iff_mem.mp mem⟩)

public theorem Std.Roi.toList_succ_succ_eq_map : type_of% @_root_.Std.Roi.toList_succ_succ_eq_map := by
  intro α _ _ _ _ _ _ _ _ lo
  apply sortedRangeImage _ _ _root_.Std.Roi.pairwise_toList_upwardEnumerableLt _root_.Std.Roi.pairwise_toList_upwardEnumerableLt
  intro y
  constructor
  · intro hy
    obtain ⟨x, eq, mem⟩ := _root_.Std.Roi.mem_succ_iff.mp (_root_.Std.Roi.mem_toList_iff_mem.mp hy)
    exact ⟨x, eq, _root_.Std.Roi.mem_toList_iff_mem.mpr mem⟩
  · rintro ⟨x, eq, mem⟩
    exact _root_.Std.Roi.mem_toList_iff_mem.mpr (_root_.Std.Roi.mem_succ_iff.mpr
      ⟨x, eq, _root_.Std.Roi.mem_toList_iff_mem.mp mem⟩)

public theorem Std.Rco.toList_eq_ite_rco : type_of% @_root_.Std.Rco.toList_eq_ite_rco := by
  intro α r _ _ _ _ _ _
  rw [_root_.Std.Rco.toList_eq_ite_roo]
  by_cases inside : r.lower < r.upper
  · rw [ite_eq_left inside, ite_eq_left inside, _root_.Std.Roo.toList_eq_match_rco]
    cases UpwardEnumerable.succ? r.lower <;> rfl
  · rw [ite_eq_right inside, ite_eq_right inside]

public theorem Std.Ric.toList_ne_nil : type_of% @_root_.Std.Ric.toList_ne_nil := by
  intro α r _ _ _ _ _ _ _ _ empty
  have member := (_root_.Std.Ric.mem_toList_iff_mem (r := r)).mpr
    (UpwardEnumerable.le_iff.mpr (UpwardEnumerable.le_refl r.upper))
  rw [empty] at member
  cases member

public theorem Std.Ric.toArray_ne_empty : type_of% @_root_.Std.Ric.toArray_ne_empty := by
  intro α r _ _ _ _ _ _ _ _ empty
  exact _root_.Std.Ric.toList_ne_nil ((_root_.Std.Ric.toList_toArray (r := r)).symm.trans (congrArg Array.toList empty))

public theorem Std.Rii.toList_eq_nil_iff : type_of% @_root_.Std.Rii.toList_eq_nil_iff := by
  intro α r _ _ _ _ _ _ _ _
  constructor
  · intro empty ⟨a⟩
    have member := _root_.Std.Rii.mem_toList (r := r) (a := a)
    rw [empty] at member
    cases member
  · intro absent
    cases h : r.toList with
    | nil => rfl
    | cons a _ => exact (absent ⟨a⟩).elim

public theorem Std.Rii.toArray_eq_empty_iff : type_of% @_root_.Std.Rii.toArray_eq_empty_iff := by
  intro α r _ _ _ _ _ _ _ _
  rw [← _root_.Std.Rii.toArray_toList]
  exact (arrayNilOfList _).trans _root_.Std.Rii.toList_eq_nil_iff

public theorem Std.Roc.toArray_eq_match : type_of% @_root_.Std.Roc.toArray_eq_match := by
  intro α r _ _ _ _ _ _
  apply Array.toList_inj.mp
  rw [_root_.Std.Roc.toList_toArray, _root_.Std.Roc.toList_eq_match]
  cases start : succ? r.lower with
  | none => rfl
  | some next =>
    dsimp only
    by_cases inside : next ≤ r.upper
    · rw [ite_eq_left inside, ite_eq_left inside, Array.toList_append, _root_.Std.Roc.toList_toArray]
      rfl
    · rw [ite_eq_right inside, ite_eq_right inside]

public theorem Std.Rii.toList_eq_match_roi : type_of% @_root_.Std.Rii.toList_eq_match_roi := by
  intro α r _ _ _ _
  rw [_root_.Std.Rii.toList_eq_match_rci]
  cases Least?.least? (α := α) with
  | none => rfl
  | some next => exact _root_.Std.Rci.toList_eq_toList_roi

public theorem Std.Rii.toArray_eq_match_roi : type_of% @_root_.Std.Rii.toArray_eq_match_roi := by
  intro α r _ _ _ _ _
  rw [_root_.Std.Rii.toArray_eq_match_rci]
  cases Least?.least? (α := α) with
  | none => rfl
  | some next => exact _root_.Std.Rci.toArray_eq_toArray_roi

public theorem Std.Rxc.Iterator.toList_eq_toList_rxoIterator :
    type_of% @_root_.Std.Rxc.Iterator.toList_eq_toList_rxoIterator := by
  intro α _ _ _ _ _ _ _ _ _ _ _ _ it
  rcases it with ⟨⟨start, upper⟩⟩
  cases start with
  | none =>
    rw [_root_.Std.Rxc.Iterator.toList_eq_match, _root_.Std.Rxo.Iterator.toList_eq_match]
  | some next => exact _root_.Std.Rcc.toList_eq_toList_rco (r := ⟨next, upper⟩)

public theorem Std.Ric.toList_succ_eq_map : type_of% @_root_.Std.Ric.toList_succ_eq_map := by
  intro α _ _ _ _ _ _ _ _ _ _ hi
  letI : Nonempty α := ⟨hi⟩
  rw [_root_.Std.Ric.toList_eq_toList_rcc, _root_.Std.Ric.toList_eq_toList_rcc,
    _root_.Std.Rcc.toList_eq_ite_roc]
  have bound : UpwardEnumerable.least ≤ succ hi := UpwardEnumerable.le_iff.mpr UpwardEnumerable.least_le
  rw [ite_eq_left bound, _root_.Std.Roc.toList_eq_match_rcc, UpwardEnumerable.succ?_eq_some]
  exact congrArg (List.cons _) (_root_.Std.Rcc.toList_succ_succ_eq_map (lo := UpwardEnumerable.least) (hi := hi))

public theorem Std.Rio.toList_succ_eq_map : type_of% @_root_.Std.Rio.toList_succ_eq_map := by
  intro α _ _ _ _ _ _ _ _ _ _ hi
  letI : Nonempty α := ⟨hi⟩
  letI : LE α := ⟨UpwardEnumerable.LE⟩
  letI : LawfulUpwardEnumerableLE α := ⟨fun _ _ => Iff.rfl⟩
  letI : DecidableLE α := fun a b => decidable_of_iff (a < succ b)
    (UpwardEnumerable.lt_iff.trans UpwardEnumerable.lt_succ_iff)
  rw [_root_.Std.Rio.toList_eq_toList_rco, _root_.Std.Rio.toList_eq_toList_rco, _root_.Std.Rco.toList_eq_ite_rco]
  have bound : UpwardEnumerable.least < succ hi :=
    UpwardEnumerable.lt_iff.mpr (UpwardEnumerable.lt_succ_iff.mpr UpwardEnumerable.least_le)
  rw [ite_eq_left bound, UpwardEnumerable.succ?_eq_some]
  exact congrArg (List.cons _) (_root_.Std.Rco.toList_succ_succ_eq_map (lo := UpwardEnumerable.least) (hi := hi))

end OmegaChecks.InitPort.Alternatives
