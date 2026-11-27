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
public import OmegaChecks.InitPort.Alternatives.Range.ListSize
import all OmegaChecks.InitPort.Alternatives.Range.ListSize

/-! Range heads, bounds and optional lookups. -/

open Std Std.PRange

namespace OmegaChecks.InitPort.Alternatives

private theorem consRangeEmpty (p : Prop) [Decidable p] (a : α) (tail : List α) :
    (if p then a :: tail else []) = [] ↔ ¬p := by
  constructor
  · intro empty hp
    rw [ite_eq_left hp] at empty
    contradiction
  · intro no
    exact ite_eq_right no

private theorem arrayNilOfList (xs : List α) : xs.toArray = #[] ↔ xs = [] :=
  ⟨fun eq => congrArg Array.toList eq, fun eq => congrArg List.toArray eq⟩

public theorem Std.Rcc.toList_eq_nil_iff : type_of% @_root_.Std.Rcc.toList_eq_nil_iff := by
  intro α r _ _ _ _ _ _
  rw [_root_.Std.Rcc.toList_eq_ite_roc]
  exact consRangeEmpty _ _ _

public theorem Std.Rco.toList_eq_nil_iff : type_of% @_root_.Std.Rco.toList_eq_nil_iff := by
  intro α r _ _ _ _ _ _
  rw [_root_.Std.Rco.toList_eq_ite_roo]
  exact consRangeEmpty _ _ _

public theorem Std.Roo.toList_eq_nil_iff : type_of% @_root_.Std.Roo.toList_eq_nil_iff := by
  intro α r _ _ _ _ _ _ _
  rw [_root_.Std.Roo.toList_eq_match_rco]
  cases h : UpwardEnumerable.succ? r.lower with
  | none =>
    constructor
    · intro _ _ eq
      cases eq
    · intro _
      rfl
  | some next =>
    constructor
    · intro empty a eq
      cases eq
      exact _root_.Std.Rco.toList_eq_nil_iff.mp empty
    · intro noneBelow
      exact _root_.Std.Rco.toList_eq_nil_iff.mpr (noneBelow next rfl)

public theorem Std.Rcc.toArray_eq_empty_iff : type_of% @_root_.Std.Rcc.toArray_eq_empty_iff := by
  intro α r _ _ _ _ _ _
  rw [← _root_.Std.Rcc.toArray_toList]
  exact (arrayNilOfList _).trans _root_.Std.Rcc.toList_eq_nil_iff

public theorem Std.Rco.toArray_eq_empty_iff : type_of% @_root_.Std.Rco.toArray_eq_empty_iff := by
  intro α r _ _ _ _ _ _
  rw [← _root_.Std.Rco.toArray_toList]
  exact (arrayNilOfList _).trans _root_.Std.Rco.toList_eq_nil_iff

public theorem Std.Roo.toArray_eq_empty_iff : type_of% @_root_.Std.Roo.toArray_eq_empty_iff := by
  intro α r _ _ _ _ _ _ _
  rw [← _root_.Std.Roo.toArray_toList]
  exact (arrayNilOfList _).trans _root_.Std.Roo.toList_eq_nil_iff

public theorem Std.Rci.isEmpty_iff_forall_not_mem : type_of% @_root_.Std.Rci.isEmpty_iff_forall_not_mem := by
  intro α r _ _ _ _ _ _ _
  constructor
  · intro empty
    change false = true at empty
    cases empty
  · intro absent
    exact (absent r.lower (UpwardEnumerable.le_iff.mpr (UpwardEnumerable.le_refl _))).elim

public theorem Std.Ric.isEmpty_iff_forall_not_mem : type_of% @_root_.Std.Ric.isEmpty_iff_forall_not_mem := by
  intro α r _ _ _ _ _ _ _
  constructor
  · intro empty
    change false = true at empty
    cases empty
  · intro absent
    exact (absent r.upper (UpwardEnumerable.le_iff.mpr (UpwardEnumerable.le_refl _))).elim

public theorem Std.Rii.isEmpty_iff_forall_not_mem : type_of% @_root_.Std.Rii.isEmpty_iff_forall_not_mem := by
  intro α r _ _ _ _ _ _ _
  constructor
  · intro empty a _
    exact (_root_.Std.Rii.isEmpty_iff.mp empty) ⟨a⟩
  · intro absent
    exact _root_.Std.Rii.isEmpty_iff.mpr fun ⟨a⟩ => absent a True.intro

public theorem Std.Roc.toList_eq_nil_iff : type_of% @_root_.Std.Roc.toList_eq_nil_iff := by
  intro α r _ _ _ _ _ _ _ _
  rw [_root_.Std.Roc.toList_eq_match_rcc]
  cases s : UpwardEnumerable.succ? r.lower with
  | none =>
    constructor
    · intro _ lt
      obtain ⟨n, h⟩ := UpwardEnumerable.lt_iff.mp lt
      rw [UpwardEnumerable.succMany?_add_one_eq_succ?_bind_succMany?, s] at h
      cases h
    · intro _
      rfl
  | some next =>
    constructor
    · intro empty lt
      obtain ⟨n, h⟩ := UpwardEnumerable.lt_iff.mp lt
      rw [UpwardEnumerable.succMany?_add_one_eq_succ?_bind_succMany?, s] at h
      exact (_root_.Std.Rcc.toList_eq_nil_iff.mp empty) (UpwardEnumerable.le_iff.mpr ⟨n, h⟩)
    · intro before
      exact _root_.Std.Rcc.toList_eq_nil_iff.mpr fun le =>
        before (UpwardEnumerable.lt_iff.mpr (UpwardEnumerable.lt_of_lt_of_le
          (UpwardEnumerable.lt_succ? s) (UpwardEnumerable.le_iff.mp le)))

public theorem Std.Roc.toArray_eq_empty_iff : type_of% @_root_.Std.Roc.toArray_eq_empty_iff := by
  intro α r _ _ _ _ _ _ _ _
  rw [← _root_.Std.Roc.toArray_toList]
  exact (arrayNilOfList _).trans _root_.Std.Roc.toList_eq_nil_iff

public theorem Std.Rxi.Iterator.toList_eq_match : type_of% @_root_.Std.Rxi.Iterator.toList_eq_match := by
  intro α _ _ _ it
  rw [_root_.Std.Iter.toList_eq_match_step (it := it), _root_.Std.Rxi.Iterator.step_eq_step]
  unfold _root_.Std.Rxi.Iterator.step
  dsimp only [Subtype.val]
  cases h : it.internalState.next with
  | none => rfl
  | some a => rfl

public theorem Std.Rxc.Iterator.toList_eq_match : type_of% @_root_.Std.Rxc.Iterator.toList_eq_match := by
  intro α _ _ _ _ _ _ it
  rw [_root_.Std.Iter.toList_eq_match_step (it := it), _root_.Std.Rxc.Iterator.step_eq_step]
  unfold _root_.Std.Rxc.Iterator.step
  dsimp only [Subtype.val]
  cases h : it.internalState.next with
  | none => rfl
  | some a =>
    dsimp only
    by_cases bound : a ≤ it.internalState.upperBound
    · rw [ite_eq_left bound, ite_eq_left bound]
    · rw [ite_eq_right bound, ite_eq_right bound]

public theorem Std.Rxo.Iterator.toList_eq_match : type_of% @_root_.Std.Rxo.Iterator.toList_eq_match := by
  intro α _ _ _ _ _ _ it
  rw [_root_.Std.Iter.toList_eq_match_step (it := it), _root_.Std.Rxo.Iterator.step_eq_step]
  unfold _root_.Std.Rxo.Iterator.step
  dsimp only [Subtype.val]
  cases h : it.internalState.next with
  | none => rfl
  | some a =>
    dsimp only
    by_cases bound : a < it.internalState.upperBound
    · rw [ite_eq_left bound, ite_eq_left bound]
    · rw [ite_eq_right bound, ite_eq_right bound]

public theorem Std.Roi.toList_eq_match_rci : type_of% @_root_.Std.Roi.toList_eq_match_rci := by
  intro α r _ _ _
  unfold _root_.Std.Roi.toList _root_.Std.Roi.Internal.iter
  cases start : UpwardEnumerable.succ? r.lower with
  | none => rw [_root_.Std.Rxi.Iterator.toList_eq_match]
  | some a => rfl

public theorem Std.Rii.toList_eq_match_rci : type_of% @_root_.Std.Rii.toList_eq_match_rci := by
  intro α r _ _ _ _
  unfold _root_.Std.Rii.toList _root_.Std.Rii.Internal.iter
  cases start : Least?.least? (α := α) with
  | none => rw [_root_.Std.Rxi.Iterator.toList_eq_match]
  | some a => rfl

public theorem Std.Roc.toList_eq_match : type_of% @_root_.Std.Roc.toList_eq_match := by
  intro α r _ _ _ _ _ _
  rw [_root_.Std.Roc.toList_eq_match_rcc]
  cases UpwardEnumerable.succ? r.lower with
  | none => rfl
  | some a => exact _root_.Std.Rcc.toList_eq_ite_roc

public theorem Std.Roo.toList_eq_match : type_of% @_root_.Std.Roo.toList_eq_match := by
  intro α r _ _ _ _ _ _
  rw [_root_.Std.Roo.toList_eq_match_rco]
  cases UpwardEnumerable.succ? r.lower with
  | none => rfl
  | some a => exact _root_.Std.Rco.toList_eq_ite_roo

public theorem Std.Rci.length_toList : type_of% @_root_.Std.Rci.length_toList := by
  intro α r _ _ _ _ _
  obtain ⟨lo⟩ := r
  generalize hn : Rxi.HasSize.size lo = n
  induction n generalizing lo with
  | zero => exact False.elim (Nat.not_lt_zero _ (hn ▸ _root_.Std.Rxi.size_pos (lo := lo)))
  | succ n ih =>
    rw [_root_.Std.Rci.toList_eq_toList_roi, List.length_cons, _root_.Std.Roi.toList_eq_match_rci]
    cases hs : UpwardEnumerable.succ? lo with
    | none => exact (Rxi.LawfulHasSize.size_eq_one_of_succ?_eq_none _ hs).symm
    | some next =>
      have eq := Rxi.LawfulHasSize.size_eq_succ_of_succ?_eq_some _ _ hs
      exact (congrArg Nat.succ (ih next (Nat.succ.inj (eq.symm.trans hn)))).trans eq.symm

public theorem Std.Roi.length_toList : type_of% @_root_.Std.Roi.length_toList := by
  intro α r _ _ _ _ _
  rw [_root_.Std.Roi.toList_eq_match_rci, _root_.Std.Roi.size_eq_match_rci]
  cases UpwardEnumerable.succ? r.lower with
  | none => rfl
  | some next => exact _root_.Std.Rci.length_toList

public theorem Std.Rii.length_toList : type_of% @_root_.Std.Rii.length_toList := by
  intro α r _ _ _ _ _ _
  rw [_root_.Std.Rii.toList_eq_match_rci, _root_.Std.Rii.size_eq_match_rci]
  cases Least?.least? (α := α) with
  | none => rfl
  | some next => exact _root_.Std.Rci.length_toList

public theorem Std.Rci.getElem?_toList_eq : type_of% @_root_.Std.Rci.getElem?_toList_eq := by
  intro α _ _ _ r i
  induction i generalizing r with
  | zero =>
    rw [_root_.Std.Rci.toList_eq_toList_roi, UpwardEnumerable.succMany?_zero]
    rfl
  | succ i ih =>
    rw [_root_.Std.Rci.toList_eq_toList_roi, List.getElem?_cons_succ,
      _root_.Std.Roi.toList_eq_match_rci, UpwardEnumerable.succMany?_add_one_eq_succ?_bind_succMany?]
    cases UpwardEnumerable.succ? r.lower with
    | none => rfl
    | some next => exact ih (r := ⟨next⟩)

public theorem Std.toList_roc_eq_toList_rcc_of_isSome_succ? :
    type_of% @_root_.Std.toList_roc_eq_toList_rcc_of_isSome_succ? := by
  intro α _ _ _ _ _ _ lo hi h
  rw [_root_.Std.Roc.toList_eq_match_rcc]
  dsimp only
  generalize hs : UpwardEnumerable.succ? lo = start at h ⊢
  cases start with
  | none => cases h
  | some next => rfl

public theorem Std.toList_roo_eq_toList_rco_of_isSome_succ? :
    type_of% @_root_.Std.toList_roo_eq_toList_rco_of_isSome_succ? := by
  intro α _ _ _ _ _ _ lo hi h
  rw [_root_.Std.Roo.toList_eq_match_rco]
  dsimp only
  generalize hs : UpwardEnumerable.succ? lo = start at h ⊢
  cases start with
  | none => cases h
  | some next => rfl

public theorem Std.toList_roi_eq_toList_rci_of_isSome_succ? :
    type_of% @_root_.Std.toList_roi_eq_toList_rci_of_isSome_succ? := by
  intro α _ _ _ lo h
  rw [_root_.Std.Roi.toList_eq_match_rci]
  dsimp only
  generalize hs : UpwardEnumerable.succ? lo = start at h ⊢
  cases start with
  | none => cases h
  | some next => rfl

public theorem Std.Roi.getElem?_toList_eq : type_of% @_root_.Std.Roi.getElem?_toList_eq := by
  intro α r _ _ _ _ _ _ i
  rw [_root_.Std.Roi.toList_eq_match_rci, UpwardEnumerable.succMany?_add_one_eq_succ?_bind_succMany?]
  cases UpwardEnumerable.succ? r.lower with
  | none => rfl
  | some a => exact _root_.Std.Rci.getElem?_toList_eq

private theorem lookupPresent {o : Option α} {a : α} (eq : o = some a) : o.isSome := eq ▸ rfl

private theorem filterLookupPresent {p : α → Bool} {o : Option α} {a : α}
    (eq : o.filter p = some a) : o.isSome := by
  cases o with
  | none => cases eq
  | some x => rfl

public theorem Std.Rcc.isSome_succMany?_of_lt_length_toList :
    type_of% @_root_.Std.Rcc.isSome_succMany?_of_lt_length_toList := by
  intro α r _ _ _ _ _ _ i h
  exact filterLookupPresent ((_root_.Std.Rcc.getElem?_toList_eq (r := r) (i := i)).symm.trans
    (getElem?_pos r.toList i h))

public theorem Std.Rcc.isSome_succMany?_of_lt_size_toArray :
    type_of% @_root_.Std.Rcc.isSome_succMany?_of_lt_size_toArray := by
  intro α r _ _ _ _ _ _ i h
  exact filterLookupPresent ((_root_.Std.Rcc.getElem?_toArray_eq (r := r) (i := i)).symm.trans
    (getElem?_pos r.toArray i h))

public theorem Std.Roc.isSome_succMany?_of_lt_length_toList :
    type_of% @_root_.Std.Roc.isSome_succMany?_of_lt_length_toList := by
  intro α r _ _ _ _ _ _ i h
  exact filterLookupPresent ((_root_.Std.Roc.getElem?_toList_eq (r := r) (i := i)).symm.trans
    (getElem?_pos r.toList i h))

public theorem Std.Roc.isSome_succMany?_of_lt_size_toArray :
    type_of% @_root_.Std.Roc.isSome_succMany?_of_lt_size_toArray := by
  intro α r _ _ _ _ _ _ i h
  exact filterLookupPresent ((_root_.Std.Roc.getElem?_toArray_eq (r := r) (i := i)).symm.trans
    (getElem?_pos r.toArray i h))

public theorem Std.Ric.isSome_succMany?_of_lt_length_toList :
    type_of% @_root_.Std.Ric.isSome_succMany?_of_lt_length_toList := by
  intro α r _ _ _ _ _ _ _ _ i h
  exact filterLookupPresent ((_root_.Std.Ric.getElem?_toList_eq (r := r) (i := i)).symm.trans
    (getElem?_pos r.toList i h))

public theorem Std.Ric.isSome_succMany?_of_lt_size_toArray :
    type_of% @_root_.Std.Ric.isSome_succMany?_of_lt_size_toArray := by
  intro α r _ _ _ _ _ _ _ _ i h
  exact filterLookupPresent ((_root_.Std.Ric.getElem?_toArray_eq (r := r) (i := i)).symm.trans
    (getElem?_pos r.toArray i h))

public theorem Std.Rco.isSome_succMany?_of_lt_length_toList :
    type_of% @_root_.Std.Rco.isSome_succMany?_of_lt_length_toList := by
  intro α r _ _ _ _ _ _ i h
  exact filterLookupPresent ((_root_.Std.Rco.getElem?_toList_eq (r := r) (i := i)).symm.trans
    (getElem?_pos r.toList i h))

public theorem Std.Rco.isSome_succMany?_of_lt_size_toArray :
    type_of% @_root_.Std.Rco.isSome_succMany?_of_lt_size_toArray := by
  intro α r _ _ _ _ _ _ i h
  exact filterLookupPresent ((_root_.Std.Rco.getElem?_toArray_eq (r := r) (i := i)).symm.trans
    (getElem?_pos r.toArray i h))

public theorem Std.Roo.isSome_succMany?_of_lt_length_toList :
    type_of% @_root_.Std.Roo.isSome_succMany?_of_lt_length_toList := by
  intro α r _ _ _ _ _ _ i h
  exact filterLookupPresent ((_root_.Std.Roo.getElem?_toList_eq (r := r) (i := i)).symm.trans
    (getElem?_pos r.toList i h))

public theorem Std.Roo.isSome_succMany?_of_lt_size_toArray :
    type_of% @_root_.Std.Roo.isSome_succMany?_of_lt_size_toArray := by
  intro α r _ _ _ _ _ _ i h
  exact filterLookupPresent ((_root_.Std.Roo.getElem?_toArray_eq (r := r) (i := i)).symm.trans
    (getElem?_pos r.toArray i h))

public theorem Std.Rio.isSome_succMany?_of_lt_length_toList :
    type_of% @_root_.Std.Rio.isSome_succMany?_of_lt_length_toList := by
  intro α r _ _ _ _ _ _ _ _ i h
  exact filterLookupPresent ((_root_.Std.Rio.getElem?_toList_eq (r := r) (i := i)).symm.trans
    (getElem?_pos r.toList i h))

public theorem Std.Rio.isSome_succMany?_of_lt_size_toArray :
    type_of% @_root_.Std.Rio.isSome_succMany?_of_lt_size_toArray := by
  intro α r _ _ _ _ _ _ _ _ i h
  exact filterLookupPresent ((_root_.Std.Rio.getElem?_toArray_eq (r := r) (i := i)).symm.trans
    (getElem?_pos r.toArray i h))

public theorem Std.Rci.isSome_succMany?_of_lt_length_toList :
    type_of% @_root_.Std.Rci.isSome_succMany?_of_lt_length_toList := by
  intro α r _ _ _ _ _ _ i h
  exact lookupPresent ((_root_.Std.Rci.getElem?_toList_eq (r := r) (i := i)).symm.trans
    (getElem?_pos r.toList i h))

public theorem Std.Rci.isSome_succMany?_of_lt_size_toArray :
    type_of% @_root_.Std.Rci.isSome_succMany?_of_lt_size_toArray := by
  intro α r _ _ _ _ _ _ i h
  exact lookupPresent ((_root_.Std.Rci.getElem?_toArray_eq (r := r) (i := i)).symm.trans
    (getElem?_pos r.toArray i h))

public theorem Std.Roi.isSome_succMany?_of_lt_length_toList :
    type_of% @_root_.Std.Roi.isSome_succMany?_of_lt_length_toList := by
  intro α r _ _ _ _ _ _ i h
  exact lookupPresent ((_root_.Std.Roi.getElem?_toList_eq (r := r) (i := i)).symm.trans
    (getElem?_pos r.toList i h))

public theorem Std.Roi.isSome_succMany?_of_lt_size_toArray :
    type_of% @_root_.Std.Roi.isSome_succMany?_of_lt_size_toArray := by
  intro α r _ _ _ _ _ _ i h
  exact lookupPresent ((_root_.Std.Roi.getElem?_toArray_eq (r := r) (i := i)).symm.trans
    (getElem?_pos r.toArray i h))

public theorem Std.Rii.isSome_succMany?_of_lt_length_toList :
    type_of% @_root_.Std.Rii.isSome_succMany?_of_lt_length_toList := by
  intro α r _ _ _ _ _ i h
  exact lookupPresent ((_root_.Std.Rii.getElem?_toList_eq (r := r) (i := i)).symm.trans
    (getElem?_pos r.toList i h))

public theorem Std.Rii.isSome_succMany?_of_lt_size_toArray :
    type_of% @_root_.Std.Rii.isSome_succMany?_of_lt_size_toArray := by
  intro α r _ _ _ _ _ i h
  exact lookupPresent ((_root_.Std.Rii.getElem?_toArray_eq (r := r) (i := i)).symm.trans
    (getElem?_pos r.toArray i h))

end OmegaChecks.InitPort.Alternatives
