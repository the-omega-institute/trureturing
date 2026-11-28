module
import all Init.Data.String.Basic
import all Init.Data.String.Lemmas.Slice
import all Init.Data.String.Lemmas.Iterate
import all Init.Data.String.Lemmas.Pattern.Basic
import all Init.Data.ByteArray.Lemmas
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Slice
import all Init.Data.String.Substring

/-! Byte comparison and matching in a string slice. -/

namespace OmegaChecks.InitPort.Alternatives

/-- Advance by the UTF-8 width at the current slice position. -/
public def String.Slice.Pos.nextFast : type_of% @_root_.String.Slice.Pos.nextFast :=
  @_root_.String.Slice.Pos.next

private theorem windowSize {bs : ByteArray} {off len : Nat} (h : off + len ≤ bs.size) :
    (bs.extract off (off + len)).size = len :=
  ByteArray.size_extract.trans ((congrArg (· - off) (Nat.min_eq_left h)).trans (Nat.add_sub_cancel_left ..))

public theorem ByteArray.extract_eq_extract_iff_getElem : type_of% @_root_.ByteArray.extract_eq_extract_iff_getElem := by
  intro a b i j len hi hj
  have left := windowSize hi
  have right := windowSize hj
  constructor
  · intro eq k hk
    have h₁ : k < (a.extract i (i + len)).size := Nat.lt_of_lt_of_eq hk left.symm
    have h₂ : k < (b.extract j (j + len)).size := Nat.lt_of_lt_of_eq hk right.symm
    exact (ByteArray.getElem_extract h₁).symm.trans
      ((show (a.extract i (i + len))[k] = (b.extract j (j + len))[k] from by
          generalize a.extract i (i + len) = x at eq h₁ ⊢
          cases eq
          rfl).trans (ByteArray.getElem_extract h₂))
  · intro pointwise
    exact ByteArray.ext_getElem (left.trans right.symm) fun k h₁ h₂ =>
      (ByteArray.getElem_extract h₁).trans ((pointwise k (left ▸ h₁)).trans (ByteArray.getElem_extract h₂).symm)

public theorem String.Slice.Pattern.Internal.memcmpStr_eq_true_iff :
    type_of% @_root_.String.Slice.Pattern.Internal.memcmpStr_eq_true_iff := by
  intro lhs rhs ls rs len hl hr
  let same (k : Nat) (hk : k < len.byteIdx) :=
    lhs.toByteArray[ls.byteIdx + k]'(Nat.lt_of_lt_of_le (Nat.add_lt_add_left hk _) hl) =
    rhs.toByteArray[rs.byteIdx + k]'(Nat.lt_of_lt_of_le (Nat.add_lt_add_left hk _) hr)
  have loop (curr : String.Pos.Raw) :
      _root_.String.Slice.Pattern.Internal.memcmpStr.go lhs rhs ls rs len hl hr curr = true ↔
        ∀ k, curr.byteIdx ≤ k → (hk : k < len.byteIdx) → same k hk := by
    fun_induction _root_.String.Slice.Pattern.Internal.memcmpStr.go with
    | case1 p lt lvalid rvalid matched ih =>
      constructor
      · intro passed k lower upper
        obtain rfl | after := Nat.eq_or_lt_of_le lower
        · exact eq_of_beq matched
        · exact ih.mp passed k after upper
      · exact fun whole => ih.mpr (fun k lower upper => whole k (Nat.le_trans (Nat.le_succ _) lower) upper)
    | case2 p lt lvalid rvalid different =>
      exact ⟨(fun h => nomatch h), fun whole => (different (beq_iff_eq.mpr (whole _ (Nat.le_refl _) lt))).elim⟩
    | case3 p stopped =>
      exact ⟨fun _ k lower upper => (stopped (Nat.lt_of_le_of_lt lower upper)).elim, fun _ => rfl⟩
  exact (loop 0).trans
    (Iff.trans ⟨fun h k hk => h k (Nat.zero_le _) hk, fun h k _ hk => h k hk⟩
      (ByteArray.extract_eq_extract_iff_getElem hl hr).symm)

private theorem fullWindow (s : String.Slice) : s.copy.toByteArray.extract 0 s.utf8ByteSize = s.copy.toByteArray := by
  rw [String.Slice.utf8ByteSize_eq_size_toByteArray_copy]
  exact ByteArray.extract_zero_size

public theorem String.Slice.beq_eq_true_iff : type_of% @_root_.String.Slice.beq_eq_true_iff := by
  intro s t
  change _root_.String.Slice.beq s t = true ↔ _
  fun_cases _root_.String.Slice.beq with
  | case1 equal =>
    refine _root_.String.Slice.Pattern.Internal.memcmpSlice_eq_true_iff.trans ?_
    change s.copy.toByteArray.extract 0 (0 + s.utf8ByteSize) = t.copy.toByteArray.extract 0 (0 + s.utf8ByteSize) ↔ _
    have left := (congrArg (s.copy.toByteArray.extract 0) (Nat.zero_add _)).trans (fullWindow s)
    have right := (congrArg (t.copy.toByteArray.extract 0) ((Nat.zero_add _).trans equal)).trans (fullWindow t)
    exact ⟨fun eq => String.toByteArray_inj.mp (left.symm.trans (eq.trans right)),
      fun eq => left.trans ((congrArg String.toByteArray eq).trans right.symm)⟩
  | case2 different =>
    refine ⟨(fun h => nomatch h), fun eq => (different ?_).elim⟩
    exact _root_.String.Slice.utf8ByteSize_copy.symm.trans
      ((congrArg String.utf8ByteSize eq).trans _root_.String.Slice.utf8ByteSize_copy)

private theorem falseIffNot {b : Bool} {p : Prop} (h : b = true ↔ p) : b = false ↔ ¬p := by
  cases b with
  | false => exact ⟨fun _ hp => Bool.noConfusion (h.mpr hp), fun _ => rfl⟩
  | true => exact ⟨fun eq => Bool.noConfusion eq, fun hn => (hn (h.mp rfl)).elim⟩

public theorem String.Slice.beq_eq_false_iff : type_of% @_root_.String.Slice.beq_eq_false_iff :=
  falseIffNot String.Slice.beq_eq_true_iff

public theorem ByteArray.validateUTF8_eq_false_iff :
    type_of% @_root_.ByteArray.validateUTF8_eq_false_iff :=
  falseIffNot _root_.ByteArray.validateUTF8_eq_true_iff

public theorem String.Pos.Raw.isValid_eq_false_iff :
    type_of% @_root_.String.Pos.Raw.isValid_eq_false_iff :=
  falseIffNot _root_.String.Pos.Raw.isValid_eq_true_iff

public theorem String.Pos.Raw.isValidForSlice_eq_false_iff :
    type_of% @_root_.String.Pos.Raw.isValidForSlice_eq_false_iff :=
  falseIffNot _root_.String.Pos.Raw.isValidForSlice_eq_true_iff

public theorem List.utf8Encode_eq_empty : type_of% @_root_.List.utf8Encode_eq_empty := by
  intro l
  constructor
  · intro empty
    cases l with
    | nil => rfl
    | cons c cs =>
      have size := congrArg ByteArray.size empty
      rw [List.utf8Encode_cons, ByteArray.size_append, List.utf8Encode_singleton,
        List.size_toByteArray, ByteArray.size_empty] at size
      exact (String.utf8EncodeChar_ne_nil
        (List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_add_eq_zero_right size))).elim
  · rintro rfl
    exact List.utf8Encode_nil

public theorem String.Slice.beq_eq_decide : type_of% @_root_.String.Slice.beq_eq_decide :=
  Bool.eq_iff_iff.mpr (String.Slice.beq_eq_true_iff.trans ⟨fun h => decide_eq_true h, of_decide_eq_true⟩)

public theorem equivBEq_of_iff_apply_eq : type_of% @_root_.equivBEq_of_iff_apply_eq := by
  intro α β _ f h
  exact {
    symm := fun {a b} eq => (h b a).mpr ((h a b).mp eq).symm
    trans := fun {a b c} ab bc => (h a c).mpr (((h a b).mp ab).trans ((h b c).mp bc))
    rfl := fun {a} => (h a a).mpr rfl
  }

public theorem String.Slice.instEquivBEq : EquivBEq String.Slice :=
  equivBEq_of_iff_apply_eq String.Slice.copy (fun _ _ => String.Slice.beq_eq_true_iff)

public theorem String.Slice.beq_list_iff : type_of% @_root_.String.Slice.beq_list_iff := by
  intro xs
  induction xs with
  | nil =>
    intro ys
    cases ys with
    | nil => exact ⟨fun _ => rfl, fun _ => rfl⟩
    | cons => exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
  | cons x xs ih =>
    intro ys
    cases ys with
    | nil => exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
    | cons y ys =>
      refine ⟨fun hb => ?_, fun eq => ?_⟩
      · obtain ⟨hd, tl⟩ := Bool.and_eq_true_iff.mp hb
        exact (congrArg (List.cons x.copy) (ih.mp tl)).trans
          (congrArg (fun z => z :: ys.map String.Slice.copy) (String.Slice.beq_eq_true_iff.mp hd))
      · obtain ⟨hd, tl⟩ := List.cons.inj eq
        exact Bool.and_eq_true_iff.mpr ⟨String.Slice.beq_eq_true_iff.mpr hd, ih.mpr tl⟩

public theorem String.Slice.beq_list_eq_false_iff : type_of% @_root_.String.Slice.beq_list_eq_false_iff :=
  falseIffNot String.Slice.beq_list_iff

public theorem String.Slice.beq_list_eq_decide : type_of% @_root_.String.Slice.beq_list_eq_decide :=
  Bool.eq_iff_iff.mpr (String.Slice.beq_list_iff.trans ⟨fun h => decide_eq_true h, of_decide_eq_true⟩)

public theorem String.Slice.le_posLT_iff : type_of% @_root_.String.Slice.le_posLT_iff := by
  intro s p h q
  exact (_root_.String.Slice.le_posLE_iff (p := q) (q := p.dec)).trans (Nat.le_pred_iff_lt h)

public theorem String.Slice.Pos.le_prev_iff_lt : type_of% @_root_.String.Slice.Pos.le_prev_iff_lt := by
  intro s p q ne
  exact String.Slice.le_posLT_iff (q := p) (p := q.offset) (h := (_root_.String.Slice.Pos.startPos_lt_iff q).mpr ne)

public theorem String.Slice.Pos.prev_lt_iff_le : type_of% @_root_.String.Slice.Pos.prev_lt_iff_le := by
  intro s p q ne
  have reverse := String.Slice.Pos.le_prev_iff_lt (p := q) (q := p) (h := ne)
  exact ⟨fun lt => Nat.le_of_not_gt (fun gt => Nat.not_le_of_gt lt (reverse.mpr gt)),
    fun le => Nat.lt_of_not_ge (fun ge => Nat.not_lt_of_ge le (reverse.mp ge))⟩

public theorem String.Slice.Pos.next_prev : type_of% @_root_.String.Slice.Pos.next_prev := by
  intro s p ne
  exact _root_.String.Slice.Pos.next_eq_iff.mpr
    ⟨_root_.String.Slice.Pos.prev_lt, fun _ lt => String.Slice.Pos.prev_lt_iff_le.mp lt⟩

public theorem String.Slice.Pos.splits_prev_right : type_of% @_root_.String.Slice.Pos.splits_prev_right := by
  intro s p ne
  let prev := p.prev ne
  have step := _root_.String.Slice.Pos.splits_next prev (_root_.String.Slice.Pos.prev_ne_endPos (h := ne))
  rw [_root_.String.Slice.Pos.next_prev (p := p) (h := ne)] at step
  exact step

public theorem String.Pos.prev_lt : type_of% @_root_.String.Pos.prev_lt := by
  intro s p ne
  exact _root_.String.Slice.Pos.prev_lt (p := p.toSlice) (h := fun eq => ne (congrArg String.Pos.ofToSlice eq))

public theorem String.Pos.next_prev._proof_2 : type_of% @_root_.String.Pos.next_prev._proof_2 := by
  intro s p h
  exact _root_.String.Pos.prev_ne_endPos

public theorem String.Pos.next_prev : type_of% @_root_.String.Pos.next_prev := by
  intro s p ne
  exact congrArg String.Pos.ofToSlice (_root_.String.Slice.Pos.next_prev (p := p.toSlice)
    (h := fun eq => ne (congrArg String.Pos.ofToSlice eq)))

public theorem String.Pos.splits_prev_right._proof_1 : type_of% @_root_.String.Pos.splits_prev_right._proof_1 := by
  intro s p ne
  exact _root_.String.Pos.prev_ne_endPos

public theorem String.splits_singleton_right_iff._proof_1 : type_of% @_root_.String.splits_singleton_right_iff._proof_1 := by
  intro s ne
  exact _root_.String.Pos.prev_ne_endPos

public theorem String.Pos.splits_prev_right : type_of% @_root_.String.Pos.splits_prev_right := by
  intro s p ne
  have step := _root_.String.Pos.splits_next (p.prev ne) _root_.String.Pos.prev_ne_endPos
  rw [_root_.String.Pos.next_prev] at step
  exact step

public theorem String.Pos.splits_prev : type_of% @_root_.String.Pos.splits_prev := by
  intro s p ne
  have step := _root_.String.Pos.splits_next_right (p.prev ne) _root_.String.Pos.prev_ne_endPos
  rw [_root_.String.Pos.next_prev] at step
  exact step

public theorem String.Slice.Pos.splits_prev : type_of% @_root_.String.Slice.Pos.splits_prev := by
  intro s p ne
  have step := _root_.String.Slice.Pos.splits_next_right (p.prev ne) _root_.String.Slice.Pos.prev_ne_endPos
  rw [_root_.String.Slice.Pos.next_prev] at step
  exact step

public theorem String.Slice.Pos.Splits.prev : type_of% @_root_.String.Slice.Pos.Splits.prev := by
  intro t c u s p h
  generalize h.ne_startPos_of_singleton = hp
  have both := h.eq (String.Slice.Pos.splits_prev_right p hp)
  have parts := _root_.String.push_inj.mp both.1
  obtain ⟨rfl, rfl⟩ := parts
  rw [both.2]
  exact String.Slice.Pos.splits_prev p _

public theorem String.Pos.Splits.prev : type_of% @_root_.String.Pos.Splits.prev := by
  intro t c u s p h
  generalize h.ne_startPos_of_singleton = hp
  have both := h.eq (String.Pos.splits_prev_right p hp)
  have parts := _root_.String.push_inj.mp both.1
  obtain ⟨rfl, rfl⟩ := parts
  rw [both.2]
  exact String.Pos.splits_prev p _

public theorem String.Slice.Pos.Splits.of_prev : type_of% @_root_.String.Slice.Pos.Splits.of_prev := by
  intro t c u s p hp h
  have both := h.eq (String.Slice.Pos.splits_prev p hp)
  obtain ⟨rfl, rfl⟩ := _root_.String.singleton_append_inj.mp both.2
  rw [both.1]
  exact String.Slice.Pos.splits_prev_right p hp

public theorem String.Pos.Splits.of_prev : type_of% @_root_.String.Pos.Splits.of_prev := by
  intro t c u s p hp h
  have both := h.eq (String.Pos.splits_prev p hp)
  obtain ⟨rfl, rfl⟩ := _root_.String.singleton_append_inj.mp both.2
  rw [both.1]
  exact String.Pos.splits_prev_right p hp

public theorem String.Slice.splits_singleton_right_iff : type_of% @_root_.String.Slice.splits_singleton_right_iff := by
  intro s p c t
  constructor
  · intro split
    have endSplit := s.splits_endPos
    rw [split.eq_append] at endSplit
    have ne := endSplit.ne_startPos_of_singleton
    have previous := String.Slice.Pos.Splits.prev endSplit
    rw [String.append_empty] at previous
    have eqPos := split.pos_eq previous
    have charEq := (previous.eq (_root_.String.Slice.splits_prev_endPos (h := ne))).2
    exact ⟨ne, eqPos, (_root_.String.singleton_inj.mp charEq).symm, split.eq_append⟩
  · rintro ⟨ne, rfl, rfl, eq⟩
    have endSplit := s.splits_endPos
    rw [eq] at endSplit
    have previous := String.Slice.Pos.Splits.prev endSplit
    rw [String.append_empty] at previous
    exact previous

public theorem String.splits_singleton_right_iff : type_of% @_root_.String.splits_singleton_right_iff := by
  intro s p c t
  constructor
  · intro split
    have endSplit : s.endPos.Splits (t ++ String.singleton c) "" :=
      Eq.mp (congrArg (fun t => s.endPos.Splits t "") split.eq_append) s.splits_endPos
    have ne := endSplit.ne_startPos_of_singleton
    have previous := String.Pos.Splits.prev endSplit
    rw [String.append_empty] at previous
    have eqPos := split.pos_eq previous
    have charEq := (previous.eq (_root_.String.splits_prev_endPos (h := ne))).2
    exact ⟨ne, eqPos, (_root_.String.singleton_inj.mp charEq).symm, split.eq_append⟩
  · rintro ⟨ne, rfl, rfl, eq⟩
    have endSplit : s.endPos.Splits (t ++ String.singleton ((s.endPos.prev ne).get _root_.String.Pos.prev_ne_endPos)) "" :=
      Eq.mp (congrArg (fun t => s.endPos.Splits t "") eq) s.splits_endPos
    have previous := String.Pos.Splits.prev endSplit
    rw [String.append_empty] at previous
    exact previous

public theorem String.Slice.front?_eq : type_of% @_root_.String.Slice.front?_eq := by
  intro s
  by_cases ends : s.startPos = s.endPos
  · have empty := _root_.String.Slice.copy_eq_empty_iff.mpr (_root_.String.Slice.startPos_eq_endPos_iff.mp ends)
    rw [empty, String.toList_empty]
    exact _root_.String.Slice.Pos.get?_eq_none ends
  · obtain ⟨rest, eq⟩ := s.splits_startPos.exists_eq_singleton_append ends
    rw [eq, String.toList_append, String.toList_singleton]
    exact _root_.String.Slice.Pos.get?_eq_some_get ends

public theorem String.Slice.back?_eq : type_of% @_root_.String.Slice.back?_eq := by
  intro s
  rw [_root_.String.Slice.back?_eq_get?]
  by_cases ends : s.endPos = s.startPos
  · have empty := _root_.String.Slice.copy_eq_empty_iff.mpr (_root_.String.Slice.startPos_eq_endPos_iff.mp ends.symm)
    rw [_root_.String.Slice.Pos.prev?_eq_none ends, empty, String.toList_empty]
    rfl
  · obtain ⟨pre, eq⟩ := s.splits_endPos.exists_eq_append_singleton_of_ne_startPos ends
    rw [_root_.String.Slice.Pos.prev?_eq_some_prev ends, eq, String.toList_append, String.toList_singleton, List.getLast?_concat]
    exact _root_.String.Slice.Pos.get?_eq_some_get _root_.String.Slice.Pos.prev_ne_endPos

public theorem String.Slice.Pos.Splits.lt_iff_exists_eq_append :
    type_of% @_root_.String.Slice.Pos.Splits.lt_iff_exists_eq_append := by
  intro s p q a b c d hp hq
  constructor
  · intro lt
    obtain ⟨mid, left, right⟩ := (hp.le_iff_exists_eq_append hq).mp (Nat.le_of_lt lt)
    refine ⟨mid, fun empty => ?_, left, right⟩
    have eq : c = a := left.trans ((congrArg (a ++ ·) empty).trans String.append_empty)
    exact Nat.ne_of_lt lt (congrArg String.Pos.Raw.byteIdx
      (hp.offset_eq_rawEndPos.trans ((congrArg String.rawEndPos eq.symm).trans hq.offset_eq_rawEndPos.symm)))
  · rintro ⟨mid, nonempty, left, right⟩
    refine Nat.lt_of_le_of_ne ((hp.le_iff_exists_eq_append hq).mpr ⟨mid, left, right⟩) (fun same => ?_)
    have posEq : p = q := String.Slice.Pos.ext (String.Pos.Raw.ext same)
    have ac := hp.eq_left (posEq ▸ hq)
    exact nonempty (String.append_eq_left_iff.mp (left.symm.trans ac.symm))

namespace String.Slice.Pattern.Model

private theorem position_eq {s : String.Slice} {p q : s.Pos} (pq : p ≤ q) (qp : q ≤ p) : p = q :=
  String.Slice.Pos.ext (String.Pos.Raw.ext (Nat.le_antisymm pq qp))

public theorem IsLongestMatch.le_of_isMatch : type_of% @_root_.String.Slice.Pattern.Model.IsLongestMatch.le_of_isMatch :=
  fun h match' => Nat.le_of_not_gt (fun lt => h.not_isMatch _ lt match')

public theorem IsLongestRevMatch.le_of_isRevMatch : type_of% @_root_.String.Slice.Pattern.Model.IsLongestRevMatch.le_of_isRevMatch :=
  fun h match' => Nat.le_of_not_gt (fun lt => h.not_isRevMatch _ lt match')

public theorem IsLongestMatch.eq : type_of% @_root_.String.Slice.Pattern.Model.IsLongestMatch.eq :=
  fun hp hq => position_eq (IsLongestMatch.le_of_isMatch hq hp.isMatch) (IsLongestMatch.le_of_isMatch hp hq.isMatch)

public theorem IsLongestRevMatch.eq : type_of% @_root_.String.Slice.Pattern.Model.IsLongestRevMatch.eq :=
  fun hp hq => position_eq (IsLongestRevMatch.le_of_isRevMatch hp hq.isRevMatch) (IsLongestRevMatch.le_of_isRevMatch hq hp.isRevMatch)

public theorem isLongestMatch_cast_iff : type_of% @_root_.String.Slice.Pattern.Model.isLongestMatch_cast_iff := by
  intro ρ pat i s t eq p
  constructor
  · intro h
    exact ⟨(_root_.String.Slice.Pattern.Model.isMatch_cast_iff eq).mp h.isMatch,
      fun q lt hq => h.not_isMatch (q.cast eq) lt ((_root_.String.Slice.Pattern.Model.isMatch_cast_iff eq).mpr hq)⟩
  · intro h
    exact ⟨(_root_.String.Slice.Pattern.Model.isMatch_cast_iff eq).mpr h.isMatch,
      fun q lt hq => h.not_isMatch (q.cast eq.symm) lt ((_root_.String.Slice.Pattern.Model.isMatch_cast_iff eq.symm).mpr hq)⟩

public theorem isLongestRevMatch_cast_iff : type_of% @_root_.String.Slice.Pattern.Model.isLongestRevMatch_cast_iff := by
  intro ρ pat i s t eq p
  constructor
  · intro h
    exact ⟨(_root_.String.Slice.Pattern.Model.isRevMatch_cast_iff eq).mp h.isRevMatch,
      fun q lt hq => h.not_isRevMatch (q.cast eq) lt ((_root_.String.Slice.Pattern.Model.isRevMatch_cast_iff eq).mpr hq)⟩
  · intro h
    exact ⟨(_root_.String.Slice.Pattern.Model.isRevMatch_cast_iff eq).mpr h.isRevMatch,
      fun q lt hq => h.not_isRevMatch (q.cast eq.symm) lt ((_root_.String.Slice.Pattern.Model.isRevMatch_cast_iff eq.symm).mpr hq)⟩

public theorem IsLongestMatchAtChain.le : type_of% @_root_.String.Slice.Pattern.Model.IsLongestMatchAtChain.le := by
  intro ρ pat i s start stop chain
  induction chain with
  | nil => exact Nat.le_refl _
  | cons _ _ _ first _ tail => exact Nat.le_trans first.le tail

public theorem IsLongestRevMatchAtChain.le : type_of% @_root_.String.Slice.Pattern.Model.IsLongestRevMatchAtChain.le := by
  intro ρ pat i s start stop chain
  induction chain with
  | nil => exact Nat.le_refl _
  | cons _ _ _ last head => exact Nat.le_trans head last.le

public theorem IsLongestMatchAt.eq : type_of% @_root_.String.Slice.Pattern.Model.IsLongestMatchAt.eq := by
  intro ρ pat i s start x y hx hy
  exact _root_.String.Slice.Pos.sliceFrom_inj.mp
    (IsLongestMatch.eq hx.isLongestMatch_sliceFrom hy.isLongestMatch_sliceFrom)

public theorem IsLongestRevMatchAt.eq : type_of% @_root_.String.Slice.Pattern.Model.IsLongestRevMatchAt.eq := by
  intro ρ pat i s x y stop hx hy
  exact _root_.String.Slice.Pos.sliceTo_inj.mp
    (IsLongestRevMatch.eq hx.isLongestRevMatch_sliceTo hy.isLongestRevMatch_sliceTo)

public theorem isLongestMatchAt_cast_iff : type_of% @_root_.String.Slice.Pattern.Model.isLongestMatchAt_cast_iff := by
  intro ρ pat i s t eq start stop
  constructor
  · intro h
    have inner := h.isLongestMatch_sliceFrom
    rw [_root_.String.Slice.Pos.sliceFrom_cast] at inner
    exact ⟨h.le, (isLongestMatch_cast_iff _).mp inner⟩
  · intro h
    refine ⟨(_root_.String.Slice.Pos.cast_le_cast_iff).mpr h.le, ?_⟩
    rw [_root_.String.Slice.Pos.sliceFrom_cast (hst := eq) start stop]
    exact (isLongestMatch_cast_iff _).mpr h.isLongestMatch_sliceFrom

public theorem isLongestRevMatchAt_cast_iff : type_of% @_root_.String.Slice.Pattern.Model.isLongestRevMatchAt_cast_iff := by
  intro ρ pat i s t eq start stop
  constructor
  · intro h
    have inner := h.isLongestRevMatch_sliceTo
    rw [_root_.String.Slice.Pos.sliceTo_cast] at inner
    exact ⟨h.le, (isLongestRevMatch_cast_iff _).mp inner⟩
  · intro h
    refine ⟨(_root_.String.Slice.Pos.cast_le_cast_iff).mpr h.le, ?_⟩
    rw [_root_.String.Slice.Pos.sliceTo_cast (hst := eq) stop start]
    exact (isLongestRevMatch_cast_iff _).mpr h.isLongestRevMatch_sliceTo

public theorem matchesAt_cast_iff : type_of% @_root_.String.Slice.Pattern.Model.matchesAt_cast_iff := by
  intro ρ pat i s t eq p
  constructor
  · rintro ⟨⟨q, matched⟩⟩
    exact ⟨⟨q.cast eq.symm, (isLongestMatchAt_cast_iff eq).mp matched⟩⟩
  · rintro ⟨⟨q, matched⟩⟩
    exact ⟨⟨q.cast eq, (isLongestMatchAt_cast_iff eq).mpr matched⟩⟩

public theorem revMatchesAt_cast_iff : type_of% @_root_.String.Slice.Pattern.Model.revMatchesAt_cast_iff := by
  intro ρ pat i s t eq p
  constructor
  · rintro ⟨⟨q, matched⟩⟩
    exact ⟨⟨q.cast eq.symm, (isLongestRevMatchAt_cast_iff eq).mp matched⟩⟩
  · rintro ⟨⟨q, matched⟩⟩
    exact ⟨⟨q.cast eq, (isLongestRevMatchAt_cast_iff eq).mpr matched⟩⟩

private theorem miss_iff {α : Type} {out : Option α} {matchExists : Prop}
    (sound : ∀ p, out = some p → matchExists) (complete : matchExists → ∃ p, out = some p) :
    out = none ↔ ¬matchExists :=
  ⟨fun empty matched => (complete matched).elim (fun _ found => nomatch empty.symm.trans found),
    fun miss => by cases eq : out with
    | none => rfl
    | some p => exact (miss (sound p eq)).elim⟩

public theorem not_matchesAt_endPos : type_of% @_root_.String.Slice.Pattern.Model.not_matchesAt_endPos := by
  rintro ρ pat i strict s ⟨p, matched⟩
  exact Nat.not_lt_of_ge p.isValidForSlice.le_utf8ByteSize matched.lt

public theorem not_revMatchesAt_startPos : type_of% @_root_.String.Slice.Pattern.Model.not_revMatchesAt_startPos := by
  rintro ρ pat i strict s ⟨p, matched⟩
  exact Nat.not_lt_zero p.offset.byteIdx matched.lt

public theorem LawfulForwardPatternModel.skipPrefix?_sliceFrom_eq_none_iff :
    type_of% @_root_.String.Slice.Pattern.Model.LawfulForwardPatternModel.skipPrefix?_sliceFrom_eq_none_iff := by
  intro ρ pat inst model law s start
  apply miss_iff
  · intro p found
    have matched := (_root_.String.Slice.Pattern.Model.LawfulForwardPatternModel.skipPrefix?_eq_some_iff p).mp found
    exact ⟨⟨_, matched.isLongestMatchAt_ofSliceFrom⟩⟩
  · rintro ⟨⟨p, matched⟩⟩
    exact ⟨_, (_root_.String.Slice.Pattern.Model.LawfulForwardPatternModel.skipPrefix?_eq_some_iff _).mpr
      matched.isLongestMatch_sliceFrom⟩

public theorem LawfulBackwardPatternModel.skipSuffix?_sliceTo_eq_none_iff :
    type_of% @_root_.String.Slice.Pattern.Model.LawfulBackwardPatternModel.skipSuffix?_sliceTo_eq_none_iff := by
  intro ρ pat inst model law s stop
  apply miss_iff
  · intro p found
    have matched := (_root_.String.Slice.Pattern.Model.LawfulBackwardPatternModel.skipSuffix?_eq_some_iff p).mp found
    exact ⟨⟨_, matched.isLongestRevMatchAt_ofSliceTo⟩⟩
  · rintro ⟨⟨p, matched⟩⟩
    exact ⟨_, (_root_.String.Slice.Pattern.Model.LawfulBackwardPatternModel.skipSuffix?_eq_some_iff _).mpr
      matched.isLongestRevMatch_sliceTo⟩

public theorem LawfulForwardPatternModel.skipPrefix?_eq_none_iff :
    type_of% @_root_.String.Slice.Pattern.Model.LawfulForwardPatternModel.skipPrefix?_eq_none_iff := by
  intro ρ pat inst model law s
  apply miss_iff
  · intro p found
    have matched := (_root_.String.Slice.Pattern.Model.LawfulForwardPatternModel.skipPrefix?_eq_some_iff p).mp found
    exact ⟨⟨p, _root_.String.Slice.Pattern.Model.isLongestMatchAt_startPos_iff.mpr matched⟩⟩
  · rintro ⟨⟨p, matched⟩⟩
    exact ⟨p, (_root_.String.Slice.Pattern.Model.LawfulForwardPatternModel.skipPrefix?_eq_some_iff p).mpr
      (_root_.String.Slice.Pattern.Model.isLongestMatchAt_startPos_iff.mp matched)⟩

public theorem LawfulBackwardPatternModel.skipSuffix?_eq_none_iff :
    type_of% @_root_.String.Slice.Pattern.Model.LawfulBackwardPatternModel.skipSuffix?_eq_none_iff := by
  intro ρ pat inst model law s
  apply miss_iff
  · intro p found
    have matched := (_root_.String.Slice.Pattern.Model.LawfulBackwardPatternModel.skipSuffix?_eq_some_iff p).mp found
    exact ⟨⟨p, _root_.String.Slice.Pattern.Model.isLongestRevMatchAt_endPos_iff.mpr matched⟩⟩
  · rintro ⟨⟨p, matched⟩⟩
    exact ⟨p, (_root_.String.Slice.Pattern.Model.LawfulBackwardPatternModel.skipSuffix?_eq_some_iff p).mpr
      (_root_.String.Slice.Pattern.Model.isLongestRevMatchAt_endPos_iff.mp matched)⟩

private theorem returnSteps {s t : String.Slice} (eq : s.copy = t.copy) (steps : List (String.Slice.Pattern.SearchStep t)) :
    (steps.map (·.cast eq.symm)).map (·.cast eq) = steps := by
  induction steps with
  | nil => rfl
  | cons step tail ih =>
    cases step <;> exact congrArg (List.cons _) ih

public theorem isValidSearchFrom_cast_iff : type_of% @_root_.String.Slice.Pattern.Model.isValidSearchFrom_cast_iff := by
  intro ρ pat i s t eq p steps
  have transport {s t : String.Slice} (eq : s.copy = t.copy) {p : s.Pos} {xs}
      (h : _root_.String.Slice.Pattern.Model.IsValidSearchFrom pat p xs) :
      _root_.String.Slice.Pattern.Model.IsValidSearchFrom pat (p.cast eq) (xs.map (·.cast eq)) := by
    induction h with
    | endPos =>
      rw [_root_.String.Slice.Pos.cast_endPos]
      exact .endPos
    | matched matched _ ih => exact .matched ((isLongestMatchAt_cast_iff eq).mpr matched) ih
    | mismatched lt misses _ ih =>
      exact .mismatched lt (fun q lower upper found =>
        misses (q.cast eq.symm) lower upper ((matchesAt_cast_iff eq.symm).mpr found)) ih
  exact ⟨fun h => transport eq.symm h, fun h => returnSteps eq steps ▸ transport eq h⟩

public theorem isValidRevSearchFrom_cast_iff : type_of% @_root_.String.Slice.Pattern.Model.isValidRevSearchFrom_cast_iff := by
  intro ρ pat i s t eq p steps
  have transport {s t : String.Slice} (eq : s.copy = t.copy) {p : s.Pos} {xs}
      (h : _root_.String.Slice.Pattern.Model.IsValidRevSearchFrom pat p xs) :
      _root_.String.Slice.Pattern.Model.IsValidRevSearchFrom pat (p.cast eq) (xs.map (·.cast eq)) := by
    induction h with
    | startPos =>
      rw [_root_.String.Slice.Pos.cast_startPos]
      exact .startPos
    | matched matched _ ih => exact .matched ((isLongestRevMatchAt_cast_iff eq).mpr matched) ih
    | mismatched lt misses _ ih =>
      exact .mismatched lt (fun q lower upper found =>
        misses (q.cast eq.symm) lower upper ((revMatchesAt_cast_iff eq.symm).mpr found)) ih
  exact ⟨fun h => transport eq.symm h, fun h => returnSteps eq steps ▸ transport eq h⟩

end String.Slice.Pattern.Model

public theorem String.Slice.eqIgnoreAsciiCase.go._unary._proof_3 :
    type_of% (private_decl% @_root_.String.Slice.eqIgnoreAsciiCase.go._unary._proof_3) := by
  intro s t p q bound
  exact Nat.sub_lt_sub_left bound.1 (Nat.lt_succ_self _)

@[expose] public def String.Slice.Pattern.instBEqSearchStep.beq :
    type_of% @_root_.String.Slice.Pattern.instBEqSearchStep.beq := fun {s} a b =>
  let same (p q r t : s.Pos) :=
    (p.offset.byteIdx == r.offset.byteIdx) && (q.offset.byteIdx == t.offset.byteIdx)
  _root_.String.Slice.Pattern.SearchStep.casesOn a
    (fun p q => _root_.String.Slice.Pattern.SearchStep.casesOn b (same p q) (fun _ _ => false))
    (fun p q => _root_.String.Slice.Pattern.SearchStep.casesOn b (fun _ _ => false) (same p q))

public theorem String.Slice.Pattern.ToBackwardSearcher.DefaultBackwardSearcher.finitenessRelation._proof_2 :
    type_of% (private_decl% @_root_.String.Slice.Pattern.ToBackwardSearcher.DefaultBackwardSearcher.finitenessRelation._proof_2) := by
  intro ρ pat s _ _ it it' step
  simp_wf
  obtain ⟨step, eq, valid⟩ := step
  match step with
  | .yield next (.rejected p q) =>
    obtain ⟨_, ⟨_, _, _, advance⟩⟩ := valid
    cases eq
    rw [advance]
    exact _root_.String.Slice.Pos.prev_lt
  | .yield next (.matched p q) =>
    obtain ⟨_, pos, ⟨found, _, _, advance⟩⟩ := valid
    cases eq
    rw [advance]
    have lt := (_root_.String.Slice.Pos.lt_endPos_iff _).mpr
      (_root_.String.Slice.Pattern.StrictBackwardPattern.ne_endPos _ _ found)
    exact Nat.lt_of_lt_of_le lt (Nat.le_of_eq _root_.String.Slice.utf8ByteSize_sliceTo)

@[expose] public def String.Slice.foldl (f : α → Char → α) (init : α) (s : String.Slice) : α :=
  s.copy.toList.foldl f init

@[expose] public def String.Slice.foldr (f : Char → α → α) (init : α) (s : String.Slice) : α :=
  s.copy.toList.foldr f init

public theorem _root_.OmegaChecks.InitPort.AlternativeEquations.String.Slice.foldl.eq_1
    (f : α → Char → α) (init : α) (s : _root_.String.Slice) :
    String.Slice.foldl f init s = s.chars.fold f init := by
  rw [← _root_.Std.Iter.foldl_toList, _root_.String.Slice.toList_chars]
  rfl

public theorem _root_.OmegaChecks.InitPort.AlternativeEquations.String.Slice.foldr.eq_1
    (f : Char → α → α) (init : α) (s : _root_.String.Slice) :
    String.Slice.foldr f init s = s.revChars.fold (flip f) init := by
  rw [← _root_.Std.Iter.foldl_toList, _root_.String.Slice.toList_revChars, _root_.List.foldl_reverse]
  rfl

@[expose] public def String.Slice.isNat (s : String.Slice) : Bool := Id.run do
  let mut lastWasDigit := false
  for c in s.copy.toList do
    if c = '_' then
      if !lastWasDigit then return false
      lastWasDigit := false
    else if c.isDigit then
      lastWasDigit := true
    else
      return false
  return lastWasDigit

@[expose] public def String.Internal.posOfImpl (s : String) (c : Char) : String.Pos.Raw :=
  (String.ofList (s.toList.takeWhile (· != c))).rawEndPos

@[expose] public def String.Internal.containsImpl (s : String) (c : Char) : Bool :=
  decide (c ∈ s.toList)

@[expose] public def String.Internal.anyImpl (s : String) (p : Char → Bool) : Bool :=
  s.toList.any p

@[expose] public def Substring.Raw.posOf (s : Substring.Raw) (c : Char) : String.Pos.Raw :=
  (s.toSlice?.map fun t => (String.ofList (t.copy.toList.takeWhile (· != c))).rawEndPos).getD ⟨s.bsize⟩

@[expose] public def Substring.Raw.any (s : Substring.Raw) (p : Char → Bool) : Bool :=
  s.toSlice?.get!.copy.toList.any p

end OmegaChecks.InitPort.Alternatives

namespace OmegaChecks.InitPort.Alternatives

/- Open at the public types of the character and predicate search laws. The pinned
statements pass a default search loop to `contains`, `find?` or `revFind?` at the
concrete pattern. The strict statements pass a loop using termination of that
pattern. A normal official import seals both string implementation wrappers
used below and the extrinsic fixpoint used by the default loop. -/
public theorem String.contains_char_eq_contains_beq {c : Char} {s : String} :
    String.Internal.containsImpl s c = String.Internal.anyImpl s (fun x => x == c) := by
  change decide (c ∈ s.toList) = s.toList.any (fun x => x == c)
  apply Bool.eq_iff_iff.mpr
  apply decide_eq_true_iff.trans
  refine (Iff.intro ?_ ?_).trans List.any_eq_true.symm
  · intro h
    exact ⟨c, h, decide_eq_true (Eq.refl c)⟩
  · rintro ⟨x, hx, eq⟩
    exact (of_decide_eq_true eq : x = c) ▸ hx

public theorem String.contains_prop_eq_contains_decide {p : Char → Prop} [DecidablePred p] {s : String} :
    String.Internal.anyImpl s p = String.Internal.anyImpl s (fun c => decide (p c)) := rfl

end OmegaChecks.InitPort.Alternatives
