module
import all Init.Data.String.Basic
import all Init.Data.String.Lemmas.Slice
import all Init.Data.String.Lemmas.Pattern.Basic
import all Init.Data.ByteArray.Lemmas
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Slice

/-! Byte comparison and matching in a string slice. -/

namespace OmegaChecks.InitPort.Alternatives

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

end String.Slice.Pattern.Model

end OmegaChecks.InitPort.Alternatives
