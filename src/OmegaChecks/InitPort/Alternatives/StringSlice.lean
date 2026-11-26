module
import all Init.Data.String.Basic
import all Init.Data.String.Slice
import all Init.Data.String.FindPos
import all Init.Data.String.Lemmas.IsEmpty
import all Init.Data.String.Lemmas.Order
import all Init.Data.String.Lemmas.FindPos
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Defs
public import OmegaChecks.InitPort.Alternatives.StringPattern.Encoding
public import OmegaChecks.InitPort.Alternatives.StringPattern
public import OmegaChecks.InitPort.Alternatives.StringPattern.TakeDrop
public import OmegaChecks.InitPort.Alternatives.StringSearch
public import OmegaChecks.InitPort.Alternatives.StringTransforms

/-! Byte bounds for positions relative to a string slice. -/

namespace OmegaChecks.InitPort.Alternatives

public theorem String.Slice.Pos.offset_str_le_offset_endExclusive :
    type_of% @_root_.String.Slice.Pos.offset_str_le_offset_endExclusive := by
  intro s pos
  have bound := Nat.add_le_add_left pos.isValidForSlice.le_utf8ByteSize s.startInclusive.offset.byteIdx
  exact Nat.le_trans bound (Nat.le_of_eq (Nat.add_sub_of_le s.startInclusive_le_endExclusive))

public theorem String.Slice.getUTF8Byte._proof_3 :
    type_of% @_root_.String.Slice.getUTF8Byte._proof_3 := by
  intro s p h
  have bound := Nat.add_lt_add_left (show p.byteIdx < s.utf8ByteSize from h) s.startInclusive.offset.byteIdx
  exact Nat.lt_of_lt_of_le bound (Nat.le_trans (Nat.le_of_eq (Nat.add_sub_of_le s.startInclusive_le_endExclusive))
    s.endExclusive.isValid.le_utf8ByteSize)

public theorem String.Slice.Pos.byte._proof_4 :
    type_of% @_root_.String.Slice.Pos.byte._proof_4 := by
  intro s pos ne
  exact Nat.lt_of_le_of_ne pos.isValidForSlice.le_utf8ByteSize
    (fun eq => ne (String.Slice.Pos.ext (String.Pos.Raw.ext eq)))

public theorem String.Slice.Pos.prev._proof_3 :
    type_of% @_root_.String.Slice.Pos.prev._proof_3 := by
  intro s pos ne
  exact Nat.pos_of_ne_zero (fun eq => ne (String.Slice.Pos.ext (String.Pos.Raw.ext eq)))

public theorem String.Slice.Pos.ne_endPos_of_lt :
    type_of% @_root_.String.Slice.Pos.ne_endPos_of_lt := by
  intro s p q lt eq
  cases eq
  exact Nat.not_lt_of_ge q.isValidForSlice.le_utf8ByteSize lt

public theorem String.Slice.startPos_ne_endPos_iff :
    type_of% @_root_.String.Slice.startPos_ne_endPos_iff := by
  intro s
  constructor
  · intro ne
    change (s.utf8ByteSize == 0) = false
    cases h : s.utf8ByteSize with
    | zero => exact (ne (String.Slice.Pos.ext (String.Pos.Raw.ext h.symm))).elim
    | succ n => rfl
  · intro h eq
    have size : s.utf8ByteSize = 0 := congrArg (fun p : s.Pos => p.offset.byteIdx) eq.symm
    change (s.utf8ByteSize == 0) = false at h
    rw [size] at h
    cases h

public theorem String.Slice.Pos.get._proof_2 :
    type_of% @_root_.String.Slice.Pos.get._proof_2 := by
  intro s pos ne atEnd
  exact (ne (String.Slice.Pos.ext atEnd)).elim

public theorem String.Slice.Pos.prevAux._proof_3 :
    type_of% @_root_.String.Slice.Pos.prevAux._proof_3 := by
  intro s off h₁ notFirst eq
  subst off
  exact notFirst String.Slice.isUTF8FirstByte_utf8ByteAt_zero

public theorem String.Slice.Pos.lt_endPos_iff :
    type_of% @_root_.String.Slice.Pos.lt_endPos_iff := by
  intro s p
  exact ⟨fun lt eq => Nat.ne_of_lt lt (congrArg (fun p : s.Pos => p.offset.byteIdx) eq),
    String.Slice.Pos.byte._proof_4 p⟩

public theorem String.Slice.Pos.offset_lt_rawEndPos_iff :
    type_of% @_root_.String.Slice.Pos.offset_lt_rawEndPos_iff := by
  intro s p
  exact String.Slice.Pos.lt_endPos_iff p

public theorem String.Slice.Pos.wellFounded_lt :
    type_of% @_root_.String.Slice.Pos.wellFounded_lt := by
  intro s
  exact InvImage.wf (fun p : s.Pos => p.offset.byteIdx) Nat.lt_wfRel.wf

public theorem String.Slice.Pos.wellFounded_gt :
    type_of% @_root_.String.Slice.Pos.wellFounded_gt := by
  intro s
  apply Subrelation.wf (r := InvImage Nat.lt (fun p : s.Pos => s.utf8ByteSize - p.offset.byteIdx))
  · intro p q h
    exact Nat.sub_lt_sub_left (Nat.lt_of_lt_of_le h p.isValidForSlice.le_utf8ByteSize) h
  · exact InvImage.wf _ Nat.lt_wfRel.wf

public theorem String.Pos.Raw.isValidForSlice_iff_isUTF8FirstByte :
    type_of% @_root_.String.Pos.Raw.isValidForSlice_iff_isUTF8FirstByte := by
  intro s p
  constructor
  · intro h
    by_cases atEnd : p = s.rawEndPos
    · exact Or.inl atEnd
    · have lt := Nat.lt_of_le_of_ne h.le_utf8ByteSize (fun eq => atEnd (String.Pos.Raw.ext eq))
      have strLt := String.Slice.getUTF8Byte._proof_3 s p lt
      obtain eq | ⟨_, first⟩ := _root_.String.Pos.Raw.isValid_iff_isUTF8FirstByte.mp h.isValid_offsetBy
      · exact (Nat.ne_of_lt strLt (congrArg String.Pos.Raw.byteIdx eq)).elim
      · exact Or.inr ⟨lt, first⟩
  · rintro (rfl | ⟨lt, first⟩)
    · exact s.endPos.isValidForSlice
    · exact ⟨Nat.le_of_lt lt, _root_.String.Pos.Raw.isValid_iff_isUTF8FirstByte.mpr
        (Or.inr ⟨String.Slice.getUTF8Byte._proof_3 s p lt, first⟩)⟩

public theorem String.Pos.Raw.isValidForSlice_iff_isSome_utf8DecodeChar? :
    type_of% @_root_.String.Pos.Raw.isValidForSlice_iff_isSome_utf8DecodeChar? := by
  intro s p
  constructor
  · intro h
    by_cases atEnd : p = s.rawEndPos
    · exact Or.inl atEnd
    · have lt := Nat.lt_of_le_of_ne h.le_utf8ByteSize (fun eq => atEnd (String.Pos.Raw.ext eq))
      have strLt := String.Slice.getUTF8Byte._proof_3 s p lt
      obtain eq | decodes := _root_.String.Pos.Raw.isValid_iff_isSome_utf8DecodeChar?.mp h.isValid_offsetBy
      · exact (Nat.ne_of_lt strLt (congrArg String.Pos.Raw.byteIdx eq)).elim
      · exact Or.inr ⟨lt, decodes⟩
  · rintro (rfl | ⟨lt, decodes⟩)
    · exact s.endPos.isValidForSlice
    · exact ⟨Nat.le_of_lt lt, _root_.String.Pos.Raw.isValid_iff_isSome_utf8DecodeChar?.mpr (Or.inr decodes)⟩

public theorem String.Slice.utf8ByteSize_slice :
    type_of% @_root_.String.Slice.utf8ByteSize_slice := by
  intro s p q h
  exact Nat.add_sub_add_left _ _ _

public theorem String.Pos.Raw.isValidForSlice_slice :
    type_of% @_root_.String.Pos.Raw.isValidForSlice_slice := by
  intro s p q ordered off
  constructor
  · intro valid
    have bound := valid.le_utf8ByteSize
    rw [String.Slice.utf8ByteSize_slice] at bound
    have relative := Nat.add_le_of_le_sub (show p.offset.byteIdx ≤ q.offset.byteIdx from ordered) bound
    rw [Nat.add_comm] at relative
    refine ⟨relative, Nat.le_trans relative q.isValidForSlice.le_utf8ByteSize, ?_⟩
    rw [String.Pos.Raw.offsetBy_assoc]
    exact valid.isValid_offsetBy
  · rintro ⟨bounded, valid⟩
    constructor
    · change off.byteIdx ≤ (s.slice p q ordered).utf8ByteSize
      rw [String.Slice.utf8ByteSize_slice]
      exact Nat.le_sub_of_add_le' bounded
    · exact String.Pos.Raw.offsetBy_assoc ▸ valid.isValid_offsetBy

public theorem String.Slice.Pos.prevAux._proof_6 :
    type_of% @_root_.String.Slice.Pos.prevAux._proof_6 := by
  intro s i h
  exact Nat.lt_trans (Nat.lt_succ_self i) h

public theorem String.Slice.Pos.prevAux._proof_8 :
    type_of% @_root_.String.Slice.Pos.prevAux._proof_8 := by
  intro s p ne
  have pos : 0 < p.offset.byteIdx := Nat.pos_of_ne_zero
    (fun eq => ne (String.Slice.Pos.ext (String.Pos.Raw.ext eq)))
  exact Nat.lt_of_lt_of_le (Nat.sub_lt pos (by decide)) p.isValidForSlice.le_utf8ByteSize

private theorem boundaryCheck {P : Prop} (dec : Decidable P) {pos endOff : String.Pos.Raw}
    (h : pos < endOff) : decide P = true ↔ pos = endOff ∨ ∃ _ : pos < endOff, P := by
  constructor
  · intro ok
    exact Or.inr ⟨h, of_decide_eq_true ok⟩
  · rintro (eq | ⟨_, valid⟩)
    · exact (Nat.ne_of_lt h (congrArg String.Pos.Raw.byteIdx eq)).elim
    · exact decide_eq_true valid

private theorem outsideCheck {pos endOff : String.Pos.Raw} {P : pos < endOff → Prop} (h : ¬ pos < endOff) :
    decide (pos = endOff) = true ↔ pos = endOff ∨ ∃ lt : pos < endOff, P lt := by
  exact ⟨fun ok => .inl (of_decide_eq_true ok),
    fun valid => valid.elim (fun eq => decide_eq_true eq) (fun ⟨lt, _⟩ => (h lt).elim)⟩

public theorem String.Pos.Raw.isValid_eq_true_iff : type_of% @_root_.String.Pos.Raw.isValid_eq_true_iff := by
  intro s p
  apply Iff.trans _ _root_.String.Pos.Raw.isValid_iff_isUTF8FirstByte.symm
  unfold _root_.String.Pos.Raw.isValid
  split <;> rename_i h
  · exact boundaryCheck _ h
  · exact outsideCheck h

public theorem String.Pos.Raw.isValidForSlice_eq_true_iff :
    type_of% @_root_.String.Pos.Raw.isValidForSlice_eq_true_iff := by
  intro s p
  apply Iff.trans _ _root_.String.Pos.Raw.isValidForSlice_iff_isUTF8FirstByte.symm
  unfold _root_.String.Pos.Raw.isValidForSlice
  split <;> rename_i h
  · exact boundaryCheck _ h
  · exact outsideCheck h

public theorem String.Slice.Pos.isUTF8FirstByte_byte :
    type_of% @_root_.String.Slice.Pos.isUTF8FirstByte_byte := by
  intro s pos ne
  obtain atEnd | ⟨_, first⟩ := String.Pos.Raw.isValidForSlice_iff_isUTF8FirstByte.mp pos.isValidForSlice
  · exact (ne (String.Slice.Pos.ext atEnd)).elim
  · exact first

public theorem String.Slice.posLE._proof_1 : type_of% @_root_.String.Slice.posLE._proof_1 := by
  rintro s off invalid rfl
  exact invalid s.startPos.isValidForSlice

public theorem String.Slice.posLE._proof_2 : type_of% @_root_.String.Slice.posLE._proof_2 := by
  intro off ne
  exact Nat.sub_lt (Nat.pos_of_ne_zero (fun eq => ne (String.Pos.Raw.ext eq))) (by decide)

public theorem String.Slice.offset_posLE_le : type_of% @_root_.String.Slice.offset_posLE_le := by
  intro s p
  obtain ⟨i⟩ := p
  induction i with
  | zero =>
    rw [String.Slice.posLE.eq_def]
    split
    · exact Nat.le_refl _
    · rename_i invalid
      exact (invalid s.startPos.isValidForSlice).elim
  | succ n ih =>
    rw [String.Slice.posLE.eq_def]
    split
    · exact Nat.le_refl _
    · exact Nat.le_trans ih (Nat.le_succ n)

public theorem String.Slice.Pos.prev_lt : type_of% @_root_.String.Slice.Pos.prev_lt := by
  intro s p ne
  have bound := String.Slice.offset_posLE_le (s := s) (p := p.offset.dec)
  have pos : 0 < p.offset.byteIdx := Nat.pos_of_ne_zero (fun eq => ne (String.Slice.Pos.ext (String.Pos.Raw.ext eq)))
  exact Nat.lt_of_le_of_lt bound (Nat.sub_lt pos (by decide))

public theorem String.Slice.Pattern.CharPred.instBackwardPatternForallCharBool._proof_3 :
    type_of% @_root_.String.Slice.Pattern.CharPred.instBackwardPatternForallCharBool._proof_3 := by
  intro s ne eq
  have lt := String.Slice.Pos.prev_lt (p := s.endPos) (h := (String.Slice.startPos_ne_endPos ne).symm)
  exact Nat.ne_of_lt lt (congrArg (fun p : s.Pos => p.offset.byteIdx) eq)

public theorem String.Slice.Pos.next._proof_1 : type_of% @_root_.String.Slice.Pos.next._proof_1 := by
  intro s pos h
  obtain ⟨t₁, t₂, ht, offset⟩ := String.Slice.Pos.copy_eq_append_get h
  apply String.Pos.Raw.isValid_copy_iff.mp
  rw [String.Slice.Pos.utf8ByteSize_byte, ht, ← String.Pos.Raw.ext offset]
  apply String.Pos.Raw.IsValid.append_right _ t₂
  rw [String.Pos.Raw.increaseBy_charUtf8Size]
  apply String.Pos.Raw.IsValid.append_left _ t₁
  exact String.Pos.Raw.isValid_singleton.mpr (Or.inr rfl)

public theorem String.Pos.Raw.isValid_copy_iff : type_of% @_root_.String.Pos.Raw.isValid_copy_iff := by
  intro s p
  apply String.Pos.Raw.isValid_iff_isUTF8FirstByte.trans
  apply Iff.trans _ String.Pos.Raw.isValidForSlice_iff_isUTF8FirstByte.symm
  constructor
  · rintro (eq | ⟨lt, first⟩)
    · exact Or.inl (eq.trans String.Slice.rawEndPos_copy)
    · refine Or.inr ⟨String.Slice.rawEndPos_copy ▸ lt, ?_⟩
      rw [String.Slice.getUTF8Byte_copy] at first
      exact first
  · rintro (eq | ⟨lt, first⟩)
    · exact Or.inl (eq.trans String.Slice.rawEndPos_copy.symm)
    · refine Or.inr ⟨String.Slice.rawEndPos_copy.symm ▸ lt, ?_⟩
      rw [String.Slice.getUTF8Byte_copy]
      exact first

public theorem String.Slice.Pos.utf8ByteSize_byte : type_of% @_root_.String.Slice.Pos.utf8ByteSize_byte := by
  intro s p h
  rw [String.Slice.Pos.get_eq_utf8DecodeChar]
  exact ByteArray.utf8Size_utf8DecodeChar.symm

public theorem String.Slice.Pos.copy_eq_append_get : type_of% @_root_.String.Slice.Pos.copy_eq_append_get := by
  intro s p h
  have ne : (s.sliceFrom p).copy.startPos ≠ (s.sliceFrom p).copy.endPos := by
    intro eq
    rw [String.Slice.startPos_copy, String.Slice.endPos_copy] at eq
    have bounds := congrArg (fun q => String.Slice.Pos.ofSliceFrom (String.Pos.ofCopy q)) eq
    rw [String.Slice.Pos.ofCopy_copy, String.Slice.Pos.ofCopy_copy,
      String.Slice.Pos.ofSliceFrom_startPos, String.Slice.Pos.ofSliceFrom_endPos] at bounds
    exact h bounds
  obtain ⟨suffix, factor⟩ := String.eq_singleton_append ne
  refine ⟨(s.sliceTo p).copy, suffix, ?_, String.Slice.utf8ByteSize_copy.trans String.Slice.utf8ByteSize_sliceTo⟩
  simp only [String.Slice.startPos_copy, String.Slice.Pos.get_copy, String.Slice.Pos.get_eq_get_ofSliceFrom,
    String.Slice.Pos.ofSliceFrom_startPos] at factor
  rw [String.append_assoc, ← factor, ← String.Slice.copy_eq_copy_sliceTo]

public theorem String.Slice.Pos.get_copy._proof_1 : type_of% @_root_.String.Slice.Pos.get_copy._proof_1 := by
  intro s p ne eq
  exact ne ((congrArg String.Slice.Pos.copy eq).trans String.Slice.endPos_copy.symm)

public theorem String.get_startPos._proof_1 : type_of% @_root_.String.get_startPos._proof_1 := by
  intro s ne nil
  exact ne (String.startPos_eq_endPos_iff.mpr (String.toList_eq_nil_iff.mp nil))

public theorem String.head_toList : type_of% @_root_.String.head_toList := by
  intro s nonempty
  obtain ⟨xs, rfl⟩ := s.exists_eq_ofList
  cases xs with
  | nil => exact (nonempty String.toList_empty).elim
  | cons c cs =>
    have dec := List.utf8DecodeChar?_utf8Encode_cons (c := c) (l := cs)
    have xs := String.toList_ofList (l := c :: cs)
    simp only [xs, List.head_cons]
    unfold ByteArray.utf8DecodeChar
    exact (Option.get_of_eq_some _ dec).symm

public theorem String.startPos_eq_endPos_iff : type_of% @_root_.String.startPos_eq_endPos_iff := by
  intro s
  constructor
  · intro eq
    exact String.utf8ByteSize_eq_zero_iff.mp (congrArg (fun p : s.Pos => p.offset.byteIdx) eq.symm)
  · rintro rfl
    rfl

public theorem String.toList_eq_nil_iff : type_of% @_root_.String.toList_eq_nil_iff := by
  intro s
  exact ⟨fun nil => String.ofList_toList.symm.trans (congrArg String.ofList nil), fun eq => eq ▸ String.toList_empty⟩

public theorem String.isSome_utf8DecodeChar?_zero : type_of% @_root_.String.isSome_utf8DecodeChar?_zero := by
  intro s ne
  rcases String.Pos.Raw.isValid_iff_isSome_utf8DecodeChar?.mp s.startPos.isValid with endEq | valid
  · exact (ne (String.rawEndPos_eq_zero_iff.mp endEq.symm)).elim
  · exact valid

public theorem String.eq_singleton_append : type_of% @_root_.String.eq_singleton_append := by
  intro s ne
  obtain ⟨xs, rfl⟩ := s.exists_eq_ofList
  cases xs with
  | nil => exact (ne rfl).elim
  | cons c cs =>
    refine ⟨String.ofList cs, ?_⟩
    have char := String.get_startPos ne
    simp only [String.toList_ofList, List.head_cons] at char
    rw [char, String.singleton_eq_ofList, ← String.ofList_append]
    rfl

open _root_.String.Slice.Pattern
private theorem isSomeWhen (b : Bool) (q : α) : b = (if b then some q else none).isSome := by
  cases b <;> rfl

public theorem String.Slice.Pattern.CharPred.instLawfulForwardPatternForallCharBool : type_of% @_root_.String.Slice.Pattern.CharPred.instLawfulForwardPatternForallCharBool := by
  intro p
  constructor
  · intro s h
    dsimp only [ForwardPattern.skipPrefixOfNonempty?, ForwardPattern.skipPrefix?, CharPred.instForwardPatternForallCharBool]
    rw [dite_eq_right (String.Slice.startPos_ne_endPos h)]
  · intro s
    dsimp only [ForwardPattern.startsWith, ForwardPattern.skipPrefix?, CharPred.instForwardPatternForallCharBool]
    split
    · rfl
    · rename_i ne
      exact isSomeWhen _ _
public theorem String.Slice.Pattern.CharPred.instLawfulBackwardPatternForallCharBool : type_of% @_root_.String.Slice.Pattern.CharPred.instLawfulBackwardPatternForallCharBool := by
  intro p
  constructor
  · intro s h
    dsimp only [BackwardPattern.skipSuffixOfNonempty?, BackwardPattern.skipSuffix?, CharPred.instBackwardPatternForallCharBool]
    rw [dite_eq_right (String.Slice.startPos_ne_endPos h).symm]
  · intro s
    dsimp only [BackwardPattern.endsWith, BackwardPattern.skipSuffix?, CharPred.instBackwardPatternForallCharBool]
    split
    · rfl
    · rename_i ne
      exact isSomeWhen _ _

public theorem String.Slice.posGE._unary._proof_1 : type_of% (private_decl% @_root_.String.Slice.posGE._unary._proof_1) := by
  intro s p bound bad
  exact Nat.lt_of_le_of_ne bound (fun eq => bad (String.Pos.Raw.ext eq ▸ s.endPos.isValidForSlice))

public theorem String.Slice.posGE._unary._proof_2 : type_of% (private_decl% @_root_.String.Slice.posGE._unary._proof_2) := by
  intro s p bound
  exact bound

public theorem String.Slice.posGE._unary._proof_3 : type_of% (private_decl% @_root_.String.Slice.posGE._unary._proof_3) := by
  intro s p bound lt
  exact Nat.sub_lt_sub_left lt (Nat.lt_succ_self p.byteIdx)

public theorem String.Slice.posGE._unary._proof_4 : type_of% (private_decl% @_root_.String.Slice.posGE._unary._proof_4) :=
  (private_decl% @_root_.String.Slice.posGE._unary._proof_1)

public theorem String.Slice.Pos.startPos_lt_iff : type_of% @_root_.String.Slice.Pos.startPos_lt_iff := by
  intro s p
  exact ⟨fun lt eq => Nat.ne_of_lt lt (congrArg (fun q : s.Pos => q.offset.byteIdx) eq.symm),
    fun ne => Nat.pos_of_ne_zero (fun eq => ne (String.Slice.Pos.ext (String.Pos.Raw.ext eq)))⟩

public theorem String.Slice.le_offset_posGE : type_of% @_root_.String.Slice.le_offset_posGE := by
  intro s p bound
  fun_induction String.Slice.posGE with
  | case1 => exact Nat.le_refl _
  | case2 r h invalid lt ih => exact Nat.le_trans (Nat.le_succ _) ih
public theorem String.Slice.posGE_le_iff : type_of% @_root_.String.Slice.posGE_le_iff := by
  intro s p bound q
  fun_induction String.Slice.posGE with
  | case1 => exact Iff.rfl
  | case2 r h invalid lt ih =>
    exact ih.trans ⟨fun nextBound => Nat.le_trans (Nat.le_succ _) nextBound,
      fun rawBound => Nat.lt_of_le_of_ne rawBound (fun eq => invalid (String.Pos.Raw.ext eq ▸ q.isValidForSlice))⟩
public theorem String.Slice.le_posLE_iff : type_of% @_root_.String.Slice.le_posLE_iff := by
  intro s p q
  fun_induction String.Slice.posLE with
  | case1 => exact Iff.rfl
  | case2 r invalid positive ih =>
    refine ih.trans ⟨fun prevBound => Nat.le_trans prevBound (Nat.sub_le ..), fun rawBound => ?_⟩
    have strict := Nat.lt_of_le_of_ne rawBound (fun eq => invalid (String.Pos.Raw.ext eq ▸ p.isValidForSlice))
    exact Nat.le_pred_of_lt strict
public theorem String.Slice.lt_posGE_iff : type_of% @_root_.String.Slice.lt_posGE_iff := by
  intro s p bound q
  have least := String.Slice.posGE_le_iff (s := s) (p := p) (h := bound) (q := q)
  exact ⟨fun lt => Nat.lt_of_not_ge (fun ge => Nat.not_le_of_lt lt (least.mpr ge)),
    fun lt => Nat.lt_of_not_ge (fun ge => Nat.not_le_of_lt lt (least.mp ge))⟩
public theorem String.Slice.posLE_lt_iff : type_of% @_root_.String.Slice.posLE_lt_iff := by
  intro s p q
  have greatest := String.Slice.le_posLE_iff (s := s) (p := p) (q := q)
  exact ⟨fun lt => Nat.lt_of_not_ge (fun ge => Nat.not_le_of_lt lt (greatest.mpr ge)),
    fun lt => Nat.lt_of_not_ge (fun ge => Nat.not_le_of_lt lt (greatest.mp ge))⟩

public theorem String.Pos.le_startPos : type_of% @_root_.String.Pos.le_startPos := by
  intro s p
  exact ⟨fun le => String.Pos.ext (String.Pos.Raw.ext (Nat.eq_zero_of_le_zero le)),
    fun eq => eq ▸ Nat.le_refl _⟩
public theorem String.Pos.endPos_le : type_of% @_root_.String.Pos.endPos_le := by
  intro s p
  exact ⟨fun le => String.Pos.ext (String.Pos.Raw.ext (Nat.le_antisymm p.isValid.le_utf8ByteSize le)),
    fun eq => eq ▸ Nat.le_refl _⟩
public theorem String.Slice.Pos.le_startPos : type_of% @_root_.String.Slice.Pos.le_startPos := by
  intro s p
  exact ⟨fun le => String.Slice.Pos.ext (String.Pos.Raw.ext (Nat.eq_zero_of_le_zero le)),
    fun eq => eq ▸ Nat.le_refl _⟩
public theorem String.Slice.Pos.endPos_le : type_of% @_root_.String.Slice.Pos.endPos_le := by
  intro s p
  exact ⟨fun le => String.Slice.Pos.ext (String.Pos.Raw.ext (Nat.le_antisymm p.isValidForSlice.le_utf8ByteSize le)),
    fun eq => eq ▸ Nat.le_refl _⟩
public theorem String.Pos.startPos_lt_iff : type_of% @_root_.String.Pos.startPos_lt_iff := by
  intro s p
  exact ⟨fun lt eq => Nat.ne_of_lt lt (congrArg (fun q : s.Pos => q.offset.byteIdx) eq.symm),
    fun ne => Nat.pos_of_ne_zero (fun eq => ne (String.Pos.ext (String.Pos.Raw.ext eq)))⟩
public theorem String.Pos.lt_endPos_iff : type_of% @_root_.String.Pos.lt_endPos_iff := by
  intro s p
  exact ⟨fun lt eq => Nat.ne_of_lt lt (congrArg (fun q : s.Pos => q.offset.byteIdx) eq),
    fun ne => Nat.lt_of_le_of_ne p.isValid.le_utf8ByteSize (fun eq => ne (String.Pos.ext (String.Pos.Raw.ext eq)))⟩

public theorem String.Slice.Pattern.ToForwardSearcher.DefaultForwardSearcher.instIteratorIdSearchStepOfForwardPattern._proof_9 :
    type_of% @_root_.String.Slice.Pattern.ToForwardSearcher.DefaultForwardSearcher.instIteratorIdSearchStepOfForwardPattern._proof_9 := by
  intro ρ p s inst iter h pos found
  exact ⟨h, pos, found, rfl, rfl, rfl⟩

public theorem String.Slice.Pattern.ToForwardSearcher.DefaultForwardSearcher.instIteratorIdSearchStepOfForwardPattern._proof_10 :
    type_of% @_root_.String.Slice.Pattern.ToForwardSearcher.DefaultForwardSearcher.instIteratorIdSearchStepOfForwardPattern._proof_10 := by
  intro ρ p s inst iter h miss
  exact ⟨h, miss, rfl, rfl, rfl⟩

public theorem String.Slice.Pattern.ToBackwardSearcher.DefaultBackwardSearcher.instIteratorIdSearchStepOfBackwardPattern._proof_9 :
    type_of% @_root_.String.Slice.Pattern.ToBackwardSearcher.DefaultBackwardSearcher.instIteratorIdSearchStepOfBackwardPattern._proof_9 := by
  intro ρ p s inst iter h pos found
  exact ⟨h, pos, found, rfl, rfl, rfl⟩

public theorem String.Slice.Pattern.ToBackwardSearcher.DefaultBackwardSearcher.instIteratorIdSearchStepOfBackwardPattern._proof_10 :
    type_of% @_root_.String.Slice.Pattern.ToBackwardSearcher.DefaultBackwardSearcher.instIteratorIdSearchStepOfBackwardPattern._proof_10 := by
  intro ρ p s inst iter h miss
  exact ⟨h, miss, rfl, rfl, rfl⟩

private theorem booleanComplement {flag : Bool} {p : Prop} (valid : flag = true ↔ p) : flag = false ↔ ¬ p := by
  cases flag with
  | false => exact ⟨fun _ h => Bool.noConfusion (valid.mpr h), fun _ => rfl⟩
  | true => exact ⟨fun eq => Bool.noConfusion eq, fun invalid => (invalid (valid.mp rfl)).elim⟩

public theorem String.Slice.isEmpty_sliceTo : type_of% @_root_.String.Slice.isEmpty_sliceTo := by
  intro s p
  change ((s.sliceTo p).utf8ByteSize == 0) = true ↔ _
  rw [String.Slice.utf8ByteSize_sliceTo]
  exact ⟨fun eq => String.Slice.Pos.ext (String.Pos.Raw.ext (eq_of_beq eq)), fun eq => eq ▸ rfl⟩

public theorem String.Slice.isEmpty_sliceTo_eq_false_iff : type_of% @_root_.String.Slice.isEmpty_sliceTo_eq_false_iff := by
  intro s p
  exact booleanComplement String.Slice.isEmpty_sliceTo

public theorem String.Slice.isEmpty_sliceFrom_eq_false_iff : type_of% @_root_.String.Slice.isEmpty_sliceFrom_eq_false_iff := by
  intro s p
  exact booleanComplement String.Slice.isEmpty_sliceFrom

public theorem String.Slice.Pattern.ToForwardSearcher.DefaultForwardSearcher.instIteratorIdSearchStepOfForwardPattern._proof_5 :
    type_of% @_root_.String.Slice.Pattern.ToForwardSearcher.DefaultForwardSearcher.instIteratorIdSearchStepOfForwardPattern._proof_5 := by
  intro ρ pat s iter ne
  exact String.Slice.isEmpty_sliceFrom_eq_false_iff.mpr ne

public theorem String.Slice.Pattern.ToForwardSearcher.DefaultForwardSearcher.instIteratorIdSearchStepOfForwardPattern._proof_7 :
    type_of% @_root_.String.Slice.Pattern.ToForwardSearcher.DefaultForwardSearcher.instIteratorIdSearchStepOfForwardPattern._proof_7 := by
  intro ρ pat s iter ne
  exact String.Slice.isEmpty_sliceFrom_eq_false_iff.mpr ne

public theorem String.Slice.Pattern.ToBackwardSearcher.DefaultBackwardSearcher.instIteratorIdSearchStepOfBackwardPattern._proof_5 :
    type_of% @_root_.String.Slice.Pattern.ToBackwardSearcher.DefaultBackwardSearcher.instIteratorIdSearchStepOfBackwardPattern._proof_5 := by
  intro ρ pat s iter ne
  exact String.Slice.isEmpty_sliceTo_eq_false_iff.mpr ne

public theorem String.Slice.Pattern.ToBackwardSearcher.DefaultBackwardSearcher.instIteratorIdSearchStepOfBackwardPattern._proof_7 :
    type_of% @_root_.String.Slice.Pattern.ToBackwardSearcher.DefaultBackwardSearcher.instIteratorIdSearchStepOfBackwardPattern._proof_7 := by
  intro ρ pat s iter ne
  exact String.Slice.isEmpty_sliceTo_eq_false_iff.mpr ne

public theorem String.Pos.next_le_of_lt : type_of% @_root_.String.Pos.next_le_of_lt := by
  intro s p q h lt
  exact _root_.String.Slice.Pos.next_le_of_lt (p := p.toSlice) (q := q.toSlice) lt

private theorem ltIffLeOfReverse {a b c d : Nat} (reverse : b ≤ a ↔ d < c) : a < b ↔ c ≤ d :=
  ⟨fun lt => Nat.le_of_not_gt (fun gt => Nat.not_le_of_gt lt (reverse.mpr gt)),
    fun le => Nat.lt_of_not_ge (fun ge => Nat.not_lt_of_ge le (reverse.mp ge))⟩

public theorem String.Slice.Pos.lt_next_iff_le : type_of% @_root_.String.Slice.Pos.lt_next_iff_le := by
  intro s p q h
  exact ltIffLeOfReverse (_root_.String.Slice.Pos.next_le_iff_lt (p := q) (q := p) (h := h))

public theorem String.Pos.lt_next_iff_le : type_of% @_root_.String.Pos.lt_next_iff_le := by
  intro s p q h
  exact ltIffLeOfReverse (_root_.String.Pos.next_le_iff_lt (p := q) (q := p) (h := h))

public theorem String.Pos.offset_lt_rawEndPos_iff : type_of% @_root_.String.Pos.offset_lt_rawEndPos_iff := by
  intro s p
  exact String.Pos.lt_endPos_iff p

public theorem String.Slice.Pos.sliceFrom_le_iff : type_of% @_root_.String.Slice.Pos.sliceFrom_le_iff := by
  intro s start p q bound
  exact Nat.sub_le_iff_le_add'

public theorem String.Slice.Pos.slice_le_iff : type_of% @_root_.String.Slice.Pos.slice_le_iff := by
  intro s start stop ordered p q lower upper
  exact Nat.sub_le_iff_le_add'

public theorem String.Slice.Pos.slice_lt_iff : type_of% @_root_.String.Slice.Pos.slice_lt_iff := by
  intro s start stop ordered p q lower upper
  exact Nat.sub_lt_iff_lt_add' lower

public theorem String.Slice.Pos.lt_slice_iff : type_of% @_root_.String.Slice.Pos.lt_slice_iff := by
  intro s start stop ordered p q lower upper
  exact Nat.lt_sub_iff_add_lt'

public theorem String.Slice.Pos.le_slice_iff : type_of% @_root_.String.Slice.Pos.le_slice_iff := by
  intro s start stop ordered p q lower upper
  exact Nat.le_sub_iff_add_le' lower

public theorem String.Pos.sliceFrom_le_iff : type_of% @_root_.String.Pos.sliceFrom_le_iff := by
  intro s start p q bound
  exact Nat.sub_le_iff_le_add'

public theorem String.Pos.slice_le_iff : type_of% @_root_.String.Pos.slice_le_iff := by
  intro s start stop ordered p q lower upper
  exact Nat.sub_le_iff_le_add'

public theorem String.Pos.slice_lt_iff : type_of% @_root_.String.Pos.slice_lt_iff := by
  intro s start stop ordered p q lower upper
  exact Nat.sub_lt_iff_lt_add' lower

public theorem String.Pos.lt_slice_iff : type_of% @_root_.String.Pos.lt_slice_iff := by
  intro s start stop ordered p q lower upper
  exact Nat.lt_sub_iff_add_lt'

public theorem String.Pos.le_slice_iff : type_of% @_root_.String.Pos.le_slice_iff := by
  intro s start stop ordered p q lower upper
  exact Nat.le_sub_iff_add_le' lower

public theorem String.Slice.Pos.ofSlice_lt_iff : type_of% @_root_.String.Slice.Pos.ofSlice_lt_iff := by
  intro s start stop ordered p q
  have left := @_root_.String.Slice.Pos.le_ofSlice s start stop ordered p
  have right := @_root_.String.Slice.Pos.ofSlice_le s start stop ordered p
  constructor
  · intro bound upper
    have lower : start ≤ q := Nat.le_of_lt (Nat.lt_of_le_of_lt left bound)
    exact ⟨lower, (String.Slice.Pos.lt_slice_iff (h₀ := lower) (h₁ := upper)).mpr bound⟩
  · intro within
    by_cases upper : q ≤ stop
    · obtain ⟨lower, inner⟩ := within upper
      exact (String.Slice.Pos.lt_slice_iff (h₀ := lower) (h₁ := upper)).mp inner
    · exact Nat.lt_of_le_of_lt right (Nat.lt_of_not_ge upper)

public theorem String.Slice.Pos.ofSlice_le_iff : type_of% @_root_.String.Slice.Pos.ofSlice_le_iff := by
  intro s start stop ordered p q
  have left := @_root_.String.Slice.Pos.le_ofSlice s start stop ordered p
  have right := @_root_.String.Slice.Pos.ofSlice_le s start stop ordered p
  constructor
  · intro bound upper
    have lower : start ≤ q := Nat.le_trans left bound
    exact ⟨lower, (String.Slice.Pos.le_slice_iff (h₀ := lower) (h₁ := upper)).mpr bound⟩
  · intro within
    by_cases upper : q ≤ stop
    · obtain ⟨lower, inner⟩ := within upper
      exact (String.Slice.Pos.le_slice_iff (h₀ := lower) (h₁ := upper)).mp inner
    · exact Nat.le_trans right (Nat.le_of_lt (Nat.lt_of_not_ge upper))

public theorem String.Pos.ofSlice_lt_iff : type_of% @_root_.String.Pos.ofSlice_lt_iff := by
  intro s start stop ordered p q
  exact String.Slice.Pos.ofSlice_lt_iff (p₀ := start.toSlice) (p₁ := stop.toSlice) (p := p) (q := q.toSlice)

public theorem String.Pos.ofSlice_le_iff : type_of% @_root_.String.Pos.ofSlice_le_iff := by
  intro s start stop ordered p q
  exact String.Slice.Pos.ofSlice_le_iff (p₀ := start.toSlice) (p₁ := stop.toSlice) (p := p) (q := q.toSlice)

public theorem String.Slice.Pos.ofSliceFrom_ne_startPos : type_of% @_root_.String.Slice.Pos.ofSliceFrom_ne_startPos := by
  intro s start p ne
  have inner := (String.Slice.Pos.startPos_lt_iff p).mpr ne
  exact (String.Slice.Pos.startPos_lt_iff _).mp
    (Nat.lt_of_lt_of_le inner (Nat.le_add_left p.offset.byteIdx start.offset.byteIdx))

public theorem String.Slice.Pos.ne_startPos_of_sliceFrom_ne_startPos : type_of% @_root_.String.Slice.Pos.ne_startPos_of_sliceFrom_ne_startPos := by
  intro s p start bound ne
  have inner := (String.Slice.Pos.startPos_lt_iff _).mpr ne
  exact (String.Slice.Pos.startPos_lt_iff p).mp (Nat.lt_of_lt_of_le inner (Nat.sub_le ..))

public theorem String.Slice.Pos.ofSlice_ne_startPos : type_of% @_root_.String.Slice.Pos.ofSlice_ne_startPos := by
  intro s start stop ordered p ne
  have inner := (String.Slice.Pos.startPos_lt_iff p).mpr ne
  exact (String.Slice.Pos.startPos_lt_iff _).mp
    (Nat.lt_of_lt_of_le inner (Nat.le_add_left p.offset.byteIdx start.offset.byteIdx))

public theorem String.Slice.Pos.ne_startPos_of_slice_ne_startPos : type_of% @_root_.String.Slice.Pos.ne_startPos_of_slice_ne_startPos := by
  intro s p start stop lower upper ne
  have inner := (String.Slice.Pos.startPos_lt_iff _).mpr ne
  exact (String.Slice.Pos.startPos_lt_iff p).mp (Nat.lt_of_lt_of_le inner (Nat.sub_le ..))

public theorem String.Pos.ofSliceFrom_ne_startPos : type_of% @_root_.String.Pos.ofSliceFrom_ne_startPos := by
  intro s start p ne
  intro atStart
  apply String.Slice.Pos.ofSliceFrom_ne_startPos (p₀ := start.toSlice) (p := p) ne
  exact String.Slice.Pos.ext (congrArg String.Pos.offset atStart)

public theorem String.Pos.ne_startPos_of_sliceFrom_ne_startPos : type_of% @_root_.String.Pos.ne_startPos_of_sliceFrom_ne_startPos := by
  intro s p start bound ne
  intro atStart
  apply String.Slice.Pos.ne_startPos_of_sliceFrom_ne_startPos (p₀ := start.toSlice) (p := p.toSlice) (h₀ := bound) ne
  exact String.Slice.Pos.ext (congrArg String.Pos.offset atStart)

public theorem String.Pos.ofSlice_ne_startPos : type_of% @_root_.String.Pos.ofSlice_ne_startPos := by
  intro s start stop ordered p ne
  intro atStart
  apply String.Slice.Pos.ofSlice_ne_startPos (p₀ := start.toSlice) (p₁ := stop.toSlice) (p := p) ne
  exact String.Slice.Pos.ext (congrArg String.Pos.offset atStart)

public theorem String.Pos.ne_startPos_of_slice_ne_startPos : type_of% @_root_.String.Pos.ne_startPos_of_slice_ne_startPos := by
  intro s p start stop lower upper ne
  intro atStart
  apply String.Slice.Pos.ne_startPos_of_slice_ne_startPos (p₀ := start.toSlice) (p₁ := stop.toSlice) (p := p.toSlice) ne
  exact String.Slice.Pos.ext (congrArg String.Pos.offset atStart)

public theorem String.Slice.Pos.lt_ofSliceTo_iff : type_of% @_root_.String.Slice.Pos.lt_ofSliceTo_iff := by
  intro s stop p q
  exact ⟨fun lt => ⟨Nat.le_trans (Nat.le_of_lt lt) (_root_.String.Slice.Pos.ofSliceTo_le (pos := p)), lt⟩,
    fun ⟨_, lt⟩ => lt⟩

public theorem String.Slice.Pos.ofSliceTo_le_iff : type_of% @_root_.String.Slice.Pos.ofSliceTo_le_iff := by
  intro s stop p q
  refine ⟨fun le _ => le, fun all => Nat.le_of_not_gt (fun gt => ?_)⟩
  obtain ⟨bound, inner⟩ := String.Slice.Pos.lt_ofSliceTo_iff.mp gt
  exact Nat.not_lt_of_ge (all bound) inner

public theorem String.Pos.ofSliceTo_le_iff : type_of% @_root_.String.Pos.ofSliceTo_le_iff := by
  intro s stop p q
  exact String.Slice.Pos.ofSliceTo_le_iff (p₀ := stop.toSlice) (p := p) (q := q.toSlice)

public theorem String.Slice.Pos.le_ofSliceFrom_iff : type_of% @_root_.String.Slice.Pos.le_ofSliceFrom_iff := by
  intro s start p q
  refine ⟨fun outer lower => (String.Slice.Pos.sliceFrom_le_iff (h := lower)).mpr outer, fun all => ?_⟩
  by_cases lower : start ≤ q
  · exact (String.Slice.Pos.sliceFrom_le_iff (h := lower)).mp (all lower)
  · exact Nat.le_trans (Nat.le_of_lt (Nat.lt_of_not_ge lower)) (_root_.String.Slice.Pos.le_ofSliceFrom (pos := p))

public theorem String.Pos.le_ofSliceFrom_iff : type_of% @_root_.String.Pos.le_ofSliceFrom_iff := by
  intro s start p q
  exact String.Slice.Pos.le_ofSliceFrom_iff (p₀ := start.toSlice) (p := p) (q := q.toSlice)

public theorem String.Pos.ofSliceTo_ne_endPos : type_of% @_root_.String.Pos.ofSliceTo_ne_endPos := by
  intro s stop p ne
  have inner : p.offset.byteIdx < (s.sliceTo stop).utf8ByteSize := (String.Slice.Pos.lt_endPos_iff p).mpr ne
  rw [String.utf8ByteSize_sliceTo] at inner
  exact (String.Pos.lt_endPos_iff _).mp (Nat.lt_of_lt_of_le inner stop.isValid.le_utf8ByteSize)

public theorem String.Pos.ne_endPos_of_sliceTo_ne_endPos : type_of% @_root_.String.Pos.ne_endPos_of_sliceTo_ne_endPos := by
  intro s p stop bound ne atEnd
  exact String.Pos.ofSliceTo_ne_endPos (p := stop.sliceTo p bound) ne
    (String.Pos.ext (congrArg String.Pos.offset atEnd))

public theorem String.Pos.ofSlice_ne_endPos : type_of% @_root_.String.Pos.ofSlice_ne_endPos := by
  intro s start stop ordered p ne
  have inner : p.offset.byteIdx < (s.slice start stop ordered).utf8ByteSize := (String.Slice.Pos.lt_endPos_iff p).mpr ne
  rw [String.utf8ByteSize_slice] at inner
  exact (String.Pos.lt_endPos_iff _).mp
    (Nat.lt_of_lt_of_le (Nat.lt_sub_iff_add_lt'.mp inner) stop.isValid.le_utf8ByteSize)

public theorem String.Pos.ne_endPos_of_slice_ne_endPos : type_of% @_root_.String.Pos.ne_endPos_of_slice_ne_endPos := by
  intro s p start stop lower upper ne atEnd
  exact String.Pos.ofSlice_ne_endPos (p := p.slice start stop lower upper) ne
    ((_root_.String.Pos.ofSlice_slice (h₁ := lower) (h₂ := upper)).trans atEnd)

public theorem String.Slice.Pos.posGE_offset : type_of% @_root_.String.Slice.Pos.posGE_offset := by
  intro s p
  exact _root_.String.Slice.posGE_eq_iff.mpr ⟨Nat.le_refl _, fun _ h => h⟩

public theorem String.Slice.Pos.posLE_offset : type_of% @_root_.String.Slice.Pos.posLE_offset := by
  intro s p
  exact _root_.String.Slice.posLE_eq_iff.mpr ⟨Nat.le_refl _, fun _ h => h⟩

public theorem String.Slice.posLT_eq_iff : type_of% @_root_.String.Slice.posLT_eq_iff := by
  intro s raw h p
  constructor
  · rintro rfl
    exact ⟨_root_.String.Slice.offset_posLT_lt, fun _ lt => _root_.String.Slice.le_posLT_iff.mpr lt⟩
  · rintro ⟨bound, maximal⟩
    apply _root_.String.Slice.Pos.ext
    apply String.Pos.Raw.ext
    exact Nat.le_antisymm (maximal _ _root_.String.Slice.offset_posLT_lt)
      (_root_.String.Slice.le_posLT_iff.mpr bound)

public theorem String.Slice.Pos.prev_eq_iff : type_of% @_root_.String.Slice.Pos.prev_eq_iff := by
  intro s p q h
  rw [_root_.String.Slice.Pos.prev_eq_posLT]
  exact String.Slice.posLT_eq_iff

public theorem String.Slice.Pos.prev_le : type_of% @_root_.String.Slice.Pos.prev_le := by
  intro s p h
  exact Nat.le_of_lt (_root_.String.Slice.Pos.prev_lt (h := h))

public theorem String.Pos.posGE_offset : type_of% @_root_.String.Pos.posGE_offset := by
  intro s p
  exact _root_.String.posGE_eq_iff.mpr ⟨Nat.le_refl _, fun _ h => h⟩

public theorem String.Pos.posLE_offset : type_of% @_root_.String.Pos.posLE_offset := by
  intro s p
  exact _root_.String.posLE_eq_iff.mpr ⟨Nat.le_refl _, fun _ h => h⟩

public theorem String.posLT_eq_iff : type_of% @_root_.String.posLT_eq_iff := by
  intro s raw h p
  constructor
  · rintro rfl
    exact ⟨_root_.String.offset_posLT_lt, fun _ lt => _root_.String.le_posLT_iff.mpr lt⟩
  · rintro ⟨bound, maximal⟩
    apply _root_.String.Pos.ext
    apply String.Pos.Raw.ext
    exact Nat.le_antisymm (maximal _ _root_.String.offset_posLT_lt)
      (_root_.String.le_posLT_iff.mpr bound)

public theorem String.Pos.prev_eq_iff : type_of% @_root_.String.Pos.prev_eq_iff := by
  intro s p q h
  rw [_root_.String.Pos.prev_eq_posLT]
  exact String.posLT_eq_iff

public theorem String.Pos.prev_le : type_of% @_root_.String.Pos.prev_le := by
  intro s p h
  exact Nat.le_of_lt (_root_.String.Pos.prev_lt (h := h))

public theorem String.Slice.Pos.prevn_le : type_of% @_root_.String.Slice.Pos.prevn_le := by
  intro s p n
  fun_induction _root_.String.Slice.Pos.prevn with
  | case1 => exact Nat.le_refl _
  | case2 p n h ih => exact Nat.le_trans ih (String.Slice.Pos.prev_le (h := h))
  | case3 => exact Nat.le_refl _

public theorem String.Pos.prevn_le : type_of% @_root_.String.Pos.prevn_le := by
  intro s p n
  exact String.Slice.Pos.prevn_le (p := p.toSlice) (n := n)

public theorem String.Slice.Pos.ofSliceTo_prev : type_of% @_root_.String.Slice.Pos.ofSliceTo_prev := by
  intro s base p h
  apply Eq.symm
  apply String.Slice.Pos.prev_eq_iff.mpr
  refine ⟨_root_.String.Slice.Pos.ofSliceTo_lt_ofSliceTo_iff.mpr _root_.String.Slice.Pos.prev_lt, ?_⟩
  intro q lt
  obtain ⟨bound, small⟩ := _root_.String.Slice.Pos.lt_ofSliceTo_iff.mp lt
  exact _root_.String.Slice.Pos.le_ofSliceTo_iff.mpr ⟨bound, _root_.String.Slice.Pos.le_prev_iff_lt.mpr small⟩

public theorem String.Slice.Pos.prev_ofSliceTo : type_of% @_root_.String.Slice.Pos.prev_ofSliceTo := by
  intro s base p h
  exact String.Slice.Pos.ofSliceTo_prev.symm

public theorem String.Slice.Pos.ofSliceFrom_prev : type_of% @_root_.String.Slice.Pos.ofSliceFrom_prev := by
  intro s base p h
  apply Eq.symm
  apply String.Slice.Pos.prev_eq_iff.mpr
  refine ⟨_root_.String.Slice.Pos.ofSliceFrom_lt_ofSliceFrom_iff.mpr _root_.String.Slice.Pos.prev_lt, ?_⟩
  intro q lt
  exact _root_.String.Slice.Pos.le_ofSliceFrom_iff.mpr fun bound =>
    _root_.String.Slice.Pos.le_prev_iff_lt.mpr (_root_.String.Slice.Pos.lt_ofSliceFrom_iff.mp lt bound)

public theorem String.Slice.Pos.ofSlice_prev : type_of% @_root_.String.Slice.Pos.ofSlice_prev := by
  intro s lo hi le p h
  apply Eq.symm
  apply String.Slice.Pos.prev_eq_iff.mpr
  refine ⟨_root_.String.Slice.Pos.ofSlice_lt_ofSlice_iff.mpr _root_.String.Slice.Pos.prev_lt, ?_⟩
  intro q lt
  obtain ⟨upper, small⟩ := _root_.String.Slice.Pos.lt_ofSlice_iff.mp lt
  exact _root_.String.Slice.Pos.le_ofSlice_iff.mpr ⟨upper, fun lower =>
    _root_.String.Slice.Pos.le_prev_iff_lt.mpr (small lower)⟩

public theorem String.Pos.ofSliceTo_prev : type_of% @_root_.String.Pos.ofSliceTo_prev := by
  intro s base p h
  apply Eq.symm
  apply String.Pos.prev_eq_iff.mpr
  refine ⟨_root_.String.Pos.ofSliceTo_lt_ofSliceTo_iff.mpr _root_.String.Slice.Pos.prev_lt, ?_⟩
  intro q lt
  obtain ⟨bound, small⟩ := _root_.String.Pos.lt_ofSliceTo_iff.mp lt
  exact _root_.String.Pos.le_ofSliceTo_iff.mpr ⟨bound, _root_.String.Slice.Pos.le_prev_iff_lt.mpr small⟩

public theorem String.Pos.prev_ofSliceTo : type_of% @_root_.String.Pos.prev_ofSliceTo := by
  intro s base p h
  exact String.Pos.ofSliceTo_prev.symm

public theorem String.Pos.ofSliceFrom_prev : type_of% @_root_.String.Pos.ofSliceFrom_prev := by
  intro s base p h
  apply Eq.symm
  apply String.Pos.prev_eq_iff.mpr
  refine ⟨_root_.String.Pos.ofSliceFrom_lt_ofSliceFrom_iff.mpr _root_.String.Slice.Pos.prev_lt, ?_⟩
  intro q lt
  exact _root_.String.Pos.le_ofSliceFrom_iff.mpr fun bound =>
    _root_.String.Slice.Pos.le_prev_iff_lt.mpr (_root_.String.Pos.lt_ofSliceFrom_iff.mp lt bound)

public theorem String.Pos.ofSlice_prev : type_of% @_root_.String.Pos.ofSlice_prev := by
  intro s lo hi le p h
  apply Eq.symm
  apply String.Pos.prev_eq_iff.mpr
  refine ⟨_root_.String.Pos.ofSlice_lt_ofSlice_iff.mpr _root_.String.Slice.Pos.prev_lt, ?_⟩
  intro q lt
  obtain ⟨upper, small⟩ := _root_.String.Pos.lt_ofSlice_iff.mp lt
  exact _root_.String.Pos.le_ofSlice_iff.mpr ⟨upper, fun lower =>
    _root_.String.Slice.Pos.le_prev_iff_lt.mpr (small lower)⟩

public theorem String.Slice.isEmpty_eq_false_of_lt : type_of% @_root_.String.Slice.isEmpty_eq_false_of_lt := by
  intro s p q lt
  apply String.Slice.startPos_ne_endPos_iff.mp
  intro ends
  have zero := congrArg (fun x : s.Pos => x.offset.byteIdx) ends
  exact Nat.not_lt_zero _ (Nat.lt_of_lt_of_le lt (Nat.le_trans q.isValidForSlice.le_utf8ByteSize (Nat.le_of_eq zero.symm)))

public theorem String.ne_empty_of_lt : type_of% @_root_.String.ne_empty_of_lt := by
  intro s p q lt eq
  have same := _root_.String.eq_empty_iff_forall_eq.mp eq p q
  exact Nat.ne_of_lt lt (congrArg (fun x : s.Pos => x.offset.byteIdx) same)

public theorem String.isEmpty_sliceTo : type_of% @_root_.String.isEmpty_sliceTo := by
  intro s p
  exact (String.Slice.isEmpty_sliceTo (p := p.toSlice)).trans
    ⟨fun eq => String.Pos.ext (congrArg (fun q : s.toSlice.Pos => q.offset) eq), fun eq => eq ▸ rfl⟩

public theorem String.isEmpty_sliceTo_eq_false_iff : type_of% @_root_.String.isEmpty_sliceTo_eq_false_iff := by
  intro s p
  exact booleanComplement String.isEmpty_sliceTo

public theorem String.isEmpty_sliceFrom_eq_false_iff : type_of% @_root_.String.isEmpty_sliceFrom_eq_false_iff := by
  intro s p
  exact booleanComplement _root_.String.isEmpty_sliceFrom

public theorem String.copy_sliceTo_startPos : type_of% @_root_.String.copy_sliceTo_startPos := by
  intro s
  exact _root_.String.Slice.copy_eq_empty_iff.mpr (String.isEmpty_sliceTo.mpr rfl)

public theorem String.Slice.isEmpty_slice_eq_false_iff : type_of% @_root_.String.Slice.isEmpty_slice_eq_false_iff := by
  intro s p q h
  exact booleanComplement (_root_.String.Slice.isEmpty_slice (h := h))

public theorem String.isEmpty_slice_eq_false_iff : type_of% @_root_.String.isEmpty_slice_eq_false_iff := by
  intro s p q h
  exact booleanComplement (_root_.String.isEmpty_slice (h := h))

public theorem String.Pos.wellFounded_lt : type_of% @_root_.String.Pos.wellFounded_lt := by
  intro s
  exact InvImage.wf (fun p : s.Pos => p.offset.byteIdx) Nat.lt_wfRel.wf

public theorem String.Pos.wellFounded_gt : type_of% @_root_.String.Pos.wellFounded_gt := by
  intro s
  exact InvImage.wf (fun p : s.Pos => p.toSlice) _root_.String.Slice.Pos.wellFounded_gt

public theorem String.Slice.Pos.ne_endPos_of_next?_eq_some :
    type_of% @_root_.String.Slice.Pos.ne_endPos_of_next?_eq_some := by
  intro s p q found atEnd
  rw [_root_.String.Slice.Pos.next?, dite_eq_left atEnd] at found
  cases found

public theorem String.Slice.Pos.eq_next_of_next?_eq_some :
    type_of% @_root_.String.Slice.Pos.eq_next_of_next?_eq_some := by
  intro s p q found
  have ne := String.Slice.Pos.ne_endPos_of_next?_eq_some found
  have eq := found
  rw [_root_.String.Slice.Pos.next?, dite_eq_right ne] at eq
  exact (Option.some.inj eq).symm

public theorem String.Slice.Pos.ne_startPos_of_prev?_eq_some :
    type_of% @_root_.String.Slice.Pos.ne_startPos_of_prev?_eq_some := by
  intro s p q found atEnd
  rw [_root_.String.Slice.Pos.prev?_eq_dite, dite_eq_left atEnd] at found
  cases found

public theorem String.Slice.Pos.eq_prev_of_prev?_eq_some :
    type_of% @_root_.String.Slice.Pos.eq_prev_of_prev?_eq_some := by
  intro s p q found
  have ne := String.Slice.Pos.ne_startPos_of_prev?_eq_some found
  have eq := found
  rw [_root_.String.Slice.Pos.prev?_eq_dite, dite_eq_right ne] at eq
  exact (Option.some.inj eq).symm

public theorem String.Slice.SplitInclusiveIterator.finitenessRelation._proof_2 :
    type_of% (private_decl% @_root_.String.Slice.SplitInclusiveIterator.finitenessRelation._proof_2) := by
  intro ρ σ iter pat searcher s it it' successor
  obtain ⟨step, next, valid⟩ := successor
  cases step <;> cases next
  all_goals
    obtain ⟨state⟩ := it
    obtain ⟨state'⟩ := it'
    cases state <;> cases state' <;> first | exact valid | exact True.intro | exact False.elim valid

public theorem String.Slice.RevSplitIterator.finitenessRelation._proof_2 :
    type_of% (private_decl% @_root_.String.Slice.RevSplitIterator.finitenessRelation._proof_2) := by
  intro ρ σ iter pat searcher s it it' successor
  obtain ⟨step, next, valid⟩ := successor
  cases step <;> cases next
  all_goals
    obtain ⟨state⟩ := it
    obtain ⟨state'⟩ := it'
    cases state <;> cases state' <;> first | exact valid | exact True.intro | exact False.elim valid

end OmegaChecks.InitPort.Alternatives
