module
import all Init.Data.String.Basic
import all Init.Data.String.FindPos
import all Init.Data.String.Lemmas.FindPos
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Defs
public import OmegaChecks.InitPort.Alternatives.StringEncoding

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

end OmegaChecks.InitPort.Alternatives
