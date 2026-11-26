module
import all Init.Data.String.Decode

/-! The leading and continuation byte ranges of UTF-8 code points. -/

namespace OmegaChecks.InitPort.Alternatives

private def checkBelow (p : Nat → Bool) : Nat → Bool
  | 0 => true
  | n + 1 => checkBelow p n && p n

private theorem checkedBelow {p : Nat → Bool} {n : Nat} (check : checkBelow p n = true) :
    ∀ x : Fin n, p x.val = true := by
  induction n with
  | zero => intro x; exact (Nat.not_lt_zero x.val x.isLt).elim
  | succ n ih =>
    intro x
    have both := Bool.and_eq_true_iff.mp check
    cases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ x.isLt) with
    | inl eq => exact (congrArg p eq).trans both.2
    | inr lt => exact ih both.1 ⟨x.val, lt⟩

private theorem firstAscii (x : Fin 128) : (UInt8.ofNat x.val).IsUTF8FirstByte :=
  of_decide_eq_true (checkedBelow (p := fun i => decide ((UInt8.ofNat i).IsUTF8FirstByte)) (by rfl) x)

private theorem firstTwo (x : Fin 32) : (UInt8.ofNat (x.val + 192)).IsUTF8FirstByte :=
  of_decide_eq_true (checkedBelow (p := fun i => decide ((UInt8.ofNat (i + 192)).IsUTF8FirstByte)) (by rfl) x)

private theorem firstThree (x : Fin 16) : (UInt8.ofNat (x.val + 224)).IsUTF8FirstByte :=
  of_decide_eq_true (checkedBelow (p := fun i => decide ((UInt8.ofNat (i + 224)).IsUTF8FirstByte)) (by rfl) x)

private theorem firstFour (x : Fin 8) : (UInt8.ofNat (x.val + 240)).IsUTF8FirstByte :=
  of_decide_eq_true (checkedBelow (p := fun i => decide ((UInt8.ofNat (i + 240)).IsUTF8FirstByte)) (by rfl) x)

private theorem continuation (x : Fin 64) : ¬ (UInt8.ofNat (x.val + 128)).IsUTF8FirstByte :=
  of_decide_eq_true (checkedBelow (p := fun i => decide (¬ (UInt8.ofNat (i + 128)).IsUTF8FirstByte)) (by rfl) x)

private def byteOffsets (bs : List UInt8) := ∀ (i : Nat) (h : i < bs.length), bs[i].IsUTF8FirstByte ↔ i = 0

public theorem UInt8.isUTF8FirstByte_getElem_utf8EncodeChar :
    type_of% @_root_.UInt8.isUTF8FirstByte_getElem_utf8EncodeChar := by
  intro c
  change byteOffsets (String.utf8EncodeChar c)
  unfold String.utf8EncodeChar
  dsimp only
  split
  · rename_i ascii
    intro i hi
    cases i with
    | zero => exact ⟨fun _ => rfl, fun _ => firstAscii ⟨_, Nat.lt_succ_of_le ascii⟩⟩
    | succ i => exact (Nat.not_lt_zero _ (Nat.lt_of_succ_lt_succ hi)).elim
  · split
    · intro i hi
      match i, hi with
      | 0, _ => exact ⟨fun _ => rfl, fun _ => firstTwo ⟨_, Nat.mod_lt _ (by decide)⟩⟩
      | 1, _ => exact ⟨fun h => (continuation ⟨_, Nat.mod_lt _ (by decide)⟩ h).elim, by intro h; cases h⟩
    · split
      · intro i hi
        match i, hi with
        | 0, _ => exact ⟨fun _ => rfl, fun _ => firstThree ⟨_, Nat.mod_lt _ (by decide)⟩⟩
        | 1, _ | 2, _ => exact ⟨fun h => (continuation ⟨_, Nat.mod_lt _ (by decide)⟩ h).elim, by intro h; cases h⟩
      · intro i hi
        match i, hi with
        | 0, _ => exact ⟨fun _ => rfl, fun _ => firstFour ⟨_, Nat.mod_lt _ (by decide)⟩⟩
        | 1, _ | 2, _ | 3, _ => exact ⟨fun h => (continuation ⟨_, Nat.mod_lt _ (by decide)⟩ h).elim, by intro h; cases h⟩

end OmegaChecks.InitPort.Alternatives
