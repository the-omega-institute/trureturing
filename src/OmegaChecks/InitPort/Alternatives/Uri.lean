/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Lovett
-/
module
public import Init.System.Uri
import all Init.System.Uri
import Init.Data.Nat.Lemmas

/-! Decode percent escapes by induction on the number of input bytes left to read. -/

namespace OmegaChecks.InitPort.Alternatives.System.Uri.UriEscape

private abbrev State := ByteArray × Nat

private def decodeStep (raw : ByteArray) (state : State) : ForInStep State :=
  let (decoded, i) := state
  if h : i < raw.size then
    let c := raw[i]
    let next := if h₁ : c == '%'.toNat.toUInt8 ∧ i + 1 < raw.size then
      let h1 := raw[i + 1]
      if let some hd1 := _root_.System.Uri.UriEscape.decodeUri.hexDigitToUInt8? h1 then
        if h₂ : i + 2 < raw.size then
          let h2 := raw[i + 2]
          if let some hd2 := _root_.System.Uri.UriEscape.decodeUri.hexDigitToUInt8? h2 then
            (decoded.push (hd1 * 16 + hd2), i + 3)
          else (((decoded.push c).push h1).push h2, i + 3)
        else ((decoded.push c).push h1, i + 2)
      else ((decoded.push c).push h1, i + 2)
    else (decoded.push c, i + 1)
    .yield next
  else .done state

private theorem decodeStep_decreases {raw : ByteArray} {state next : State}
    (h : decodeStep raw state = .yield next) : raw.size - next.2 < raw.size - state.2 := by
  rcases state with ⟨out, i⟩
  unfold decodeStep at h
  dsimp only at h
  split at h
  · rename_i short
    apply Nat.sub_lt_sub_left short
    have values := ForInStep.yield.inj h
    split at values
    · split at values
      · split at values
        · split at values <;> cases values <;> exact Nat.lt_add_of_pos_right (by decide)
        · cases values; exact Nat.lt_add_of_pos_right (by decide)
      · cases values; exact Nat.lt_add_of_pos_right (by decide)
    · cases values; exact Nat.lt_add_of_pos_right (by decide)
  · contradiction

private noncomputable def decodeLoop (raw : ByteArray) (state : State) : State :=
  match _h : decodeStep raw state with
  | .done result => result
  | .yield next => decodeLoop raw next
termination_by raw.size - state.2
decreasing_by exact decodeStep_decreases _h

private theorem decodeLoop_eq (raw : ByteArray) (state : State) :
    decodeLoop raw state = match decodeStep raw state with
    | .done result => result
    | .yield next => decodeLoop raw next := by
  rw [decodeLoop.eq_1]
  cases decodeStep raw state <;> rfl

public noncomputable def decodeUri (uri : String) : String :=
  String.fromUTF8! (decodeLoop uri.toUTF8 (ByteArray.empty, 0)).1

end OmegaChecks.InitPort.Alternatives.System.Uri.UriEscape
