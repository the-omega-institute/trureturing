module
import all Init.Data.Float.Model.Float
import all Init.Data.Float.Model.Float32

/-! IEEE packing produces a canonical NaN for both binary formats. -/

namespace OmegaChecks.InitPort.Alternatives
open _root_.Float.Model
open _root_.Float.Model.UnpackedFloat

public theorem Float.Model.UnpackedFloat.unpackMantissa_packComponents :
    type_of% @_root_.Float.Model.UnpackedFloat.unpackMantissa_packComponents := by
  intro spec sign exponent mantissa
  exact BitVec.extractLsb'_append_eq_right

public theorem Float.Model.UnpackedFloat.unpackExponent_packComponents :
    type_of% @_root_.Float.Model.UnpackedFloat.unpackExponent_packComponents := by
  intro spec sign exponent mantissa
  unfold unpackExponent packComponents
  rw [BitVec.extractLsb'_append_eq_of_le (Nat.le_refl _), Nat.sub_self]
  exact BitVec.extractLsb'_append_eq_right

private theorem exponentNat {w : Nat} : (-1#w).toNat = 2 ^ w - 1 := by
  rw [BitVec.neg_one_eq_allOnes, BitVec.toNat_allOnes]

private theorem nonExceptional {spec : Format} {sign : Sign} {e : BitVec spec.exponentBits}
    {m : BitVec spec.mantissaBitsWithoutImplicit} (h : e.toNat < 2 ^ spec.exponentBits - 1) :
    spec.Valid (packComponents spec sign e m) :=
  ⟨fun he _ => False.elim ((Nat.ne_of_lt h) ((congrArg BitVec.toNat
    (Float.Model.UnpackedFloat.unpackExponent_packComponents.symm.trans he)).trans exponentNat))⟩

private theorem validZeroMantissa (spec : Format) (s : Sign) (e : BitVec spec.exponentBits) :
    spec.Valid (packComponents spec s e 0#_) :=
  ⟨fun _ hn => False.elim (hn Float.Model.UnpackedFloat.unpackMantissa_packComponents)⟩

public theorem Float.Model.UnpackedFloat.valid_pack :
    type_of% @_root_.Float.Model.UnpackedFloat.valid_pack := by
  intro spec f
  cases f with
  | notANumber => exact ⟨fun _ _ => rfl⟩
  | infinity s => exact validZeroMantissa spec s _
  | zero s => exact validZeroMantissa spec s _
  | finite s m e hm =>
    unfold _root_.Float.Model.UnpackedFloat.pack
    dsimp only
    split
    · exact validZeroMantissa spec s _
    · rename_i limit
      split
      · apply nonExceptional
        change _ % 2 ^ spec.exponentBits < 2 ^ spec.exponentBits - 1
        have h := Nat.lt_of_not_ge limit
        rw [Nat.mod_eq_of_lt (Nat.lt_trans (Nat.lt_succ_self _) h)]
        exact Nat.lt_pred_iff.mpr h
      · apply nonExceptional
        exact Nat.sub_pos_of_lt (Nat.one_lt_two_pow (Nat.ne_zero_of_lt spec.he))

public theorem Float.Model.pack._proof_1 : type_of% @_root_.Float.Model.pack._proof_1 :=
  fun _ => Float.Model.UnpackedFloat.valid_pack

public theorem Float32.Model.pack._proof_1 : type_of% @_root_.Float32.Model.pack._proof_1 :=
  fun _ => Float.Model.UnpackedFloat.valid_pack

end OmegaChecks.InitPort.Alternatives
