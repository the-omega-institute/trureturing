module

import all Init.Data.UInt.Bitwise
public import Init.Data.UInt.Bitwise
public import Init.Data.SInt.Bitwise

namespace OmegaChecks.InitPort.Alternatives

public theorem UInt16.toUInt32_and : type_of% @_root_.UInt16.toUInt32_and := by
  intro x y
  apply UInt32.toNat.inj
  rw [UInt16.toNat_toUInt32, UInt32.toNat_and, UInt16.toNat_and, UInt16.toNat_toUInt32, UInt16.toNat_toUInt32]

public theorem UInt16.toUInt32_or : type_of% @_root_.UInt16.toUInt32_or := by
  intro x y
  apply UInt32.toNat.inj
  rw [UInt16.toNat_toUInt32, UInt32.toNat_or, UInt16.toNat_or, UInt16.toNat_toUInt32, UInt16.toNat_toUInt32]

public theorem UInt16.toUInt32_xor : type_of% @_root_.UInt16.toUInt32_xor := by
  intro x y
  apply UInt32.toNat.inj
  rw [UInt16.toNat_toUInt32, UInt32.toNat_xor, UInt16.toNat_xor, UInt16.toNat_toUInt32, UInt16.toNat_toUInt32]

public theorem UInt16.toUInt64_and : type_of% @_root_.UInt16.toUInt64_and := by
  intro x y
  apply UInt64.toNat.inj
  rw [UInt16.toNat_toUInt64, UInt64.toNat_and, UInt16.toNat_and, UInt16.toNat_toUInt64, UInt16.toNat_toUInt64]

public theorem UInt16.toUInt64_or : type_of% @_root_.UInt16.toUInt64_or := by
  intro x y
  apply UInt64.toNat.inj
  rw [UInt16.toNat_toUInt64, UInt64.toNat_or, UInt16.toNat_or, UInt16.toNat_toUInt64, UInt16.toNat_toUInt64]

public theorem UInt16.toUInt64_xor : type_of% @_root_.UInt16.toUInt64_xor := by
  intro x y
  apply UInt64.toNat.inj
  rw [UInt16.toNat_toUInt64, UInt64.toNat_xor, UInt16.toNat_xor, UInt16.toNat_toUInt64, UInt16.toNat_toUInt64]

public theorem UInt32.toUInt64_and : type_of% @_root_.UInt32.toUInt64_and := by
  intro x y
  apply UInt64.toNat.inj
  rw [UInt32.toNat_toUInt64, UInt64.toNat_and, UInt32.toNat_and, UInt32.toNat_toUInt64, UInt32.toNat_toUInt64]

public theorem UInt32.toUInt64_or : type_of% @_root_.UInt32.toUInt64_or := by
  intro x y
  apply UInt64.toNat.inj
  rw [UInt32.toNat_toUInt64, UInt64.toNat_or, UInt32.toNat_or, UInt32.toNat_toUInt64, UInt32.toNat_toUInt64]

public theorem UInt32.toUInt64_xor : type_of% @_root_.UInt32.toUInt64_xor := by
  intro x y
  apply UInt64.toNat.inj
  rw [UInt32.toNat_toUInt64, UInt64.toNat_xor, UInt32.toNat_xor, UInt32.toNat_toUInt64, UInt32.toNat_toUInt64]

public theorem UInt16.not_zero : type_of% @_root_.UInt16.not_zero := by
  apply UInt16.toBitVec_inj.mp
  rw [UInt16.toBitVec_not, UInt16.toBitVec_zero, BitVec.not_zero, UInt16.toBitVec_neg, UInt16.toBitVec_one, BitVec.neg_one_eq_allOnes]

public theorem UInt16.not_neg_one : type_of% @_root_.UInt16.not_neg_one := by
  exact (congrArg (fun x : UInt16 => ~~~x) UInt16.not_zero.symm).trans UInt16.not_not

public theorem UInt32.not_zero : type_of% @_root_.UInt32.not_zero := by
  apply UInt32.toBitVec_inj.mp
  rw [UInt32.toBitVec_not, UInt32.toBitVec_zero, BitVec.not_zero, UInt32.toBitVec_neg, UInt32.toBitVec_one, BitVec.neg_one_eq_allOnes]

public theorem UInt32.not_neg_one : type_of% @_root_.UInt32.not_neg_one := by
  exact (congrArg (fun x : UInt32 => ~~~x) UInt32.not_zero.symm).trans UInt32.not_not

public theorem UInt64.not_zero : type_of% @_root_.UInt64.not_zero := by
  apply UInt64.toBitVec_inj.mp
  rw [UInt64.toBitVec_not, UInt64.toBitVec_zero, BitVec.not_zero, UInt64.toBitVec_neg, UInt64.toBitVec_one, BitVec.neg_one_eq_allOnes]

public theorem UInt64.not_neg_one : type_of% @_root_.UInt64.not_neg_one := by
  exact (congrArg (fun x : UInt64 => ~~~x) UInt64.not_zero.symm).trans UInt64.not_not

public theorem UInt16.ofNat_shiftLeft : type_of% @_root_.UInt16.ofNat_shiftLeft := by
  intro a b small
  apply UInt16.toNat.inj
  rw [UInt16.toNat_shiftLeft, UInt16.toNat_ofNat' (n := b), Nat.mod_eq_of_lt (Nat.lt_trans small (Nat.lt_pow_self Nat.one_lt_two)),
    Nat.mod_eq_of_lt small, UInt16.toNat_ofNat', UInt16.toNat_ofNat', Nat.mod_two_pow_shiftLeft_mod_two_pow]

public theorem UInt32.ofNat_shiftLeft : type_of% @_root_.UInt32.ofNat_shiftLeft := by
  intro a b small
  apply UInt32.toNat.inj
  rw [UInt32.toNat_shiftLeft, UInt32.toNat_ofNat' (n := b), Nat.mod_eq_of_lt (Nat.lt_trans small (Nat.lt_pow_self Nat.one_lt_two)),
    Nat.mod_eq_of_lt small, UInt32.toNat_ofNat', UInt32.toNat_ofNat', Nat.mod_two_pow_shiftLeft_mod_two_pow]

public theorem UInt64.ofNat_shiftLeft : type_of% @_root_.UInt64.ofNat_shiftLeft := by
  intro a b small
  apply UInt64.toNat.inj
  rw [UInt64.toNat_shiftLeft, UInt64.toNat_ofNat' (n := b), Nat.mod_eq_of_lt (Nat.lt_trans small (Nat.lt_pow_self Nat.one_lt_two)),
    Nat.mod_eq_of_lt small, UInt64.toNat_ofNat', UInt64.toNat_ofNat', Nat.mod_two_pow_shiftLeft_mod_two_pow]

public theorem USize.ofNat_shiftLeft : type_of% @_root_.USize.ofNat_shiftLeft := by
  intro a b small
  apply USize.toNat.inj
  rw [USize.toNat_shiftLeft, USize.toNat_ofNat' (n := b), Nat.mod_eq_of_lt (Nat.lt_trans small (Nat.lt_pow_self Nat.one_lt_two)),
    Nat.mod_eq_of_lt small, USize.toNat_ofNat', USize.toNat_ofNat', Nat.mod_two_pow_shiftLeft_mod_two_pow]

public theorem Int16.not_zero : type_of% @_root_.Int16.not_zero := by
  apply Int16.toBitVec_inj.mp
  rw [Int16.toBitVec_not, Int16.toBitVec_ofNat, Int16.toBitVec_neg, Int16.toBitVec_ofNat]
  exact BitVec.not_zero.trans BitVec.neg_one_eq_allOnes.symm

public theorem Int16.not_neg_one : type_of% @_root_.Int16.not_neg_one := by
  exact (congrArg (fun x : Int16 => ~~~x) Int16.not_zero.symm).trans Int16.not_not

public theorem Int32.not_zero : type_of% @_root_.Int32.not_zero := by
  apply Int32.toBitVec_inj.mp
  rw [Int32.toBitVec_not, Int32.toBitVec_ofNat, Int32.toBitVec_neg, Int32.toBitVec_ofNat]
  exact BitVec.not_zero.trans BitVec.neg_one_eq_allOnes.symm

public theorem Int32.not_neg_one : type_of% @_root_.Int32.not_neg_one := by
  exact (congrArg (fun x : Int32 => ~~~x) Int32.not_zero.symm).trans Int32.not_not

public theorem Int64.not_zero : type_of% @_root_.Int64.not_zero := by
  apply Int64.toBitVec_inj.mp
  rw [Int64.toBitVec_not, Int64.toBitVec_ofNat, Int64.toBitVec_neg, Int64.toBitVec_ofNat]
  exact BitVec.not_zero.trans BitVec.neg_one_eq_allOnes.symm

public theorem Int64.not_neg_one : type_of% @_root_.Int64.not_neg_one := by
  exact (congrArg (fun x : Int64 => ~~~x) Int64.not_zero.symm).trans Int64.not_not

private theorem platformWidthDvd : System.Platform.numBits ∣ 2 ^ System.Platform.numBits := by
  rcases System.Platform.numBits_eq with h | h
  · rw [h]
    exact Nat.pow_dvd_pow 2 (by decide : 5 ≤ 32)
  · rw [h]
    exact Nat.pow_dvd_pow 2 (by decide : 6 ≤ 64)

public theorem USize.ofBitVec_shiftLeft_mod : type_of% @_root_.USize.ofBitVec_shiftLeft_mod := by
  intro a b
  apply USize.toBitVec_inj.mp
  simp only [USize.toBitVec_shiftLeft, BitVec.natCast_eq_ofNat, BitVec.shiftLeft_eq',
    BitVec.toNat_umod, USize.toNat_toBitVec, USize.toNat_ofNat', BitVec.toNat_ofNat,
    Nat.mod_two_pow_self, Nat.mod_mod_of_dvd _ platformWidthDvd]

public theorem USize.ofBitVec_shiftLeft : type_of% @_root_.USize.ofBitVec_shiftLeft := by
  intro a b small
  have eq := USize.ofBitVec_shiftLeft_mod a b
  rw [Nat.mod_eq_of_lt small] at eq
  exact eq

public theorem USize.ofBitVec_shiftRight_mod : type_of% @_root_.USize.ofBitVec_shiftRight_mod := by
  intro a b
  apply USize.toBitVec_inj.mp
  simp only [USize.toBitVec_shiftRight, BitVec.natCast_eq_ofNat, BitVec.ushiftRight_eq',
    BitVec.toNat_umod, USize.toNat_toBitVec, USize.toNat_ofNat', BitVec.toNat_ofNat,
    Nat.mod_two_pow_self, Nat.mod_mod_of_dvd _ platformWidthDvd]

public theorem USize.ofBitVec_shiftRight : type_of% @_root_.USize.ofBitVec_shiftRight := by
  intro a b small
  have eq := USize.ofBitVec_shiftRight_mod a b
  rw [Nat.mod_eq_of_lt small] at eq
  exact eq

private theorem add_lt_wordSize {a b w : Nat} (ha : a < w) (hb : b < w) : a+b < 2^w := by
  cases w with
  | zero => exact False.elim (Nat.not_lt_zero _ ha)
  | succ w =>
    have lt := Nat.lt_two_pow_self (n := w)
    rw [Nat.pow_succ, Nat.mul_two]
    omega

public theorem UInt16.shiftLeft_add : type_of% @_root_.UInt16.shiftLeft_add := by
  intro a b c hb hc h
  have width : (16 : UInt16).toNat = 16 :=
    (@UInt16.toNat_ofNat 16).trans (Nat.mod_eq_of_lt Nat.lt_two_pow_self)
  have smallB := UInt16.lt_iff_toNat_lt.mp hb
  have smallC := UInt16.lt_iff_toNat_lt.mp hc
  have sum := UInt16.lt_iff_toNat_lt.mp h
  rw [width] at smallB smallC sum
  rw [UInt16.toNat_add, Nat.mod_eq_of_lt (add_lt_wordSize smallB smallC)] at sum
  exact UInt16.shiftLeft_add_of_toNat_lt sum

public theorem UInt32.shiftLeft_add : type_of% @_root_.UInt32.shiftLeft_add := by
  intro a b c hb hc h
  have width : (32 : UInt32).toNat = 32 :=
    (@UInt32.toNat_ofNat 32).trans (Nat.mod_eq_of_lt Nat.lt_two_pow_self)
  have smallB := UInt32.lt_iff_toNat_lt.mp hb
  have smallC := UInt32.lt_iff_toNat_lt.mp hc
  have sum := UInt32.lt_iff_toNat_lt.mp h
  rw [width] at smallB smallC sum
  rw [UInt32.toNat_add, Nat.mod_eq_of_lt (add_lt_wordSize smallB smallC)] at sum
  exact UInt32.shiftLeft_add_of_toNat_lt sum

public theorem UInt64.shiftLeft_add : type_of% @_root_.UInt64.shiftLeft_add := by
  intro a b c hb hc h
  have width : (64 : UInt64).toNat = 64 :=
    (@UInt64.toNat_ofNat 64).trans (Nat.mod_eq_of_lt Nat.lt_two_pow_self)
  have smallB := UInt64.lt_iff_toNat_lt.mp hb
  have smallC := UInt64.lt_iff_toNat_lt.mp hc
  have sum := UInt64.lt_iff_toNat_lt.mp h
  rw [width] at smallB smallC sum
  rw [UInt64.toNat_add, Nat.mod_eq_of_lt (add_lt_wordSize smallB smallC)] at sum
  exact UInt64.shiftLeft_add_of_toNat_lt sum

public theorem USize.shiftLeft_add : type_of% @_root_.USize.shiftLeft_add := by
  intro a b c hb hc h
  have width : (USize.ofNat System.Platform.numBits).toNat = System.Platform.numBits :=
    (@USize.toNat_ofNat' System.Platform.numBits).trans (Nat.mod_eq_of_lt Nat.lt_two_pow_self)
  have smallB := USize.lt_iff_toNat_lt.mp hb
  have smallC := USize.lt_iff_toNat_lt.mp hc
  have sum := USize.lt_iff_toNat_lt.mp h
  rw [width] at smallB smallC sum
  rw [USize.toNat_add, Nat.mod_eq_of_lt (add_lt_wordSize smallB smallC)] at sum
  exact USize.shiftLeft_add_of_toNat_lt sum

public theorem UInt16.toUInt32_shiftLeft_of_lt : type_of% @_root_.UInt16.toUInt32_shiftLeft_of_lt := by
  intro x y small
  apply (UInt16.toUInt32_eq_mod_65536_iff _ _).mpr
  have lt := UInt16.lt_iff_toNat_lt.mp small
  rw [UInt16.toNat_ofNat_of_lt Nat.lt_two_pow_self] at lt
  have widened : y.toUInt32 < 16 := by
    apply UInt32.lt_iff_toNat_lt.mpr
    rw [UInt16.toNat_toUInt32, UInt32.toNat_ofNat_of_lt (Nat.lt_of_le_of_lt (by decide : 16 ≤ 32) Nat.lt_two_pow_self)]
    exact lt
  rw [UInt32.toUInt16_shiftLeft _ _ widened, UInt16.toUInt16_toUInt32, UInt16.toUInt16_toUInt32]

public theorem UInt16.toUInt64_shiftLeft_of_lt : type_of% @_root_.UInt16.toUInt64_shiftLeft_of_lt := by
  intro x y small
  apply (UInt16.toUInt64_eq_mod_65536_iff _ _).mpr
  have lt := UInt16.lt_iff_toNat_lt.mp small
  rw [UInt16.toNat_ofNat_of_lt Nat.lt_two_pow_self] at lt
  have widened : y.toUInt64 < 16 := by
    apply UInt64.lt_iff_toNat_lt.mpr
    rw [UInt16.toNat_toUInt64, UInt64.toNat_ofNat_of_lt (Nat.lt_of_le_of_lt (by decide : 16 ≤ 64) Nat.lt_two_pow_self)]
    exact lt
  rw [UInt64.toUInt16_shiftLeft _ _ widened, UInt16.toUInt16_toUInt64, UInt16.toUInt16_toUInt64]

public theorem UInt32.toUInt64_shiftLeft_of_lt : type_of% @_root_.UInt32.toUInt64_shiftLeft_of_lt := by
  intro x y small
  apply (UInt32.toUInt64_eq_mod_4294967296_iff _ _).mpr
  have lt := UInt32.lt_iff_toNat_lt.mp small
  rw [UInt32.toNat_ofNat_of_lt Nat.lt_two_pow_self] at lt
  have widened : y.toUInt64 < 32 := by
    apply UInt64.lt_iff_toNat_lt.mpr
    rw [UInt32.toNat_toUInt64, UInt64.toNat_ofNat_of_lt (Nat.lt_of_le_of_lt (by decide : 32 ≤ 64) Nat.lt_two_pow_self)]
    exact lt
  rw [UInt64.toUInt32_shiftLeft _ _ widened, UInt32.toUInt32_toUInt64, UInt32.toUInt32_toUInt64]

public theorem USize.toUInt8_shiftLeft_mod : type_of% @_root_.USize.toUInt8_shiftLeft_mod := by
  intro a b
  have bound : 8 < 2 ^ System.Platform.numBits :=
    Nat.lt_of_le_of_lt (Nat.le_trans (by decide : 8 ≤ 32) System.Platform.le_numBits) Nat.lt_two_pow_self
  have width : (8 : USize).toNat = 8 := USize.toNat_ofNat_of_lt bound
  have rem : b % 8 < 8 := by
    apply USize.lt_iff_toNat_lt.mpr
    rw [USize.toNat_mod, width]
    exact Nat.mod_lt _ (by decide)
  have divides : (8 : USize).toNat ∣ 256 := by
    rw [width]
    exact Nat.pow_dvd_pow 2 (by decide : 3 ≤ 8)
  have cast : (8 : USize).toUInt8 = 8 := by
    apply UInt8.toNat.inj
    rw [USize.toNat_toUInt8, width, UInt8.toNat_ofNat_of_lt Nat.lt_two_pow_self]
  rw [USize.toUInt8_shiftLeft _ _ rem, USize.toUInt8_mod_of_dvd _ _ divides, cast]
  exact (UInt8.shiftLeft_eq_shiftLeft_mod ..).symm

public theorem USize.toUInt16_shiftLeft_mod : type_of% @_root_.USize.toUInt16_shiftLeft_mod := by
  intro a b
  have bound : 16 < 2 ^ System.Platform.numBits :=
    Nat.lt_of_le_of_lt (Nat.le_trans (by decide : 16 ≤ 32) System.Platform.le_numBits) Nat.lt_two_pow_self
  have width : (16 : USize).toNat = 16 := USize.toNat_ofNat_of_lt bound
  have rem : b % 16 < 16 := by
    apply USize.lt_iff_toNat_lt.mpr
    rw [USize.toNat_mod, width]
    exact Nat.mod_lt _ (by decide)
  have divides : (16 : USize).toNat ∣ 65536 := by
    rw [width]
    exact Nat.pow_dvd_pow 2 (by decide : 4 ≤ 16)
  have cast : (16 : USize).toUInt16 = 16 := by
    apply UInt16.toNat.inj
    rw [USize.toNat_toUInt16, width, UInt16.toNat_ofNat_of_lt Nat.lt_two_pow_self]
  rw [USize.toUInt16_shiftLeft _ _ rem, USize.toUInt16_mod_of_dvd _ _ divides, cast]
  exact (UInt16.shiftLeft_eq_shiftLeft_mod ..).symm

public theorem USize.toUInt32_shiftLeft_mod : type_of% @_root_.USize.toUInt32_shiftLeft_mod := by
  intro a b
  have bound : 32 < 2 ^ System.Platform.numBits :=
    Nat.lt_of_le_of_lt (Nat.le_trans (by decide : 32 ≤ 32) System.Platform.le_numBits) Nat.lt_two_pow_self
  have width : (32 : USize).toNat = 32 := USize.toNat_ofNat_of_lt bound
  have rem : b % 32 < 32 := by
    apply USize.lt_iff_toNat_lt.mpr
    rw [USize.toNat_mod, width]
    exact Nat.mod_lt _ (by decide)
  have divides : (32 : USize).toNat ∣ 4294967296 := by
    rw [width]
    exact Nat.pow_dvd_pow 2 (by decide : 5 ≤ 32)
  have cast : (32 : USize).toUInt32 = 32 := by
    apply UInt32.toNat.inj
    rw [USize.toNat_toUInt32, width, UInt32.toNat_ofNat_of_lt Nat.lt_two_pow_self]
  rw [USize.toUInt32_shiftLeft _ _ rem, USize.toUInt32_mod_of_dvd _ _ divides, cast]
  exact (UInt32.shiftLeft_eq_shiftLeft_mod ..).symm

public theorem UInt64.toUSize_shiftLeft_mod : type_of% @_root_.UInt64.toUSize_shiftLeft_mod := by
  intro a b
  have width : (UInt64.ofNat System.Platform.numBits).toNat = System.Platform.numBits :=
    UInt64.toNat_ofNat'.trans (Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt System.Platform.numBits_le Nat.lt_two_pow_self))
  have bound : (b % UInt64.ofNat System.Platform.numBits).toNat < System.Platform.numBits := by
    rw [UInt64.toNat_mod, width]
    exact Nat.mod_lt _ (Nat.lt_of_lt_of_le (by decide : 0 < 32) System.Platform.le_numBits)
  have divides : (UInt64.ofNat System.Platform.numBits).toNat ∣ USize.size := by
    rw [width]
    exact platformWidthDvd
  rw [UInt64.toUSize_shiftLeft _ _ bound, UInt64.toUSize_mod_of_dvd_usizeSize _ _ divides]
  have eq : (UInt64.ofNat System.Platform.numBits).toUSize = USize.ofNat System.Platform.numBits := by
    apply USize.toNat.inj
    rw [UInt64.toNat_toUSize, width, USize.toNat_ofNat']
  rw [eq]
  exact (USize.shiftLeft_eq_shiftLeft_mod ..).symm

public theorem UInt16.shiftLeft_add._proof_1_2 :
    type_of% (private_decl% @_root_.UInt16.shiftLeft_add._proof_1_2) :=
  fun hb hc impossible => impossible (Nat.lt_trans (Nat.add_lt_add hb hc)
    (by decide : 32 < 65536))

public theorem UInt32.shiftLeft_add._proof_1_2 :
    type_of% (private_decl% @_root_.UInt32.shiftLeft_add._proof_1_2) :=
  fun hb hc impossible => impossible (Nat.lt_trans (Nat.add_lt_add hb hc)
    (by decide : 64 < 4294967296))

public theorem UInt64.shiftLeft_add._proof_1_2 :
    type_of% (private_decl% @_root_.UInt64.shiftLeft_add._proof_1_2) :=
  fun hb hc impossible => impossible (Nat.lt_trans (Nat.add_lt_add hb hc)
    (by decide : 128 < 18446744073709551616))

public theorem USize.shiftLeft_add._proof_1_2 :
    type_of% (private_decl% @_root_.USize.shiftLeft_add._proof_1_2) :=
  fun hb hc impossible => impossible (Nat.lt_trans (Nat.add_lt_add hb hc)
    (by decide : 64 < 4294967296))

public theorem USize.shiftLeft_add._proof_1_3 :
    type_of% (private_decl% @_root_.USize.shiftLeft_add._proof_1_3) :=
  fun hb hc impossible => impossible (Nat.lt_trans (Nat.add_lt_add hb hc)
    (by decide : 128 < 18446744073709551616))

end OmegaChecks.InitPort.Alternatives
